module Idris.CommandLine

import Data.String

%default total

public export
data PkgCommand
      = Build
      | Install
      | Clean
      | REPL


export
Show PkgCommand where
  show Build = "--build"
  show Install = "--install"
  show Clean = "--clean"
  show REPL = "--repl"

||| CLOpt - possible command line options
public export
data CLOpt
  =
   ||| Only typecheck the given file
  CheckOnly |
   ||| The output file from the code generator
  OutputFile String |
   ||| Execute a given function after checking the source file
  ExecFn String |
   ||| Use a specific code generator (default chez)
  SetCG String |
   ||| Don't implicitly import Prelude
  NoPrelude |
   ||| Show the installation prefix
  ShowPrefix |
   ||| Display Idris version
  Version |
   ||| Display help text
  Help |
   ||| Run Idris 2 in quiet mode
  Quiet |
   ||| Add a package as a dependency
  PkgPath String |
   ||| Build or install a given package, depending on PkgCommand
  Package PkgCommand String |
   ||| The input Idris file
  InputFile String |
   ||| Whether or not to run in IdeMode (easily parsable for other tools)
  IdeMode |
   ||| Whether or not to run IdeMode (using a socket instead of stdin/stdout)
  IdeModeSocket String |
   ||| Run as a checker for the core language TTImp
  Yaffle String |
  Timing |
  BlodwenPaths


ActType : List String -> Type
ActType [] = List CLOpt
ActType (a :: as) = String -> ActType as

record OptDesc where
  constructor MkOpt
  flags : List String
  argdescs : List String
  action : ActType argdescs
  help : Maybe String

options : List OptDesc
options = [MkOpt ["--check", "-c"] [] [CheckOnly]
              (Just "Exit after checking source file"),
           MkOpt ["--output", "-o"] ["file"] (\f => [OutputFile f, Quiet])
              (Just "Specify output file"),
           MkOpt ["--exec", "-x"] ["name"] (\f => [ExecFn f, Quiet])
              (Just "Execute function after checking source file"),
           MkOpt ["--no-prelude"] [] [NoPrelude]
              (Just "Don't implicitly import Prelude"),
           MkOpt ["--codegen", "--cg"] ["backend"] (\f => [SetCG f])
              (Just "Set code generator (default chez)"),
           MkOpt ["--package", "-p"] ["package"] (\f => [PkgPath f])
              (Just "Add a package as a dependency"),

           MkOpt ["--ide-mode"] [] [IdeMode]
              (Just "Run the REPL with machine-readable syntax"),

           MkOpt ["--ide-mode-socket"] [] [IdeModeSocket "localhost:38398"]
              (Just "Run the ide socket mode on default host and port (localhost:38398"),

           MkOpt ["--ide-mode-socket-with"] ["host:port"] (\hp => [IdeModeSocket hp])
              (Just "Run the ide socket mode on given host and port"),

           MkOpt ["--prefix"] [] [ShowPrefix]
              (Just "Show installation prefix"),
           MkOpt ["--paths"] [] [BlodwenPaths]
              (Just "Show paths"),
           MkOpt ["--build"] ["package file"] (\f => [Package Build f])
              (Just "Build modules/executable for the given package"),
           MkOpt ["--install"] ["package file"] (\f => [Package Install f])
              (Just "Install the given package"),
           MkOpt ["--clean"] ["package file"] (\f => [Package Clean f])
              (Just "Clean intermediate files/executables for the given package"),

           MkOpt ["--quiet", "-q"] [] [Quiet]
              (Just "Quiet mode; display fewer messages"),
           MkOpt ["--version", "-v"] [] [Version]
              (Just "Display version string"),
           MkOpt ["--help", "-h", "-?"] [] [Help]
              (Just "Display help text"),
           MkOpt ["--yaffle", "--ttimp"] ["ttimp file"] (\f => [Yaffle f])
              Nothing,
           MkOpt ["--timing"] [] [Timing]
              (Just "Display timing logs")
           ]

optUsage : OptDesc -> String
optUsage d
    = maybe "" -- Don't show anything if there's no help string (that means
               -- it's an internal option)
        (\h =>
            let optshow = showSep "," (flags d) ++ " " ++
                    showSep " " (map (\x => "<" ++ x ++ ">") (argdescs d)) in
                optshow ++ pack (List.replicate (minus 26 (length optshow)) ' ')
                ++ h ++ "\n") (help d)
  where
    showSep : String -> List String -> String
    showSep sep [] = ""
    showSep sep [x] = x
    showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export
version : String
version = "0.0"

export
versionMsg : String
versionMsg = "Idris 2, version " ++ version

export
usage : String
usage = versionMsg ++ "\n" ++
        "Usage: idris2 [options] [input file]\n\n" ++
        "Available options:\n" ++
        concatMap (\u => "  " ++ optUsage u) options

processArgs : String -> (args : List String) -> List String -> ActType args ->
              Either String (List CLOpt, List String)
processArgs flag [] xs f = Right (f, xs)
processArgs flag (a :: as) [] f
    = Left $ "Missing argument <" ++ a ++ "> for flag " ++ flag
processArgs flag (a :: as) (x :: xs) f
    = processArgs flag as xs (f x)

matchFlag : (d : OptDesc) -> List String ->
            Either String (Maybe (List CLOpt, List String))
matchFlag d [] = Right Nothing -- Nothing left to match
matchFlag d (x :: xs)
    = if x `elem` flags d
         then do args <- processArgs x (argdescs d) xs (action d)
                 Right (Just args)
         else Right Nothing

findMatch : List OptDesc -> List String ->
            Either String (List CLOpt, List String)
findMatch [] [] = Right ([], [])
findMatch [] (f :: args) = Right ([InputFile f], args)
findMatch (d :: ds) args
    = case !(matchFlag d args) of
           Nothing => findMatch ds args
           Just res => Right res

parseOpts : List OptDesc -> List String -> Either String (List CLOpt)
parseOpts opts [] = Right []
parseOpts opts args
   = do (cl, rest) <- findMatch opts args
        cls <- assert_total (parseOpts opts rest) -- 'rest' smaller than 'args'
        pure (cl ++ cls)

export
getOpts : List String -> Either String (List CLOpt)
getOpts opts = parseOpts options opts


export covering
getCmdOpts : IO (Either String (List CLOpt))
getCmdOpts = do (_ :: opts) <- getArgs
                    | pure (Left "Invalid command line")
                pure $ getOpts opts

portPart : String -> Maybe String
portPart p with (not $ p == "") proof prf
  portPart p | False  = Nothing
  portPart p | True = Just $ strTail' p (sym prf)

||| Extract the host and port to bind the IDE socket to
public export
ideSocketModeHostPort : List CLOpt -> (String, Int)
ideSocketModeHostPort []  = ("localhost", 38398)
ideSocketModeHostPort (IdeModeSocket hp :: _) =
  let (h, p) = Strings.break (== ':') hp
      port = fromMaybe 38398 (portPart p >>= parsePositive)
      host = if h == "" then "localhost" else h
  in (host, port)
ideSocketModeHostPort (_ :: rest) = ideSocketModeHostPort rest
