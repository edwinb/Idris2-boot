module Main

import System

%default covering

------------------------------------------------------------------------
-- Test cases

ttimpTests : List String
ttimpTests
    = ["basic001", "basic002", "basic003", "basic004", "basic005",
       "basic006",
       "coverage001", "coverage002",
       "dot001",
       "eta001", "eta002",
       "lazy001",
       "nest001", "nest002",
       "perf001", "perf002", "perf003",
       "record001", "record002", "record003",
       "rewrite001",
       "qtt001", "qtt002", "qtt003",
       "search001", "search002", "search003", "search004", "search005",
       "total001", "total002", "total003",
       "with001"]

idrisTests : List String
idrisTests
    = -- Fundamental language feturea
      ["basic001", "basic002", "basic003", "basic004", "basic005",
       "basic006", "basic007", "basic008", "basic009", "basic010",
       "basic011", "basic012", "basic013", "basic014", "basic015",
       "basic016", "basic017", "basic018", "basic019", "basic020",
       "basic021", "basic022", "basic023", "basic024", "basic025",
       "basic026", "basic027", "basic028", "basic029", "basic030",
       "basic031", "basic032", "basic033", "basic034", "basic035",
       "basic036", "basic037", "basic038",
       -- Coverage checking
       "coverage001", "coverage002", "coverage003", "coverage004",
       "coverage005", "coverage006",
       -- Error messages
       "error001", "error002", "error003", "error004", "error005",
       "error006", "error007", "error008", "error009", "error010",
       -- Modules and imports
       "import001", "import002", "import003", "import004",
       -- Interactive editing support
       "interactive001", "interactive002", "interactive003", "interactive004",
       "interactive005", "interactive006", "interactive007", "interactive008",
       "interactive009", "interactive010", "interactive011", "interactive012",
       -- Literate
       "literate001", "literate002", "literate003", "literate004",
       "literate005", "literate006", "literate007", "literate008",
       "literate009", "literate010", "literate011", "literate012",
       -- Interfaces
       "interface001", "interface002", "interface003", "interface004",
       "interface005", "interface006", "interface007", "interface008",
       "interface009", "interface010", "interface011", "interface012",
       "interface013", "interface014", "interface015",
       -- Miscellaneous REPL
       "interpreter001",
       -- Implicit laziness, lazy evaluation
       "lazy001",
       -- QTT and linearity related
       "linear001", "linear002", "linear003", "linear004", "linear005",
       "linear006", "linear007", "linear008",
       -- Parameters blocks
       "params001",
       -- Performance: things which have been slow in the past, or which
       -- pose interesting challenges for the elaborator
       "perf001", "perf002", "perf003", "perf004",
       -- Parse errors
       "perror001", "perror002", "perror003", "perror004", "perror005",
       "perror006",
       -- Packages and ipkg files
       "pkg001", "pkg002",
       -- Larger programs arising from real usage. Typically things with
       -- interesting interactions between features
       "real001", "real002",
       -- Records, access and dependent update
       "record001", "record002", "record003", "record004",
       -- Miscellaneous regressions
       "reg001", "reg002", "reg003", "reg004", "reg005", "reg006", "reg007",
       "reg008", "reg009", "reg010", "reg011", "reg012", "reg013", "reg014",
       "reg015", "reg016", "reg017", "reg018",
       -- Totality checking
       "total001", "total002", "total003", "total004", "total005",
       "total006",
       -- The 'with' rule
       "with001", "with002",
       -- 'with' expressions
       "with003"]

typeddTests : List String
typeddTests
   = ["chapter01", "chapter02", "chapter03", "chapter04", "chapter05",
      "chapter06", "chapter07", "chapter08", "chapter09", "chapter10",
      "chapter11", "chapter12", "chapter13", "chapter14"]

chezTests : List String
chezTests
   = ["chez001", "chez002", "chez003", "chez004", "chez005", "chez006",
      "chez007", "chez008", "chez009", "chez010", "chez011", "chez012",
      "chez013", "chez014", "chez015", "chez016",
      "reg001"]

ideModeTests : List String
ideModeTests
  =  [ "ideMode001", "ideMode002", "ideMode003" ]

------------------------------------------------------------------------
-- Options

||| Options for the test driver.
record Options where
  constructor MkOptions
  ||| Name of the idris2 executable
  idris2      : String
  ||| Should we only run some specific cases?
  onlyNames   : List String
  ||| Should we run the test suite interactively?
  interactive : Bool

usage : String
usage = "Usage: runtests <idris2 path> [--interactive] [--only [NAMES]]"

options : List String -> Maybe Options
options args = case args of
    (_ :: idris2 :: rest) => go rest (MkOptions idris2 [] False)
    _ => Nothing

  where

    go : List String -> Options -> Maybe Options
    go rest opts = case rest of
      []                      => pure opts
      ("--interactive" :: xs) => go xs (record { interactive = True } opts)
      ("--only" :: xs)        => pure $ record { onlyNames = xs } opts
      _ => Nothing

------------------------------------------------------------------------
-- Actual test runner

chdir : String -> IO Bool
chdir dir
    = do ok <- foreign FFI_C "chdir" (String -> IO Int) dir
         pure (ok == 0)

fail : String -> IO ()
fail err
    = do putStrLn err
         exitWith (ExitFailure 1)

runTest : Options -> String -> IO Bool
runTest opts testPath
    = do chdir testPath
         isSuccess <- runTest'
         chdir "../.."
         pure isSuccess
    where
        getAnswer : IO Bool
        getAnswer = do
          str <- getLine
          case str of
            "y" => pure True
            "n" => pure False
            _   => do putStrLn "Invalid Answer."
                      getAnswer

        printExpectedVsOutput : String -> String -> IO ()
        printExpectedVsOutput exp out = do
          putStrLn "Expected:"
          printLn exp
          putStrLn "Given:"
          printLn out

        mayOverwrite : Maybe String -> String -> IO ()
        mayOverwrite mexp out = do
          case mexp of
            Nothing => putStr $ unlines
              [ "Golden value missing. I computed the following result:"
              , out
              , "Accept new golden value? [yn]"
              ]
            Just exp => do
              putStrLn "Golden value differs from actual value."
              code <- system "git diff expected output"
              when (code /= 0) $ printExpectedVsOutput exp out
              putStrLn "Accept actual value as new golden value? [yn]"
          b <- getAnswer
          when b $ do Right _ <- writeFile "expected" out
                          | Left err => print err
                      pure ()

        runTest' : IO Bool
        runTest'
            = do putStr $ testPath ++ ": "
                 system $ "sh ./run " ++ idris2 opts ++ " | tr -d '\\r' > output"
                 Right out <- readFile "output"
                     | Left err => do print err
                                      pure False
                 Right exp <- readFile "expected"
                     | Left FileNotFound => do
                         if interactive opts
                           then mayOverwrite Nothing out
                           else print FileNotFound
                         pure False
                     | Left err => do print err
                                      pure False

                 if (out == exp)
                    then putStrLn "success"
                    else do
                      putStrLn "FAILURE"
                      if interactive opts then mayOverwrite (Just exp) out
                      else printExpectedVsOutput exp out

                 pure (out == exp)

exists : String -> IO Bool
exists f
    = do Right ok <- openFile f Read
             | Left err => pure False
         closeFile ok
         pure True

firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

pathLookup : IO (Maybe String)
pathLookup = do
  path <- getEnv "PATH"
  let pathList = split (== ':') $ fromMaybe "/usr/bin:/usr/local/bin" path
  let candidates = [p ++ "/" ++ x | p <- pathList,
                                    x <- ["chez", "chezscheme9.5", "scheme"]]
  firstExists candidates

findChez : IO (Maybe String)
findChez
    = do Just chez <- getEnv "CHEZ" | Nothing => pathLookup
         pure $ Just chez

runChezTests : Options -> List String -> IO (List Bool)
runChezTests opts tests
    = do chexec <- findChez
         maybe (do putStrLn "Chez Scheme not found"
                   pure [])
               (\c => do putStrLn $ "Found Chez Scheme at " ++ c
                         traverse (runTest opts) tests)
               chexec

filterTests : Options -> List String -> List String
filterTests opts = case onlyNames opts of
  [] => id
  xs => filter (\ name => any (`isInfixOf` name) xs)

main : IO ()
main
    = do args <- getArgs
         let (Just opts) = options args
              | _ => do print args
                        putStrLn usage
         let filteredNonCGTests =
              filterTests opts $ concat
                 [ testPaths "ttimp" ttimpTests
                 , testPaths "idris2" idrisTests
                 , testPaths "typedd-book" typeddTests
                 , testPaths "ideMode" ideModeTests
                 ]
         let filteredChezTests = filterTests opts (testPaths "chez" chezTests)
         nonCGTestRes <- traverse (runTest opts) filteredNonCGTests
         chezTestRes <- if length filteredChezTests > 0
              then runChezTests opts filteredChezTests
              else pure []
         let res = nonCGTestRes ++ chezTestRes
         putStrLn (show (length (filter id res)) ++ "/" ++ show (length res)
                       ++ " tests successful")
         if (any not res)
            then exitWith (ExitFailure 1)
            else exitWith ExitSuccess
    where
         testPaths : String -> List String -> List String
         testPaths dir tests = map (\test => dir ++ "/" ++ test) tests
