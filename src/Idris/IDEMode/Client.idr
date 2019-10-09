module Idris.IDEMode.Client

import System
import Idris.IDEMode.Commands
import Idris.IDEMode.Parser
import Idris.Socket
import Idris.Syntax
import Idris.REPL
import Idris.Socket.Data
import Idris.IDEMode.REPL
import Parser.Support
import Utils.Hex

connectTo : String -> Int -> IO (Either String Socket)
connectTo host port = do
  osock <- socket AF_INET Stream 0
  case osock of
    Left fail => do
      pure $ Left ("Failed to open client socket " ++ show fail)
    Right sock => do
      res <- connect sock (Hostname host) port
      if res /= 0
      then pure $ Left ("Failed to connect to :" ++ host ++ ":" ++ show port ++", " ++ show res)
      else pure (Right sock)

||| Runs an ide-mode client to execute one command against a given server
serialize : IDECommand -> Maybe String
serialize cmd =
  let scmd = show $ SExpList [ toSExp cmd, toSExp 1 ]
      hexLen = asHex $ cast $ Strings.length scmd
      len = case isLTE (length hexLen) 6 of
                 (Yes _) => Just $ cast (replicate (6 - length hexLen) '0') ++  hexLen
                 (No  _) => Nothing
  in (++) <$> len <*> Just scmd


readOutput : Socket -> IO (Either String  SExp)
readOutput sock = do
  Right (len, _) <- recv sock 6 | Left err => pure (Left $ "failed to read from socket, error: " ++ show err)
  case toHex 1 (reverse $ cast len) of
    Nothing => pure $ Left ("expected a length in six-digits hexadecimal, got " ++ len)
    Just num => do
      Right (msg, _) <- recv sock num | Left err => pure (Left $ "failed to read from socket, error: " ++ show err)
      pure $ either (Left . show) Right $ parseSExp msg

data IDEResult : Type where
  IDEReturn : SExp -> IDEResult
  NetworkError : String -> IDEResult
  InputError : String -> IDEResult
  OutputError : String -> IDEResult

implementation Show IDEResult where
  show (IDEReturn exprs) = show exprs
  show (NetworkError reason) = reason
  show (InputError reason) = reason
  show (OutputError reason) = reason


readResult: Socket -> (SExp -> IO Bool) -> IO IDEResult
readResult sock cont = do
  Right output <- readOutput sock | Left err => pure (OutputError err)
  case output of
    (SExpList (SymbolAtom "return" ::  result :: _)) => pure (IDEReturn result)
    other => do continue <- cont other
                if continue
                then readResult sock cont
                else pure (IDEReturn other)

printExp : SExp -> IO Bool
printExp exp = do putStrLn (show exp)
                  pure True

execute : Socket -> IDECommand -> IO IDEResult
execute cnx command = do
      let cmdString = serialize command
      case cmdString of
        Just cmd => do
          Right sent <- send cnx cmd
            | Left err => pure (NetworkError ("Failed to send command, error: " ++ show err))
          readResult cnx printExp
        Nothing => pure $ InputError "Command is too long"

connect : String -> Int -> IO Socket
connect host port = do
  Right sock <- connectTo host port
    | Left fail => do
      putStrLn $ "fail to connect to " ++ host ++ ":" ++ show port ++", error: " ++ fail
      exit 1
  pure sock

covering
makeIDECommand : REPLCmd -> Either String IDECommand
makeIDECommand (Eval term)            = Right $ Interpret (show term)
makeIDECommand (Check term)           = Right $ TypeOf (show term) Nothing
makeIDECommand (Load file)            = Right $ LoadFile file Nothing
makeIDECommand (Editing (TypeAt line col name)) = Right $ TypeOf (show name) (Just (cast line, cast col))
makeIDECommand (CD x) = Right $ Interpret (":cd " ++ x)
makeIDECommand ShowVersion = Right Version
makeIDECommand _ = Left $ "Don't know how to interpret command"
-- makeIDECommand (Editing (CaseSplit x y z)) = ?makeIDECommand_rhs_1
-- makeIDECommand (Editing (AddClause x y)) = ?makeIDECommand_rhs_2
-- makeIDECommand (Editing (ExprSearch x y xs z)) = ?makeIDECommand_rhs_3
-- makeIDECommand (Editing (GenerateDef x y)) = ?makeIDECommand_rhs_4
-- makeIDECommand (Editing (MakeLemma x y)) = ?makeIDECommand_rhs_5
-- makeIDECommand (Editing (MakeCase x y)) = ?makeIDECommand_rhs_6
-- makeIDECommand (Editing (MakeWith x y)) = ?makeIDECommand_rhs_7
-- makeIDECommand (PrintDef x) = ?makeIDECommand_rhs_8
-- makeIDECommand Reload = ?makeIDECommand_rhs_9
-- makeIDECommand Edit = ?makeIDECommand_rhs_10
-- makeIDECommand (Compile x y) = ?makeIDECommand_rhs_11
-- makeIDECommand (Exec x) = ?makeIDECommand_rhs_12
-- makeIDECommand (ProofSearch x) = ?makeIDECommand_rhs_13
-- makeIDECommand (DebugInfo x) = ?makeIDECommand_rhs_14
-- makeIDECommand (SetOpt x) = ?makeIDECommand_rhs_15
-- makeIDECommand (Missing x) = ?makeIDECommand_rhs_17
-- makeIDECommand (Total x) = ?makeIDECommand_rhs_18
-- makeIDECommand (SetLog k) = ?makeIDECommand_rhs_19
-- makeIDECommand Metavars = ?makeIDECommand_rhs_20
-- makeIDECommand Quit = ?makeIDECommand_rhs_22
-- makeIDECommand NOP = ?makeIDECommand_rhs_23


parseCommand : String -> Either String IDECommand
parseCommand = either (Left . show) makeIDECommand . parseRepl

repl : Socket -> IO ()
repl cnx
    = do putStr prompt
         Right input <- map parseCommand getLine
           | Left err => do
                  putStrLn err
                  repl cnx
         end <- fEOF stdin
         if end
            then putStrLn "Bye!"
            else do
              result <- execute cnx input
              putStrLn $ show result
              repl cnx

  where
    prompt : String
    prompt = "λ> "

readProtocol : Socket -> IO ()
readProtocol sock = do
  res <- readResult sock (const $ pure False)
  case res of
    (IDEReturn (SExpList [ SymbolAtom "protocol-version" , IntegerAtom 2, IntegerAtom 0])) => pure ()
    _ => do { putStrLn ("Expected protocol version 2.0, got " ++ show res) ; exit 1 }

export
client : String -> Int -> IO ()
client host port = do
  sock <- connect host port
  readProtocol sock
  repl sock
