module Idris.IDEMode.Client

import Data.Primitives.Views
import System
import Idris.IDEMode.Commands
import Idris.IDEMode.Parser
import Idris.Socket
import Idris.Syntax
import Idris.REPL
import Idris.Socket.Data
import Idris.IDEMode.REPL
import Parser.Support

hexDigit : Int -> Char
hexDigit 0 = '0'
hexDigit 1 = '1'
hexDigit 2 = '2'
hexDigit 3 = '3'
hexDigit 4 = '4'
hexDigit 5 = '5'
hexDigit 6 = '6'
hexDigit 7 = '7'
hexDigit 8 = '8'
hexDigit 9 = '9'
hexDigit 10 = 'a'
hexDigit 11 = 'b'
hexDigit 12 = 'c'
hexDigit 13 = 'd'
hexDigit 14 = 'e'
hexDigit 15 = 'f'

||| Convert a positive integer into a list of (lower case) hexadecimal characters
asHex : Int -> String
asHex n = pack $ asHex' n []
  where
    asHex' : Int -> List Char -> List Char
    asHex' 0 hex = hex
    asHex' n hex with (n `divides` 16)
      asHex' (16 * div + rem) hex | DivBy {div} {rem} _ = asHex' div (hexDigit rem :: hex)

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
  IDEReturn : List SExp -> IDEResult
  NetworkError : String -> IDEResult
  InputError : String -> IDEResult
  OutputError : String -> IDEResult

implementation Show IDEResult where
  show (IDEReturn exprs) = unlines $ map show exprs
  show (NetworkError reason) = reason
  show (InputError reason) = reason
  show (OutputError reason) = reason


readResult: Socket -> List SExp -> IO IDEResult
readResult sock outputs = do
  Right output <- readOutput sock | Left err => pure (OutputError err)
  case output of
    SExpList (SymbolAtom "return" :: rest) => pure (IDEReturn (SExpList rest :: outputs))
    res => do
      readResult sock (res :: outputs)

execute : Socket -> IDECommand -> IO IDEResult
execute cnx command = do
      let cmdString = serialize command
      case cmdString of
        Just cmd => do
          Right sent <- send cnx cmd
            | Left err => pure (NetworkError ("Failed to send command, error: " ++ show err))
          readResult cnx []
        Nothing => pure $ InputError "Command is too long"

connect : String -> Int -> IO Socket
connect host port = do
  Right sock <- connectTo host port
    | Left fail => do
      putStrLn $ "fail to connect to " ++ host ++ ":" ++ show port ++", error: " ++ fail
      exit 1
  pure sock

makeIDECommand : REPLCmd -> Either String IDECommand
makeIDECommand (Eval term)            = Right $ Interpret (show term)
makeIDECommand (Check term)           = Right $ TypeOf (show term) Nothing
makeIDECommand (Load file)            = Right $ LoadFile file Nothing
makeIDECommand (Editing (TypeAt line col name)) = Right $ TypeOf (show name) (Just (cast line, cast col))
makeIDECommand other                  = Left "Don't know how to interpret command"

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

export
client : String -> Int -> IO ()
client host port = connect host port  >>= repl
