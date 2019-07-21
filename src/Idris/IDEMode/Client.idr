module Idris.IDEMode.Client

import Data.Primitives.Views
import System
import Idris.IDEMode.Commands
import Idris.Socket
import Idris.Socket.Data
import Idris.IDEMode.REPL

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

client : String -> Int -> IDECommand -> IO ()
client host port command = do
  cnx<- connectTo host port
  case cnx of
    Left fail => do
      putStrLn fail
    Right sock => do
      let cmdString = serialize command
      case cmdString of
        Just cmd => do
          res <- send sock cmd
          case res of
            Left err =>
              putStrLn ("Failed to connect to :" ++ host ++ ":" ++ show port ++", " ++ show err)
            Right sent =>
              putStrLn ("Sent " ++ show sent ++ " bytes")
        Nothing => putStrLn "Command is too long"
