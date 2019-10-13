module Idris.IDEMode.REPL

import Compiler.Scheme.Chez
import Compiler.Scheme.Chicken
import Compiler.Scheme.Racket
import Compiler.Common

import Core.AutoSearch
import Core.CompileExpr
import Core.Context
import Core.InitPrimitives
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.TT
import Core.Unify

import Idris.Desugar
import Idris.Error
import Idris.ModTree
import Idris.Parser
import Idris.Resugar
import Idris.REPL
import Idris.Syntax

import Idris.IDEMode.Parser
import Idris.IDEMode.Commands

import TTImp.Interactive.CaseSplit
import TTImp.Elab
import TTImp.TTImp
import TTImp.ProcessDecls

import Control.Catchable
import System
import Idris.Socket
import Idris.Socket.Data

export
socketToFile : Socket -> IO (Either String File)
socketToFile (MkSocket f _ _ _) = do
  file <- map FHandle $ foreign FFI_C "fdopen" (Int -> String -> IO Ptr) f "r+"
  if !(ferror file) then do
    pure (Left "Failed to fdopen socket file descriptor")
  else pure (Right file)

export
initIDESocketFile : String -> Int -> IO (Either String File)
initIDESocketFile h p = do
  osock <- socket AF_INET Stream 0
  case osock of
    Left fail => do
      putStrLn (show fail)
      putStrLn "Failed to open socket"
      exit 1
    Right sock => do
      res <- bind sock (Just (Hostname h)) p
      if res /= 0
      then
        pure (Left ("Failed to bind socket with error: " ++ show res))
      else do
        res <- listen sock
        if res /= 0
        then
          pure (Left ("Failed to listen on socket with error: " ++ show res))
        else do
          putStrLn (show p)
          res <- accept sock
          case res of
            Left err =>
               pure (Left ("Failed to accept on socket with error: " ++ show err))
            Right (s, _) =>
               socketToFile s

getChar : File -> IO Char
getChar (FHandle h) = do
  if !(fEOF (FHandle h)) then do
    putStrLn "Alas the file is done, aborting"
    exit 1
  else do
    chr <- map cast $ foreign FFI_C "fgetc" (Ptr -> IO Int) h
    if !(ferror (FHandle h)) then do
      putStrLn "Failed to read a character"
      exit 1
    else pure chr

getFLine : File -> IO String
getFLine (FHandle h) = do
  str <- prim_fread h
  if !(ferror (FHandle h)) then do
    putStrLn "Failed to read a line"
    exit 1
  else pure str

getNChars : File -> Nat -> IO (List Char)
getNChars i Z = pure []
getNChars i (S k)
    = do x <- getChar i
         xs <- getNChars i k
         pure (x :: xs)

hex : Char -> Maybe Int
hex '0' = Just 0
hex '1' = Just 1
hex '2' = Just 2
hex '3' = Just 3
hex '4' = Just 4
hex '5' = Just 5
hex '6' = Just 6
hex '7' = Just 7
hex '8' = Just 8
hex '9' = Just 9
hex 'a' = Just 10
hex 'b' = Just 11
hex 'c' = Just 12
hex 'd' = Just 13
hex 'e' = Just 14
hex 'f' = Just 15
hex _ = Nothing

export
toHex : Int -> List Char -> Maybe Int
toHex _ [] = Just 0
toHex m (d :: ds)
    = pure $ !(hex (toLower d)) * m + !(toHex (m*16) ds)


-- Read 6 characters. If they're a hex number, read that many characters.
-- Otherwise, just read to newline
getInput : File -> IO String
getInput f
    = do x <- getNChars f 6
         case toHex 1 (reverse x) of
              Nothing =>
                do rest <- getFLine f
                   pure (pack x ++ rest)
              Just num =>
                do inp <- getNChars f (cast num)
                   pure (pack inp)

process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref MD Metadata} ->
          {auto o : Ref ROpts REPLOpts} ->
          IDECommand -> Core ()
process (Interpret cmd)
    = do interpret cmd ; pure ()
process (LoadFile fname toline)
    = do opts <- get ROpts
         put ROpts (record { mainfile = Just fname } opts)
         resetContext
         errs <- buildDeps fname
         updateErrorLine errs
         Right res <- coreLift (readFile fname)
            | Left err => setSource ""
         setSource res
         case errs of
              [] => printResult $ "Loaded " ++ fname
              _ => printError $ "Failed to load " ++ fname
process (TypeOf n Nothing)
    = do Idris.REPL.process (Check (PRef replFC (UN n)))
         pure ()
process (TypeOf n (Just (l, c)))
    = do Idris.REPL.process (Editing (TypeAt (fromInteger l) (fromInteger c) (UN n)))
         pure ()
process (CaseSplit l c n)
    = do Idris.REPL.process (Editing (CaseSplit (fromInteger l) (fromInteger c) (UN n)))
         pure ()
process (AddClause l n)
    = do Idris.REPL.process (Editing (AddClause (fromInteger l) (UN n)))
         pure ()
process (ExprSearch l n hs all)
    = do Idris.REPL.process (Editing (ExprSearch (fromInteger l) (UN n)
                                                 (map UN hs) all))
         pure ()
process (GenerateDef l n)
    = do Idris.REPL.process (Editing (GenerateDef (fromInteger l) (UN n)))
         pure ()
process (MakeLemma l n)
    = do Idris.REPL.process (Editing (MakeLemma (fromInteger l) (UN n)))
         pure ()
process (MakeCase l n)
    = do Idris.REPL.process (Editing (MakeCase (fromInteger l) (UN n)))
         pure ()
process (MakeWith l n)
    = do Idris.REPL.process (Editing (MakeWith (fromInteger l) (UN n)))
         pure ()
process Version
    = do Idris.REPL.process ShowVersion
         pure ()
process (Metavariables _)
    = do Idris.REPL.process Metavars
         pure ()
process GetOptions
    = do printResult ""
         pure ()

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref MD Metadata} ->
               {auto o : Ref ROpts REPLOpts} ->
               IDECommand -> Core ()
processCatch cmd
    = do c' <- branch
         u' <- get UST
         s' <- get Syn
         o' <- get ROpts
         catch (do process cmd
                   commit)
               (\err => do put Ctxt c'
                           put UST u'
                           put Syn s'
                           put ROpts o'
                           emitError err
                           printError "Command failed")

loop : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST UState} ->
       {auto s : Ref Syn SyntaxInfo} ->
       {auto m : Ref MD Metadata} ->
       {auto o : Ref ROpts REPLOpts} ->
       Core ()
loop
    = do res <- getOutput
         case res of
              REPL _ => printError "Running idemode but output isn't"
              IDEMode _ inf outf => do
                inp <- coreLift $ getInput inf
                end <- coreLift $ fEOF inf
                if end then pure ()
                else case parseSExp inp of
                  Left err =>
                    do printError ("Parse error: " ++ show err)
                       loop
                  Right sexp =>
                    case getMsg sexp of
                      Just (cmd, i) =>
                        do updateOutput i
                           processCatch cmd
                           loop
                      Nothing =>
                        do printError ("Unrecognised command: " ++ show sexp)
                           loop
  where
    updateOutput : Integer -> Core ()
    updateOutput idx
        = do IDEMode _ i o <- getOutput
                 | _ => pure ()
             setOutput (IDEMode idx i o)

export
replIDE : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref MD Metadata} ->
          {auto o : Ref ROpts REPLOpts} ->
          Core ()
replIDE
    = do res <- getOutput
         case res of
              REPL _ => printError "Running idemode but output isn't"
              IDEMode _ inf outf => do
                send outf (version 2 0)
                loop
