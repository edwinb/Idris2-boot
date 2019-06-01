module Idris.REPLCommon

import Core.Context
import Core.InitPrimitives
import Core.Metadata
import Core.Options
import Core.Unify

import Idris.Error
import Idris.IDEMode.Commands
import public Idris.REPLOpts
import Idris.Syntax


-- Output informational messages, unless quiet flag is set
export
iputStrLn : {auto o : Ref ROpts REPLOpts} ->
            String -> Core ()
iputStrLn msg
    = do opts <- get ROpts
         case idemode opts of
              REPL False => coreLift $ putStrLn msg
              REPL _ => pure ()
              IDEMode i _ f =>
                send f (SExpList [SymbolAtom "write-string", 
                                 toSExp msg, toSExp i])
                                                                

printWithStatus : {auto o : Ref ROpts REPLOpts} ->
                  String -> String -> Core ()
printWithStatus status msg
    = do opts <- get ROpts
         case idemode opts of
              REPL _ => coreLift $ putStrLn msg
              IDEMode i _ f =>
                do let m = SExpList [SymbolAtom status, toSExp msg, 
                                     -- highlighting; currently blank
                                     SExpList []]
                   send f (SExpList [SymbolAtom "return", m, toSExp i])

export
printResult : {auto o : Ref ROpts REPLOpts} ->
              String -> Core ()
printResult msg = printWithStatus "ok" msg

-- Return that a protocol request failed somehow
export
printError : {auto o : Ref ROpts REPLOpts} ->
             String -> Core ()
printError msg = printWithStatus "error" msg

-- Display an error message from checking a source file
export
emitError : {auto c : Ref Ctxt Defs} ->
            {auto o : Ref ROpts REPLOpts} ->
            {auto s : Ref Syn SyntaxInfo} ->
            Error FC -> Core FC ()
emitError err
    = do opts <- get ROpts
         case idemode opts of
              REPL _ => 
                  do msg <- display err
                     coreLift $ putStrLn msg
              IDEMode i _ f =>
                  do msg <- perror err
                     case getAnnot err of
                          Nothing => iputStrLn msg
                          Just fc =>
                            send f (SExpList [SymbolAtom "warning", 
                                   SExpList [toSExp (file fc), 
                                            toSExp (addOne (startPos fc)), 
                                              toSExp (addOne (endPos fc)), 
                                              toSExp msg,
                                              -- highlighting; currently blank
                                              SExpList []],
                                    toSExp i])
  where
    addOne : (Int, Int) -> (Int, Int)
    addOne (l, c) = (l + 1, c + 1)

getFCLine : FC -> Int
getFCLine fc = fst (startPos fc)

export
updateErrorLine : {auto o : Ref ROpts REPLOpts} ->
                  List (Error FC) -> Core FC ()
updateErrorLine []
    = do opts <- get ROpts
         put ROpts (record { errorLine = Nothing } opts)
updateErrorLine (e :: es)
    = do opts <- get ROpts
         put ROpts (record { errorLine = map getFCLine (getAnnot e) } opts)

export
resetContext : {auto u : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState FC)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref Meta (Metadata FC)} ->
               Core FC ()
resetContext
    = do defs <- get Ctxt
         put Ctxt (record { options = clearNames (options defs) } initCtxt)
         addPrimitives
         put UST initUState
         put Syn initSyntax
         put Meta initMetadata


