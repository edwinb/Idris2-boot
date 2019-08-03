module Idris.SetOptions

import Core.Context
import Core.Directory
import Core.Metadata
import Core.Options
import Core.Unify

import Idris.CommandLine
import Idris.REPL
import Idris.Syntax

import System

-- TODO: Version numbers on dependencies
export
addPkgDir : {auto c : Ref Ctxt Defs} ->
            String -> Core ()
addPkgDir p
    = do defs <- get Ctxt
         addExtraDir (dir_prefix (dirs (options defs)) ++ dirSep ++ 
                             "idris2" ++ dirSep ++ p)

-- Options to be processed before type checking
export
preOptions : {auto c : Ref Ctxt Defs} ->
             {auto o : Ref ROpts REPLOpts} ->
             List CLOpt -> Core ()
preOptions [] = pure ()
preOptions (Quiet :: opts)
    = do setOutput (REPL True)
         preOptions opts
preOptions (NoPrelude :: opts)
    = do setSession (record { noprelude = True } !getSession)
         preOptions opts
preOptions (SetCG e :: opts)
    = case getCG e of
           Just cg => do setCG cg
                         preOptions opts
           Nothing => 
              do coreLift $ putStrLn "No such code generator"
                 coreLift $ putStrLn $ "Code generators available: " ++
                                 showSep ", " (map fst availableCGs)
                 coreLift $ exit 1
preOptions (PkgPath p :: opts)
    = do addPkgDir p
         preOptions opts
preOptions (Timing :: opts)
    = setLogTimings True
preOptions (_ :: opts) = preOptions opts

-- Options to be processed after type checking. Returns whether execution
-- should continue (i.e., whether to start a REPL)
export
postOptions : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto m : Ref MD Metadata} ->
              {auto o : Ref ROpts REPLOpts} ->
              List CLOpt -> Core Bool
postOptions [] = pure True
postOptions (OutputFile outfile :: rest)
    = do compileExp (PRef (MkFC "(script)" (0, 0) (0, 0)) (UN "main")) outfile
         postOptions rest
         pure False
postOptions (ExecFn str :: rest) 
    = do execExp (PRef (MkFC "(script)" (0, 0) (0, 0)) (UN str))
         postOptions rest
         pure False
postOptions (CheckOnly :: rest) 
    = do postOptions rest
         pure False
postOptions (_ :: rest) = postOptions rest

export
ideMode : List CLOpt -> Bool
ideMode [] = False
ideMode (IdeMode :: _) = True
ideMode (_ :: xs) = ideMode xs

export
ideModeSocket : List CLOpt -> Bool
ideModeSocket [] = False
ideModeSocket (IdeModeSocket :: _) = True
ideModeSocket (_ :: xs) = ideModeSocket xs

