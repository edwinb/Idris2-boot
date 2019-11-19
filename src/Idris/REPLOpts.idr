module Idris.REPLOpts

import Idris.Syntax
import Idris.Socket

public export
data OutputMode
  = IDEMode Integer File File
  | REPL Bool -- quiet flag (ignore iputStrLn)

public export
record REPLOpts where
  constructor MkREPLOpts
  showTypes : Bool
  evalMode : REPLEval
  mainfile : Maybe String
  source : String
  editor : String
  errorLine : Maybe Int
  idemode : OutputMode

export
defaultOpts : Maybe String -> OutputMode -> REPLOpts
defaultOpts fname outmode
   = MkREPLOpts False NormaliseAll fname "" "vim" Nothing outmode

export
data ROpts : Type where

export
replFC : FC
replFC = MkFC "(interactive)" (0, 0) (0, 0)

export
setOutput : {auto o : Ref ROpts REPLOpts} ->
            OutputMode -> Core ()
setOutput m
    = do opts <- get ROpts
         put ROpts (record { idemode = m } opts)

export
getOutput : {auto o : Ref ROpts REPLOpts} -> Core OutputMode
getOutput = do opts <- get ROpts
               pure (idemode opts)

export
setSource : {auto o : Ref ROpts REPLOpts} ->
            String -> Core ()
setSource src
    = do opts <- get ROpts
         put ROpts (record { source = src } opts)

export
getSource : {auto o : Ref ROpts REPLOpts} ->
            Core String
getSource
    = do opts <- get ROpts
         pure (source opts)

export
getSourceLine : {auto o : Ref ROpts REPLOpts} ->
                Int -> Core (Maybe String)
getSourceLine l
    = do src <- getSource
         pure $ findLine (cast (l-1)) (lines src)
  where
    findLine : Nat -> List String -> Maybe String
    findLine Z (l :: ls) = Just l
    findLine (S k) (l :: ls) = findLine k ls
    findLine _ [] = Nothing
