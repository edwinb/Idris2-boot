module TTImp.Elab.Check

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.TTImp

public export
record EState (vars : List Name) where
  constructor MkEState
  nextVar : Int

export
data EST : Type where

-- Implemented in TTImp.Elab.Term; delaring just the type allows us to split
-- the elaborator over multiple files more easily
export
check : {vars : _} ->
        {auto c : Ref Ctxt Defs} ->
        {auto e : Ref EST (EState vars)} ->
        RigCount -> Env Term vars -> RawImp -> 
        Maybe (NF vars) ->
        Core (Term vars, NF vars)

-- As above, but doesn't add any implicit lambdas, forces, delays, etc
export
checkImp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> Env Term vars -> RawImp -> Maybe (NF vars) ->
           Core (Term vars, NF vars)

