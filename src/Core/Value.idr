module Core.Value

import Core.Context
import Core.Core
import Core.Env
import Core.TT

public export
record EvalOpts where
  constructor MkEvalOpts
  evalAll : Bool -- evaluate everything, including private names
  tcInline : Bool -- inline for totality checking
  fuel : Maybe Nat -- Limit for recursion depth

export
defaultOpts : EvalOpts
defaultOpts = MkEvalOpts True False Nothing

mutual
  public export
  data LocalEnv : List Name -> List Name -> Type where
       Nil  : LocalEnv free []
       (::) : Closure free -> LocalEnv free vars -> LocalEnv free (x :: vars)

  public export
  data Closure : List Name -> Type where
       MkClosure : (opts : EvalOpts) ->
                   LocalEnv free vars -> 
                   Env Term free ->
                   Term (vars ++ free) -> Closure free
       MkNFClosure : NF free -> Closure free

  -- The head of a value: things you can apply arguments to
  public export
  data NHead : List Name -> Type where
       NLocal : Maybe RigCount -> (idx : Nat) -> IsVar name idx vars ->
                NHead vars
       NRef   : NameType -> Name -> NHead vars
       NMeta  : Name -> Int -> List (AppInfo, Closure vars) -> NHead vars

  -- Values themselves. 'Closure' is an unevaluated thunk, which means 
  -- we can wait until necessary to reduce constructor arguments
  public export
  data NF : List Name -> Type where
       NBind    : FC -> (x : Name) -> Binder (NF vars) ->
                  (Closure vars -> Core (NF vars)) -> NF vars
       NApp     : FC -> NHead vars -> List (AppInfo, Closure vars) -> NF vars
       NDCon    : FC -> Name -> (tag : Int) -> (arity : Nat) -> 
                  List (AppInfo, Closure vars) -> NF vars
       NTCon    : FC -> Name -> (tag : Int) -> (arity : Nat) -> 
                  List (AppInfo, Closure vars) -> NF vars
       NDelayed : FC -> LazyReason -> Closure vars -> NF vars
       NDelay   : FC -> LazyReason -> Closure vars -> NF vars
       NForce   : FC -> NF vars -> NF vars
       NPrimVal : FC -> Constant -> NF vars
       NErased  : FC -> NF vars
       NType    : FC -> NF vars

