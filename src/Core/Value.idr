module Core.Value

import Core.Context
import Core.Core
import Core.Env
import Core.TT

import Data.IntMap

public export
record EvalOpts where
  constructor MkEvalOpts
  holesOnly : Bool -- only evaluate hole solutions
  argHolesOnly : Bool -- only evaluate holes which are relevant arguments
  removeAs : Bool -- reduce 'as' patterns (don't do this on LHS)
  usedMetas : IntMap () -- Metavariables we're under, to detect cycles
  evalAll : Bool -- evaluate everything, including private names
  tcInline : Bool -- inline for totality checking
  fuel : Maybe Nat -- Limit for recursion depth

export
defaultOpts : EvalOpts
defaultOpts = MkEvalOpts False False True empty False False Nothing

export
withHoles : EvalOpts
withHoles = MkEvalOpts True True False empty False False Nothing

export
withAll : EvalOpts
withAll = MkEvalOpts False False True empty True False Nothing

export
withArgHoles : EvalOpts
withArgHoles = MkEvalOpts False True False empty False False Nothing

export
tcOnly : EvalOpts
tcOnly = record { tcInline = True } withArgHoles

export
onLHS : EvalOpts
onLHS = record { removeAs = False } defaultOpts

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
       NLocal : Maybe Bool -> (idx : Nat) -> IsVar name idx vars ->
                NHead vars
       NRef   : NameType -> Name -> NHead vars
       NMeta  : Name -> Int -> List (Closure vars) -> NHead vars

  -- Values themselves. 'Closure' is an unevaluated thunk, which means
  -- we can wait until necessary to reduce constructor arguments
  public export
  data NF : List Name -> Type where
       NBind    : FC -> (x : Name) -> Binder (NF vars) ->
                  (Defs -> Closure vars -> Core (NF vars)) -> NF vars
       NApp     : FC -> NHead vars -> List (Closure vars) -> NF vars
       NDCon    : FC -> Name -> (tag : Int) -> (arity : Nat) ->
                  List (Closure vars) -> NF vars
       NTCon    : FC -> Name -> (tag : Int) -> (arity : Nat) ->
                  List (Closure vars) -> NF vars
       NAs      : FC -> NF vars -> NF vars -> NF vars
       NDelayed : FC -> LazyReason -> NF vars -> NF vars
       NDelay   : FC -> LazyReason -> Closure vars -> Closure vars -> NF vars
       NForce   : FC -> NF vars -> List (Closure vars) -> NF vars
       NPrimVal : FC -> Constant -> NF vars
       NErased  : FC -> NF vars
       NType    : FC -> NF vars

export
getLoc : NF vars -> FC
getLoc (NBind fc _ _ _) = fc
getLoc (NApp fc _ _) = fc
getLoc (NDCon fc _ _ _ _) = fc
getLoc (NTCon fc _ _ _ _) = fc
getLoc (NAs fc _ _) = fc
getLoc (NDelayed fc _ _) = fc
getLoc (NDelay fc _ _ _) = fc
getLoc (NForce fc _ _) = fc
getLoc (NPrimVal fc _) = fc
getLoc (NErased fc) = fc
getLoc (NType fc) = fc

