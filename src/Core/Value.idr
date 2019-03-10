module Core.Value

import Core.Context
import Core.Env
import Core.TT

public export
record EvalOpts where
  constructor MkEvalOpts
  holesOnly : Bool -- only evaluate hole solutions
  evalAll : Bool -- evaluate everything, including private names
  tcInline : Bool -- inline for totality checking
  fuel : Maybe Nat -- Limit for recursion depth

-- Context for local unification variables
export
data UCtxt : List Name -> Type where
     MkUCtxt : {wkns : List Name} -> Context (Term vars) ->
               UCtxt (wkns ++ vars)

export
Weaken UCtxt where
  weaken (MkUCtxt {wkns} ctxt) = MkUCtxt {wkns = _ :: wkns} ctxt

export
lookup : Int -> UCtxt ns -> Core (Maybe (Term ns))
lookup i (MkUCtxt {wkns} ctxt)
    = do Just tm <- lookupCtxtExact (Resolved i) ctxt
              | Nothing => pure Nothing
         pure (Just (weakenNs wkns tm))

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
       NBlocked : Closure vars -> NHead vars -- complex blocked term, e.g. Case

  -- Values themselves
  public export
  data NF : List Name -> Type where
       NBind    : FC -> (x : Name) -> Binder (NF vars) ->
                  (Closure vars -> NF vars) -> NF vars
       NApp     : FC -> NHead vars -> List (Closure vars) -> NF vars
       NDCon    : FC -> Name -> (tag : Int) -> (arity : Nat) -> 
                  List (Closure vars) -> NF vars
       NTCon    : FC -> Name -> (tag : Int) -> (arity : Nat) -> 
                  List (Closure vars) -> NF vars
       NPrimVal : FC -> Constant -> NF vars
       NErased  : FC -> NF vars
       NType    : FC -> NF vars

