module Core.Unify

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value

%default covering

public export
data UnifyMode = InLHS
               | InTerm
               | InDot
               | InSearch

Eq UnifyMode where
   InLHS == InLHS = True
   InTerm == InTerm = True
   InDot == InDot = True
   InSearch == InSearch = True
   _ == _ = False

public export
interface Unify (tm : List Name -> Type) where
  -- Unify returns a list of ids referring to newly added constraints
  unifyD : Ref Ctxt Defs ->
           Ref UST UState ->
           UnifyMode ->
           FC -> Env Term vars ->
           tm vars -> tm vars -> 
           Core (List Int)

-- Workaround for auto implicits not working in interfaces
-- In calls to unification, the first argument is the given type, and the second
-- argument is the expected type.
export
unify : Unify tm => 
        {auto c : Ref Ctxt Defs} ->
        {auto u : Ref UST UState} ->
        UnifyMode ->
        FC -> Env Term vars ->
        tm vars -> tm vars -> 
        Core (List Int)
unify {c} {u} = unifyD c u

mutual

  export
  Unify NF where

  export
  Unify Term where
    unifyD _ _ mode loc env x y 
          = do gam <- get Ctxt
               if !(convert gam env x y)
                  then do log 10 $ "Skipped unification (convert already): "
                                 ++ show x ++ " and " ++ show y
                          pure []
                  else unify mode loc env !(nf gam env x) !(nf gam env y)

  export
  Unify Closure where
    unifyD _ _ mode loc env x y 
        = do gam <- get Ctxt
             empty <- clearDefs gam
             -- 'quote' using an empty global context, because then function
             -- names won't reduce until they have to
             unify mode loc env !(quote empty env x) !(quote empty env y)

