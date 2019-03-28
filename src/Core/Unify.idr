module Core.Unify

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import public Core.UnifyState
import Core.Value

import Data.IntMap

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

ufail : FC -> String -> Core a
ufail loc msg = throw (GenericMsg loc msg)

convertError : FC -> Env Term vars -> Term vars -> Term vars -> Core a
convertError loc env x y = throw (CantConvert loc env x y)

convertErrorS : Bool -> FC -> Env Term vars -> Term vars -> Term vars -> Core a
convertErrorS s loc env x y 
    = if s then throw (CantConvert loc env y x)
           else throw (CantConvert loc env x y)

postpone : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           FC -> Env Term vars -> NF vars -> NF vars -> Core (List Int)
postpone loc env x y
    = do defs <- get Ctxt
         empty <- clearDefs defs
         c <- addConstraint (MkConstraint loc env !(quote empty env x) 
                                                  !(quote empty env y))
         pure [c]

unifyArgs : (Unify tm, Quote tm) =>
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            UnifyMode -> FC -> Env Term vars ->
            List (tm vars) -> List (tm vars) ->
            Core (List Int)
unifyArgs mode loc env [] [] = pure []
unifyArgs mode loc env (cx :: cxs) (cy :: cys)
    = do constr <- unify mode loc env cx cy
         case constr of
              [] => unifyArgs mode loc env cxs cys
              _ => do cs <- unifyArgs mode loc env cxs cys
                      -- TODO: Fix this bit! See p59 Ulf's thesis
--                       c <- addConstraint 
--                                (MkSeqConstraint loc env 
--                                    (map (quote gam env) (cx :: cxs))
--                                    (map (quote gam env) (cy :: cys)))
                      pure (union constr cs) -- [c]
unifyArgs mode loc env _ _ = ufail loc ""

mutual
  unifyIfEq : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              (postpone : Bool) ->
              FC -> Env Term vars -> NF vars -> NF vars -> 
              Core (List Int)
  unifyIfEq post loc env x y 
        = do defs <- get Ctxt
             empty <- clearDefs defs
             if !(convert defs env x y)
                then pure []
                else if post 
                        then do -- log 10 $ "Postponing constraint (unifyIfEq) " ++
                                --         show !(quote empty env x) ++ " =?= " ++
                                --         show !(quote empty env y)
                                postpone loc env x y
                        else convertError loc env 
                                     !(quote empty env x)
                                     !(quote empty env y)

  unifyNoEta : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               UnifyMode -> FC -> Env Term vars ->
               NF vars -> NF vars ->
               Core (List Int)
  unifyNoEta mode loc env x y 
      = do defs <- get Ctxt
           empty <- clearDefs defs
           unifyIfEq False loc env x y

  export
  Unify NF where
    -- TODO: Eta!
    unifyD _ _ mode loc env tmx tmy = unifyNoEta mode loc env tmx tmy

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

public export
data SolveMode = Normal -- during elaboration: unifies and searches
               | Defaults -- unifies and searches for default hints only
               | LastChance -- as normal, but any failure throws rather than delays

retry : {auto c : Ref Ctxt Defs} ->
        {auto u : Ref UST UState} ->
        UnifyMode -> Int -> Core (List Int)
retry mode c
    = do ust <- get UST
         case lookup c (constraints ust) of
              Nothing => pure []
              Just Resolved => pure []
              Just (MkConstraint loc env x y)
                  => catch (do log 5 $ "Retrying " ++ show x ++ " and " ++ show y
                               cs <- unify mode loc env x y 
                               case cs of
                                 [] => do setConstraint c Resolved
                                          pure []
                                 _ => pure cs)
                       (\err => throw (WhenUnifying loc env x y err)) 
              Just (MkSeqConstraint loc env xs ys)
                  => do cs <- unifyArgs mode loc env xs ys
                        case cs of
                             [] => do setConstraint c Resolved
                                      pure []
                             _ => pure cs

-- Retry the given constraint, return True if progress was made
retryGuess : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             UnifyMode -> (smode : SolveMode) -> (hole : (FC, Name, Int)) ->
             Core Bool
retryGuess mode smode (loc, hname, hid)
    = do defs <- get Ctxt
         case !(lookupCtxtExact (Resolved hid) (gamma defs)) of
           Nothing => pure False
           Just def =>
             case definition def of
               Guess tm constraints => 
                 do cs' <- traverse (retry mode) constraints
                    case concat cs' of
                         -- All constraints resolved, so turn into a
                         -- proper definition and remove it from the
                         -- hole list
                         [] => do let gdef = record { definition = Fn tm } def
                                  addDef (Resolved hid) gdef
                                  removeGuess hid
                                  pure True
                         newcs => do let gdef = record { definition = Guess tm newcs } def
                                     addDef (Resolved hid) gdef
                                     pure False
               _ => pure False

export
solveConstraints : {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   UnifyMode -> (smode : SolveMode) -> Core ()
solveConstraints umode smode
    = do ust <- get UST
         progress <- traverse (retryGuess umode smode) (guesses ust)
         when (or (map Delay progress)) $ solveConstraints umode smode

