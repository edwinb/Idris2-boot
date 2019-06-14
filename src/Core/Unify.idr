module Core.Unify

import Core.CaseTree
import Core.Context
import Core.Core
import Core.Env
import Core.GetType
import Core.Normalise
import Core.TT
import public Core.UnifyState
import Core.Value

import Data.IntMap
import Data.List.Views

%default covering

public export
data UnifyMode = InLHS
               | InTerm
               | InSearch

Eq UnifyMode where
   InLHS == InLHS = True
   InTerm == InTerm = True
   InSearch == InSearch = True
   _ == _ = False

-- If we're unifying a Lazy type with a non-lazy type, we need to add an
-- explicit force or delay to the first argument to unification. This says
-- which to add, if any. Can only added at the very top level.
public export
data AddLazy = NoLazy | AddForce | AddDelay LazyReason

export
Show AddLazy where
  show NoLazy = "NoLazy"
  show AddForce = "AddForce"
  show (AddDelay _) = "AddDelay"

public export
record UnifyResult where
  constructor MkUnifyResult
  constraints : List Int
  holesSolved : Bool
  addLazy : AddLazy

union : UnifyResult -> UnifyResult -> UnifyResult
union u1 u2 = MkUnifyResult (union (constraints u1) (constraints u2))
                            (holesSolved u1 || holesSolved u2)
                            NoLazy -- only top level, so assume no annotation

unionAll : List UnifyResult -> UnifyResult
unionAll [] = MkUnifyResult [] False NoLazy
unionAll [c] = c
unionAll (c :: cs) = union c (unionAll cs)

constrain : Int -> UnifyResult
constrain c = MkUnifyResult [c] False NoLazy

success : UnifyResult
success = MkUnifyResult [] False NoLazy

solvedHole : UnifyResult
solvedHole = MkUnifyResult [] True NoLazy

public export
interface Unify (tm : List Name -> Type) where
  -- Unify returns a list of ids referring to newly added constraints
  unifyD : Ref Ctxt Defs ->
           Ref UST UState ->
           UnifyMode ->
           FC -> Env Term vars ->
           tm vars -> tm vars -> 
           Core UnifyResult
  -- As unify but at the top level can allow lazy/non-lazy to be mixed in
  -- order to infer annotations
  unifyWithLazyD : Ref Ctxt Defs ->
                   Ref UST UState ->
                   UnifyMode ->
                   FC -> Env Term vars ->
                   tm vars -> tm vars -> 
                   Core UnifyResult
  unifyWithLazyD = unifyD

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
        Core UnifyResult
unify {c} {u} = unifyD c u

export
unifyWithLazy : Unify tm => 
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                UnifyMode ->
                FC -> Env Term vars ->
                tm vars -> tm vars -> 
                Core UnifyResult
unifyWithLazy {c} {u} = unifyWithLazyD c u

-- Defined in Core.AutoSearch
export
search : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         FC -> RigCount ->
         (defaults : Bool) -> (depth : Nat) ->
         (defining : Name) -> (topTy : Term vars) -> Env Term vars -> 
         Core (Term vars)

ufail : FC -> String -> Core a
ufail loc msg = throw (GenericMsg loc msg)

convertError : {auto c : Ref Ctxt Defs} ->
               FC -> Env Term vars -> NF vars -> NF vars -> Core a
convertError loc env x y 
    = do defs <- get Ctxt
         empty <- clearDefs defs
         throw (CantConvert loc env !(quote empty env x) 
                                    !(quote empty env y))

convertErrorS : {auto c : Ref Ctxt Defs} ->
                Bool -> FC -> Env Term vars -> NF vars -> NF vars -> Core a
convertErrorS s loc env x y 
    = if s then convertError loc env y x
           else convertError loc env x y

export
postpone : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           FC -> String -> Env Term vars -> NF vars -> NF vars -> Core UnifyResult
postpone loc logstr env x y
    = do defs <- get Ctxt
         empty <- clearDefs defs
         logC 10 $
              do xq <- quote defs env x
                 yq <- quote defs env y
                 pure (logstr ++ ": " ++ show !(toFullNames xq) ++ 
                                    " =?= " ++ show !(toFullNames yq))
         c <- addConstraint (MkConstraint loc env !(quote empty env x) 
                                                  !(quote empty env y))
         pure (constrain c)

postponeS : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Bool -> FC -> String -> Env Term vars ->
            NF vars -> NF vars ->
            Core UnifyResult
postponeS s loc logstr env x y
    = if s then postpone loc logstr env y x
           else postpone loc logstr env x y

unifyArgs : (Unify tm, Quote tm) =>
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            UnifyMode -> FC -> Env Term vars ->
            List (tm vars) -> List (tm vars) ->
            Core UnifyResult
unifyArgs mode loc env [] [] = pure success
unifyArgs mode loc env (cx :: cxs) (cy :: cys)
    = do res <- unify mode loc env cx cy
         case constraints res of
              [] => unifyArgs mode loc env cxs cys
              _ => do cs <- unifyArgs mode loc env cxs cys
                      -- TODO: Fix this bit! See p59 Ulf's thesis
--                       c <- addConstraint 
--                                (MkSeqConstraint loc env 
--                                    (map (quote gam env) (cx :: cxs))
--                                    (map (quote gam env) (cy :: cys)))
                      pure (union res cs) -- [c]
unifyArgs mode loc env _ _ = ufail loc ""

-- Get the variables in an application argument list; fail if any arguments 
-- are not variables, fail if there's any repetition of variables
-- We use this to check that the pattern unification rule is applicable
-- when solving a metavariable applied to arguments
getVarsBelow : Nat -> List (NF vars) -> Maybe (List (Var vars))
getVarsBelow max [] = Just []
getVarsBelow max (NApp fc (NLocal r idx v) [] :: xs) 
    = if idx >= max then Nothing
         else do xs' <- getVarsBelow idx xs
                 pure (MkVar v :: xs')
getVarsBelow _ (_ :: xs) = Nothing

-- Make a sublist representing the variables used in the application.
-- We'll use this to ensure that local variables which appear in a term
-- are all arguments to a metavariable application for pattern unification
toSubVars : (vars : List Name) -> List (Var vars) ->
            (newvars ** SubVars newvars vars)
toSubVars [] xs = ([] ** SubRefl)
toSubVars (n :: ns) xs 
     -- If there's a proof 'First' in 'xs', then 'n' should be kept,
     -- otherwise dropped
     -- (Remember: 'n' might be shadowed; looking for 'First' ensures we
     -- get the *right* proof that the name is in scope!)
     = let (_ ** svs) = toSubVars ns (dropFirst xs) in
           if anyFirst xs 
              then (_ ** KeepCons svs)
              else (_ ** DropCons svs)
  where
    anyFirst : List (Var (n :: ns)) -> Bool
    anyFirst [] = False
    anyFirst (MkVar First :: xs) = True
    anyFirst (MkVar (Later p) :: xs) = anyFirst xs

{- Applying the pattern unification rule is okay if:
   * Arguments are all distinct local variables
   * The metavariable name doesn't appear in the unifying term
   * The local variables which appear in the term are all arguments to
     the metavariable application (not checked here, checked with the
     result of `patternEnv`)

   Return the subset of the environment used in the arguments
   to which the metavariable is applied. If this environment is enough
   to check the term we're unifying with, and that term doesn't use the
   metavariable name, we can safely apply the rule.

   Also, return the list of arguments the metavariable was applied to, to
   make sure we use them in the right order when we build the solution.
-}
patternEnv : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {vars : _} ->
             Env Term vars -> List (Closure vars) -> 
             Core (Maybe (newvars ** (Maybe (List (Var newvars)),
                                     SubVars newvars vars)))
patternEnv {vars} env args
    = do defs <- get Ctxt
         empty <- clearDefs defs
         args' <- traverse (evalArg empty) args
         case getVarsBelow 1000000 args' of
              Nothing => pure Nothing
              Just vs => 
                 let (newvars ** svs) = toSubVars _ vs in
                     pure (Just (newvars ** 
                                     (if vars == newvars
                                         then Nothing
                                         else Just (updateVars vs svs), svs)))
  where
    -- Update the variable list to point into the sub environment
    -- (All of these will succeed because the SubVars we have comes from
    -- the list of variable uses! It's not stated in the type, though.)
    updateVars : List (Var vars) -> SubVars newvars vars -> List (Var newvars)
    updateVars [] svs = []
    updateVars (MkVar p :: ps) svs
        = case subElem p svs of
               Nothing => updateVars ps svs
               Just p' => p' :: updateVars ps svs
  
getVarsBelowTm : Nat -> List (Term vars) -> Maybe (List (Var vars))
getVarsBelowTm max [] = Just []
getVarsBelowTm max (Local fc r idx v :: xs) 
    = if idx >= max then Nothing
         else do xs' <- getVarsBelowTm idx xs
                 pure (MkVar v :: xs')
getVarsBelowTm _ (_ :: xs) = Nothing

export
patternEnvTm : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {vars : _} ->
               Env Term vars -> List (Term vars) -> 
               Core (Maybe (newvars ** (Maybe (List (Var newvars)),
                                       SubVars newvars vars)))
patternEnvTm {vars} env args
    = do defs <- get Ctxt
         empty <- clearDefs defs
         case getVarsBelowTm 1000000 args of
              Nothing => pure Nothing
              Just vs => 
                 let (newvars ** svs) = toSubVars _ vs in
                     pure (Just (newvars ** 
                                     (if vars == newvars
                                         then Nothing
                                         else Just (updateVars vs svs), svs)))
  where
    -- Update the variable list to point into the sub environment
    -- (All of these will succeed because the SubVars we have comes from
    -- the list of variable uses! It's not stated in the type, though.)
    updateVars : List (Var vars) -> SubVars newvars vars -> List (Var newvars)
    updateVars [] svs = []
    updateVars (MkVar p :: ps) svs
        = case subElem p svs of
               Nothing => updateVars ps svs
               Just p' => p' :: updateVars ps svs

-- Instantiate a metavariable by binding the variables in 'newvars'
-- and returning the term
-- If the type of the metavariable doesn't have enough arguments, fail, because
-- this wasn't valid for pattern unification
export
instantiate : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {newvars : _} ->
              FC -> Env Term vars -> 
              (metavar : Name) -> (mref : Int) -> (mdef : GlobalDef) ->
              Maybe (List (Var newvars)) -> -- Variable each argument maps to
              Term vars -> -- original, just for error message
              Term newvars -> -- shrunk environment
              Core ()
instantiate {newvars} loc env mname mref mdef locs otm tm
    = do log 5 $ "Instantiating " ++ show tm ++ " in " ++ show newvars 
--          let Hole _ _ = definition mdef
--              | def => ufail {a=()} loc (show mname ++ " already resolved as " ++ show def)
         case fullname mdef of
              PV pv pi => throw (PatternVariableUnifies loc env (PV pv pi) otm)
              _ => pure ()
         let ty = type mdef
         defs <- get Ctxt
         rhs <- mkDef [] newvars (snocList newvars) CompatPre
                     (rewrite appendNilRightNeutral newvars in locs)
                     (rewrite appendNilRightNeutral newvars in tm) 
                     !(nf defs [] ty)
         logTerm 5 ("Instantiated: " ++ show mname) ty
         logTerm 5 "Definition" rhs
         let newdef = record { definition = 
                                 PMDef [] (STerm rhs) (STerm rhs) [] 
                             } mdef
         addDef (Resolved mref) newdef
         removeHole mref
  where
    updateLoc : {v : Nat} -> List (Var vs) -> .(IsVar name v vs') -> 
                Maybe (Var vs)
    updateLoc [] el = Nothing
    updateLoc (p :: ps) First = Just p
    updateLoc (p :: ps) (Later prf) = updateLoc ps prf

    -- Since the order of variables is not necessarily the same in the solution,
    -- this is to make sure the variables point to the right argument, given
    -- the argument list we got from the application of the hole.
    updateLocs : List (Var vs) -> Term vs -> Maybe (Term vs)
    updateLocs locs (Local fc r idx p)
        = do MkVar p' <- updateLoc locs p
             Just (Local fc r _ p')
    updateLocs {vs} locs (Bind fc x b sc)
        = do b' <- updateLocsB b
             sc' <- updateLocs 
                       (MkVar First :: map (\ (MkVar p) => (MkVar (Later p))) locs) 
                       sc
             Just (Bind fc x b' sc')
      where
        updateLocsB : Binder (Term vs) -> Maybe (Binder (Term vs))
        updateLocsB (Lam c p t) = Just (Lam c p !(updateLocs locs t))
        updateLocsB (Let c v t) = Just (Let c !(updateLocs locs v) !(updateLocs locs t))
        updateLocsB (Pi c p t) = Just (Pi c p !(updateLocs locs t))
        updateLocsB (PVar c t) = Just (PVar c !(updateLocs locs t))
        updateLocsB (PLet c v t) = Just (PLet c !(updateLocs locs v) !(updateLocs locs t))
        updateLocsB (PVTy c t) = Just (PVTy c !(updateLocs locs t))

    updateLocs locs (App fc f a)
        = Just (App fc !(updateLocs locs f) !(updateLocs locs a))
    updateLocs locs tm = Just tm

    mkDef : (got : List Name) -> (vs : List Name) -> SnocList vs ->
            CompatibleVars got rest ->
            Maybe (List (Var (vs ++ got))) -> Term (vs ++ got) -> 
            NF [] -> Core (Term rest)
    mkDef got [] Empty cvs locs tm ty 
        = do let Just tm' = maybe (Just tm) (\lvs => updateLocs (reverse lvs) tm) locs
                    | Nothing => ufail loc ("Can't make solution for " ++ show mname)
             pure (renameVars cvs tm')
    mkDef got (vs ++ [v]) (Snoc rec) cvs locs tm (NBind bfc x (Pi c _ ty) scfn) 
        = do defs <- get Ctxt
             sc <- scfn defs (toClosure defaultOpts [] (Erased bfc))
             sc' <- mkDef (v :: got) vs rec (CompatExt cvs)
                       (rewrite appendAssociative vs [v] got in locs)
                       (rewrite appendAssociative vs [v] got in tm)
                       sc
             pure (Bind bfc x (Lam c Explicit (Erased bfc)) sc')
    mkDef got (vs ++ [v]) (Snoc rec) cvs locs tm ty
        = ufail loc $ "Can't make solution for " ++ show mname  

isDefInvertible : {auto c : Ref Ctxt Defs} ->
                  Int -> Core Bool
isDefInvertible i
    = do defs <- get Ctxt
         Just (Hole _ t) <- lookupDefExact (Resolved i) (gamma defs)
              | _ => pure False
         pure t

mutual
  unifyIfEq : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars : _} ->
              (postpone : Bool) ->
              FC -> Env Term vars -> NF vars -> NF vars -> 
              Core UnifyResult
  unifyIfEq post loc env x y 
        = do defs <- get Ctxt
             if !(convert defs env x y)
                then pure success
                else if post 
                        then postpone loc "Postponing unifyIfEq" env x y
                        else convertError loc env x y

  getArgTypes : Defs -> (fnType : NF vars) -> List (Closure vars) -> 
                Core (Maybe (List (NF vars)))
  getArgTypes defs (NBind _ n (Pi _ _ ty) sc) (a :: as)
     = do Just scTys <- getArgTypes defs !(sc defs a) as
               | Nothing => pure Nothing
          pure (Just (ty :: scTys))
  getArgTypes _ _ [] = pure (Just [])
  getArgTypes _ _ _ = pure Nothing

  headsConvert : {auto c : Ref Ctxt Defs} ->
                 Env Term vars -> 
                 Maybe (List (NF vars)) -> Maybe (List (NF vars)) ->
                 Core Bool
  headsConvert env (Just vs) (Just ns)
      = case (reverse vs, reverse ns) of
             (v :: _, n :: _) => 
                do logNF 10 "Converting" env v
                   logNF 10 "......with" env n
                   defs <- get Ctxt
                   convert defs env v n
             _ => pure False
  headsConvert env _ _ 
      = do log 10 "Nothing to convert"
           pure True

  unifyInvertible : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    {vars : _} ->
                    UnifyMode -> FC -> Env Term vars ->
                    (metaname : Name) -> (metaref : Int) ->
                    (margs : List (Closure vars)) ->
                    (margs' : List (Closure vars)) ->
                    Maybe ClosedTerm ->
                    (List (Closure vars) -> NF vars) ->
                    List (Closure vars) ->
                    Core UnifyResult
  unifyInvertible mode fc env mname mref margs margs' nty con args'
      = do defs <- get Ctxt
           -- Get the types of the arguments to ensure that the rightmost
           -- argument types match up
           Just vty <- lookupTyExact (Resolved mref) (gamma defs)
                | Nothing => ufail fc ("No such metavariable " ++ show mname)
           vargTys <- getArgTypes defs !(nf defs env (embed vty)) (margs ++ margs')
           nargTys <- maybe (pure Nothing)
                            (\ty => getArgTypes defs !(nf defs env (embed ty)) args')
                            nty
           -- If the rightmost arguments have the same type, or we don't
           -- know the types of the arguments, we'll get on with it.
           if !(headsConvert env vargTys nargTys)
              then 
                -- Unify the rightmost arguments, with the goal of turning the
                -- hole application into a pattern form
                case (reverse margs', reverse args') of
                     (h :: hargs, f :: fargs) =>
                        tryUnify
                          (do log 10 "Unifying invertible"
                              ures <- unify mode fc env h f
                              log 10 $ "Constraints " ++ show (constraints ures)
                              uargs <- unify mode fc env 
                                    (NApp fc (NMeta mname mref margs) (reverse hargs))
                                    (con (reverse fargs))
                              pure (union ures uargs))
                          (postpone fc "Postponing hole application [1]" env
                                (NApp fc (NMeta mname mref margs) margs')
                                (con args'))
                     _ => postpone fc "Postponing hole application [2]" env
                                (NApp fc (NMeta mname mref margs) margs')
                                (con args')
              else -- TODO: Cancellable function applications
                   postpone fc "Postponing hole application [3]" env 
                            (NApp fc (NMeta mname mref margs) margs') (con args')

  -- Unify a hole application - we have already checked that the hole is
  -- invertible (i.e. it's a determining argument to a proof search where
  -- it is a constructor or something else invertible in each case)
  unifyHoleApp : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 {vars : _} ->
                 UnifyMode -> FC -> Env Term vars ->
                 (metaname : Name) -> (metaref : Int) ->
                 (margs : List (Closure vars)) ->
                 (margs' : List (Closure vars)) ->
                 NF vars ->
                 Core UnifyResult
  unifyHoleApp mode loc env mname mref margs margs' (NTCon nfc n t a args')
      = do defs <- get Ctxt
           mty <- lookupTyExact n (gamma defs)
           unifyInvertible mode loc env mname mref margs margs' mty (NTCon nfc n t a) args'
  unifyHoleApp mode loc env mname mref margs margs' (NDCon nfc n t a args')
      = do defs <- get Ctxt
           mty <- lookupTyExact n (gamma defs)
           unifyInvertible mode loc env mname mref margs margs' mty (NTCon nfc n t a) args'
  unifyHoleApp mode loc env mname mref margs margs' (NApp nfc (NLocal r idx p) args')
      = unifyInvertible mode loc env mname mref margs margs' Nothing 
                        (NApp nfc (NLocal r idx p)) args'
  unifyHoleApp mode loc env mname mref margs margs' tm@(NApp nfc (NMeta n i margs2) args2')
      = do defs <- get Ctxt
           Just mdef <- lookupCtxtExact (Resolved i) (gamma defs)
                | Nothing => throw (UndefinedName nfc mname)
           let inv = case definition mdef of
                          Hole _ i => i
                          _ => isPatName n
           if inv
              then unifyInvertible mode loc env mname mref margs margs' Nothing
                                   (NApp nfc (NMeta n i margs2)) args2'
              else postpone loc "Postponing hole application" env 
                             (NApp loc (NMeta mname mref margs) margs') tm
    where
      isPatName : Name -> Bool
      isPatName (PV _ _) = True
      isPatName _ = False
           
  unifyHoleApp mode loc env mname mref margs margs' tm
      = postpone loc "Postponing hole application" env 
                 (NApp loc (NMeta mname mref margs) margs') tm

  unifyPatVar : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {vars : _} ->
                UnifyMode -> FC -> Env Term vars ->
                (metaname : Name) -> (metaref : Int) ->
                (margs : List (Closure vars)) ->
                (margs' : List (Closure vars)) ->
                (soln : NF vars) ->
                Core UnifyResult
  -- TODO: if either side is a pattern variable application, and we're in a term,
  -- (which will be a type) we can proceed because the pattern variable
  -- has to end up pi bound. Unify the right most variables, and continue.
  unifyPatVar mode loc env mname mref margs margs' tm
      = postpone loc "Not in pattern fragment" env 
                 (NApp loc (NMeta mname mref margs) margs') tm

  solveHole : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars : _} ->
              FC -> Env Term vars ->
              (metaname : Name) -> (metaref : Int) ->
              (margs : List (Closure vars)) ->
              (margs' : List (Closure vars)) ->
              Maybe (List (Var newvars)) ->
              SubVars newvars vars ->
              (solfull : Term vars) -> -- Original solution
              (soln : Term newvars) -> -- Solution with shrunk environment
              (solnf : NF vars) ->
              Core UnifyResult
  solveHole loc env mname mref margs margs' locs submv solfull stm solnf
      = do defs <- get Ctxt
           empty <- clearDefs defs
           -- if the terms are the same, this isn't a solution
           -- but they are already unifying, so just return
           if solutionHeadSame solnf 
              then pure success
              else -- Rather than doing the occurs check here immediately,
                   -- we'll wait until all metavariables are resolved, and in
                   -- the meantime look out for cycles when normalising (which
                   -- is cheap enough because we only need to look out for
                   -- metavariables)
                   do Just hdef <- lookupCtxtExact (Resolved mref) (gamma defs)
                           | Nothing => throw (InternalError ("Can't happen: Lost hole " ++ show mname))
                      instantiate loc env mname mref hdef locs solfull stm
                      pure solvedHole
    where
      -- Only need to check the head metavar is the same, we've already
      -- checked the rest if they are the same (and we couldn't instantiate it
      -- anyway...)
      solutionHeadSame : NF vars -> Bool
      solutionHeadSame (NApp _ (NMeta _ shead _) _) = shead == mref
      solutionHeadSame _ = False

  unifyHole : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars : _} ->
              UnifyMode -> FC -> Env Term vars ->
              FC -> (metaname : Name) -> (metaref : Int) ->
              (args : List (Closure vars)) ->
              (args' : List (Closure vars)) ->
              (soln : NF vars) ->
              Core UnifyResult
  unifyHole mode loc env fc mname mref margs margs' tmnf
      = do defs <- get Ctxt
           empty <- clearDefs defs
           let args = margs ++ margs'
           logC 10 (do args' <- traverse (evalArg empty) args
                       qargs <- traverse (quote empty env) args'
                       qtm <- quote empty env tmnf
                       pure $ "Unifying: " ++ show mname ++ " " ++ show qargs ++
                              " with " ++ show qtm)
           case !(patternEnv env args) of
                Nothing => 
                  do Just (Hole _ inv) <- lookupDefExact (Resolved mref) (gamma defs)
                        | _ => unifyPatVar mode loc env mname mref margs margs' tmnf
                     if inv
                        then unifyHoleApp mode loc env mname mref margs margs' tmnf
                        else unifyPatVar mode loc env mname mref margs margs' tmnf
                Just (newvars ** (locs, submv)) => 
                  do tm <- quote empty env tmnf
                     case shrinkTerm tm submv of
                          Just stm => solveHole fc env mname mref 
                                                margs margs' locs submv 
                                                tm stm tmnf
                          Nothing => 
                            do tm' <- normalise defs env tm
                               case shrinkTerm tm' submv of
                                    Nothing => postpone loc "Can't shrink" env
                                               (NApp loc (NMeta mname mref margs) margs')
                                               tmnf
                                    Just stm => solveHole fc env mname mref 
                                                          margs margs' locs submv 
                                                          tm stm tmnf

  -- Unify an application with something else
  unifyApp : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {vars : _} ->
             (swaporder : Bool) -> -- swap the order when postponing
                                   -- (this is to preserve second arg being expected type)
             UnifyMode -> FC -> Env Term vars -> FC ->
             NHead vars -> List (Closure vars) -> NF vars ->
             Core UnifyResult
  unifyApp swap mode loc env fc (NMeta n i margs) args tm
      = unifyHole mode loc env fc n i margs args tm
  unifyApp swap mode loc env fc hd args (NApp mfc (NMeta n i margs) margs')
      = unifyHole mode loc env mfc n i margs margs' (NApp fc hd args)
  -- Postpone if a name application against an application, unless they are
  -- convertible
  unifyApp swap mode loc env fc (NRef nt n) args tm
      = unifyIfEq True loc env (NApp fc (NRef nt n) args) tm
  unifyApp swap mode loc env xfc (NLocal rx x xp) [] (NApp yfc (NLocal ry y yp) [])
      = do gam <- get Ctxt
           if x == y then pure success
             else postponeS swap loc "Postponing var" 
                            env (NApp xfc (NLocal rx x xp) []) 
                                (NApp yfc (NLocal ry y yp) [])
  -- A local against something canonical (binder or constructor) is bad
  unifyApp swap mode loc env xfc (NLocal rx x xp) args y@(NBind _ _ _ _)
      = convertErrorS swap loc env (NApp xfc (NLocal rx x xp) args) y
  unifyApp swap mode loc env xfc (NLocal rx x xp) args y@(NDCon _ _ _ _ _)
      = convertErrorS swap loc env (NApp xfc (NLocal rx x xp) args) y
  unifyApp swap mode loc env xfc (NLocal rx x xp) args y@(NTCon _ _ _ _ _)
      = convertErrorS swap loc env (NApp xfc (NLocal rx x xp) args) y
  unifyApp swap mode loc env xfc (NLocal rx x xp) args y@(NPrimVal _ _)
      = convertErrorS swap loc env (NApp xfc (NLocal rx x xp) args) y
  unifyApp swap mode loc env xfc (NLocal rx x xp) args y@(NType _)
      = convertErrorS swap loc env (NApp xfc (NLocal rx x xp) args) y
  -- If they're already convertible without metavariables, we're done,
  -- otherwise postpone
  unifyApp swap mode loc env fc hd args tm 
      = do gam <- get Ctxt
           if !(convert gam env (NApp fc hd args) tm)
              then pure success
              else postponeS swap loc "Postponing constraint"
                             env (NApp fc hd args) tm

  doUnifyBothApps : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    {vars : _} ->
                    UnifyMode -> FC -> Env Term vars ->
                    FC -> NHead vars -> List (Closure vars) -> 
                    FC -> NHead vars -> List (Closure vars) ->
                    Core UnifyResult
  doUnifyBothApps mode loc env xfc (NLocal xr x xp) [] yfc (NLocal yr y yp) []
      = if x == y
           then pure success
           else convertError loc env (NApp xfc (NLocal xr x xp) [])
                                     (NApp yfc (NLocal yr y yp) [])
  -- Locally bound things, in a term (not LHS). Since we have to unify
  -- for *all* possible values, we can safely unify the arguments.
  doUnifyBothApps InTerm loc env xfc (NLocal xr x xp) xargs yfc (NLocal yr y yp) yargs
      = if x == y
           then unifyArgs InTerm loc env xargs yargs
           else postpone loc "Postponing local app"
                         env (NApp xfc (NLocal xr x xp) xargs)
                             (NApp yfc (NLocal yr y yp) yargs)
  doUnifyBothApps _ loc env xfc (NLocal xr x xp) xargs yfc (NLocal yr y yp) yargs
      = unifyIfEq True loc env (NApp xfc (NLocal xr x xp) xargs)
                               (NApp yfc (NLocal yr y yp) yargs)
  -- If they're both holes, solve the one with the bigger context
  doUnifyBothApps mode loc env xfc (NMeta xn xi xargs) xargs' yfc (NMeta yn yi yargs) yargs'
      = do invx <- isDefInvertible xi
           if xi == yi && (invx || mode == InSearch)
                               -- Invertible, (from auto implicit search)
                               -- so we can also unify the arguments.
              then unifyArgs mode loc env (xargs ++ xargs')
                                          (yargs ++ yargs')
              else do xlocs <- localsIn xargs
                      ylocs <- localsIn yargs
                      if xlocs >= ylocs && not (pv xn)
                        then unifyApp False mode loc env xfc (NMeta xn xi xargs) xargs'
                                            (NApp yfc (NMeta yn yi yargs) yargs')
                        else unifyApp True mode loc env yfc (NMeta yn yi yargs) yargs'
                                           (NApp xfc (NMeta xn xi xargs) xargs')
    where
      pv : Name -> Bool
      pv (PV _ _) = True
      pv _ = False

      localsIn : List (Closure vars) -> Core Nat
      localsIn [] = pure 0
      localsIn (c :: cs)
          = do defs <- get Ctxt
               case !(evalClosure defs c) of
                 NApp _ (NLocal _ _ _) _ => pure $ S !(localsIn cs)
                 _ => localsIn cs
      
  doUnifyBothApps mode loc env xfc (NMeta xn xi xargs) xargs' yfc fy yargs'
      = unifyApp False mode loc env xfc (NMeta xn xi xargs) xargs'
                                        (NApp yfc fy yargs')
  doUnifyBothApps mode loc env xfc fx xargs' yfc (NMeta yn yi yargs) yargs'
      = unifyApp True mode loc env xfc (NMeta yn yi yargs) yargs'
                                       (NApp xfc fx xargs')
  doUnifyBothApps InSearch loc env xfc fx@(NRef xt hdx) xargs yfc fy@(NRef yt hdy) yargs
      = if hdx == hdy
           then unifyArgs InSearch loc env xargs yargs
           else unifyApp False InSearch loc env xfc fx xargs (NApp yfc fy yargs)
  doUnifyBothApps mode loc env xfc fx ax yfc fy ay
      = unifyApp False mode loc env xfc fx ax (NApp yfc fy ay)

  unifyBothApps : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {vars : _} ->
                  UnifyMode -> FC -> Env Term vars ->
                  FC -> NHead vars -> List (Closure vars) -> 
                  FC -> NHead vars -> List (Closure vars) ->
                  Core UnifyResult
  unifyBothApps mode loc env xfc hx ax yfc hy ay
      = do defs <- get Ctxt
           if !(convert defs env (NApp xfc hx ax) (NApp yfc hy ay))
              then pure success
              else doUnifyBothApps mode loc env xfc hx ax yfc hy ay

  -- Comparing multiplicities when converting pi binders
  subRig : RigCount -> RigCount -> Bool
  subRig Rig1 RigW = True -- we can pass a linear function if a general one is expected
  subRig x y = x == y -- otherwise, the multiplicities need to match up

  unifyBothBinders: {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    {vars : _} ->
                    UnifyMode -> FC -> Env Term vars ->
                    FC -> Name -> Binder (NF vars) -> 
                    (Defs -> Closure vars -> Core (NF vars)) ->
                    FC -> Name -> Binder (NF vars) -> 
                    (Defs -> Closure vars -> Core (NF vars)) ->
                    Core UnifyResult
  unifyBothBinders mode loc env xfc x (Pi cx ix tx) scx yfc y (Pi cy iy ty) scy
      = do defs <- get Ctxt
           if ix /= iy || not (subRig cx cy)
             then convertError loc env 
                    (NBind xfc x (Pi cx ix tx) scx)
                    (NBind yfc y (Pi cy iy ty) scy)
             else
               do empty <- clearDefs defs
                  tx' <- quote empty env tx
                  logC 10 $ (do ty' <- quote empty env ty
                                pure ("Unifying arg types " ++ show tx' ++ " and " ++ show ty'))
                  ct <- unify mode loc env tx ty
                  xn <- genVarName "x"
                  let env' : Env Term (x :: _)
                           = Pi cx ix tx' :: env
                  case constraints ct of
                      [] => -- No constraints, check the scope
                         do tscx <- scx defs (toClosure defaultOpts env (Ref loc Bound xn))
                            tscy <- scy defs (toClosure defaultOpts env (Ref loc Bound xn))
                            tmx <- quote empty env tscx
                            tmy <- quote empty env tscy
                            unify mode loc env' (refsToLocals (Add x xn None) tmx)
                                                (refsToLocals (Add x xn None) tmy)
                      cs => -- Constraints, make new guarded constant
                         do txtm <- quote empty env tx
                            tytm <- quote empty env ty
                            c <- newConstant loc Rig0 env
                                   (Bind xfc x (Lam cx Explicit txtm) (Local xfc Nothing _ First))
                                   (Bind xfc x (Pi cx Explicit txtm)
                                       (weaken tytm)) cs
                            tscx <- scx defs (toClosure defaultOpts env (Ref loc Bound xn))
                            tscy <- scy defs (toClosure defaultOpts env (App loc c (Ref loc Bound xn)))
                            tmx <- quote empty env tscx
                            tmy <- quote empty env tscy
                            cs' <- unify mode loc env' (refsToLocals (Add x xn None) tmx)
                                                       (refsToLocals (Add x xn None) tmy)
                            pure (union ct cs')
  unifyBothBinders mode loc env xfc x (Lam cx ix tx) scx yfc y (Lam cy iy ty) scy
      = do defs <- get Ctxt
           if ix /= iy || not (subRig cx cy)
             then convertError loc env 
                    (NBind xfc x (Lam cx ix tx) scx)
                    (NBind yfc y (Lam cy iy ty) scy)
             else
               do empty <- clearDefs defs
                  tx' <- quote empty env tx
                  ct <- unify mode loc env tx ty
                  xn <- genVarName "x"
                  let env' : Env Term (x :: _)
                           = Lam cx ix tx' :: env
                  txtm <- quote empty env tx
                  tytm <- quote empty env ty

                  tscx <- scx defs (toClosure defaultOpts env (Ref loc Bound xn))
                  tscy <- scy defs (toClosure defaultOpts env (Ref loc Bound xn))
                  tmx <- quote empty env tscx
                  tmy <- quote empty env tscy
                  cs' <- unify mode loc env' (refsToLocals (Add x xn None) tmx)
                                             (refsToLocals (Add x xn None) tmy)
                  pure (union ct cs')

  unifyBothBinders mode loc env xfc x bx scx yfc y by scy
      = convertError loc env 
                  (NBind xfc x bx scx)
                  (NBind yfc y by scy)

  export
  unifyNoEta : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {vars : _} ->
               UnifyMode -> FC -> Env Term vars ->
               NF vars -> NF vars ->
               Core UnifyResult
  unifyNoEta mode loc env (NDCon xfc x tagx ax xs) (NDCon yfc y tagy ay ys)
      = do gam <- get Ctxt
           if tagx == tagy
             then unifyArgs mode loc env xs ys
             else convertError loc env 
                       (NDCon xfc x tagx ax xs)
                       (NDCon yfc y tagy ay ys)
  unifyNoEta mode loc env (NTCon xfc x tagx ax xs) (NTCon yfc y tagy ay ys)
      = if x == y
           then unifyArgs mode loc env xs ys
             -- TODO: Type constructors are not necessarily injective.
             -- If we don't know it's injective, need to postpone the
             -- constraint. But before then, we need some way to decide
             -- what's injective...
--                then postpone loc env (quote empty env (NTCon x tagx ax xs))
--                                      (quote empty env (NTCon y tagy ay ys))
           else convertError loc env 
                     (NTCon xfc x tagx ax xs)
                     (NTCon yfc y tagy ay ys)
  unifyNoEta mode loc env (NDelayed xfc _ x) (NDelayed yfc _ y)
      = unify mode loc env x y
  unifyNoEta mode loc env (NDelay xfc _ xty x) (NDelay yfc _ yty y)
      = unifyArgs mode loc env [xty, x] [yty, y]
  unifyNoEta mode loc env (NForce xfc x) (NForce yfc y)
      = unify mode loc env x y
  unifyNoEta mode loc env (NApp xfc fx axs) (NApp yfc fy ays)
      = unifyBothApps mode loc env xfc fx axs yfc fy ays
  unifyNoEta mode loc env (NApp xfc hd args) y 
      = unifyApp False mode loc env xfc hd args y
  unifyNoEta mode loc env y (NApp yfc hd args)
      = unifyApp True mode loc env yfc hd args y
  -- Only try stripping as patterns as a last resort
  unifyNoEta mode loc env x (NAs _ _ y) = unifyNoEta mode loc env x y
  unifyNoEta mode loc env (NAs _ _ x) y = unifyNoEta mode loc env x y
  unifyNoEta mode loc env x y 
      = do defs <- get Ctxt
           empty <- clearDefs defs
           unifyIfEq False loc env x y

  -- Try to get the type of the application inside the given term, to use in
  -- eta expansion. If there's no application, return Nothing
  getEtaType : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               Env Term vars -> Term vars ->
               Core (Maybe (Term vars))
  getEtaType env (Bind fc n b sc)
      = do Just ty <- getEtaType (b :: env) sc
               | Nothing => pure Nothing
           pure (shrinkTerm ty (DropCons SubRefl))
  getEtaType env (App fc f _)
      = do fty <- getType env f
           logGlue 10 "Function type" env fty
           case !(getNF fty) of
                NBind _ _ (Pi _ _ ty) sc =>
                    do defs <- get Ctxt
                       empty <- clearDefs defs
                       pure (Just !(quote empty env ty))
                _ => pure Nothing
  getEtaType env _ = pure Nothing

  isHoleApp : NF vars -> Bool
  isHoleApp (NApp _ (NMeta _ _ _) _) = True
  isHoleApp _ = False

  export
  Unify NF where
    unifyD _ _ mode loc env (NBind xfc x bx scx) (NBind yfc y by scy) 
        = unifyBothBinders mode loc env xfc x bx scx yfc y by scy
    unifyD _ _ mode loc env tmx@(NBind xfc x (Lam cx ix tx) scx) tmy
        = do defs <- get Ctxt
             logNF 10 "EtaR" env tmx
             logNF 10 "...with" env tmy
             if isHoleApp tmy
                then unifyNoEta mode loc env tmx tmy
                else do empty <- clearDefs defs
                        ety <- getEtaType env !(quote empty env tmx)
                        case ety of
                             Just argty =>
                               do etay <- nf defs env 
                                             (Bind xfc x (Lam cx ix argty)
                                                     (App xfc 
                                                          (weaken !(quote empty env tmy)) 
                                                          (Local xfc Nothing 0 First)))
                                  logNF 10 "Expand" env etay
                                  unify mode loc env tmx etay
                             _ => unifyNoEta mode loc env tmx tmy
    unifyD _ _ mode loc env tmx tmy@(NBind yfc y (Lam cy iy ty) scy)
        = do defs <- get Ctxt
             logNF 10 "EtaL" env tmx
             logNF 10 "...with" env tmy
             if isHoleApp tmx
                then unifyNoEta mode loc env tmx tmy
                else do empty <- clearDefs defs
                        ety <- getEtaType env !(quote empty env tmy)
                        case ety of
                             Just argty =>
                               do etax <- nf defs env 
                                             (Bind yfc y (Lam cy iy argty)
                                                     (App yfc 
                                                          (weaken !(quote empty env tmx)) 
                                                          (Local yfc Nothing 0 First)))
                                  logNF 10 "Expand" env etax
                                  unify mode loc env etax tmy
                             _ => unifyNoEta mode loc env tmx tmy
    unifyD _ _ mode loc env tmx tmy = unifyNoEta mode loc env tmx tmy

    unifyWithLazyD _ _ mode loc env (NDelayed _ _ tmx) (NDelayed _ _ tmy)
       = unify mode loc env tmx tmy
    unifyWithLazyD _ _ mode loc env (NDelayed _ r tmx) tmy
       = do vs <- unify mode loc env tmx tmy
            pure (record { addLazy = AddForce } vs)
    unifyWithLazyD _ _ mode loc env tmx (NDelayed _ r tmy)
       = do vs <- unify mode loc env tmx tmy
            pure (record { addLazy = AddDelay r } vs)
    unifyWithLazyD _ _ mode loc env tmx tmy
       = unify mode loc env tmx tmy

  export
  Unify Term where
    unifyD _ _ mode loc env x y 
          = do defs <- get Ctxt
               if x == y
                  then do log 10 $ "Skipped unification (equal already): "
                                 ++ show x ++ " and " ++ show y
                          pure success
                  else unify mode loc env !(nf defs env x) !(nf defs env y)
    unifyWithLazyD _ _ mode loc env x y 
          = do defs <- get Ctxt
               if x == y
                  then do log 10 $ "Skipped unification (equal already): "
                                 ++ show x ++ " and " ++ show y
                          pure success
                  else unifyWithLazy mode loc env !(nf defs env x) !(nf defs env y)

  export
  Unify Closure where
    unifyD _ _ mode loc env x y 
        = do defs <- get Ctxt
             unify mode loc env !(evalClosure defs x) !(evalClosure defs y)

export
setInvertible : {auto c : Ref Ctxt Defs} ->
                FC -> Int -> Core ()
setInvertible loc i
    = updateDef (Resolved i)
           (\old => case old of
                         Hole locs _ => Just (Hole locs True)
                         _ => Nothing)

public export
data SolveMode = Normal -- during elaboration: unifies and searches
               | Defaults -- unifies and searches for default hints only
               | LastChance -- as normal, but any failure throws rather than delays

Eq SolveMode where
  Normal == Normal = True
  Defaults == Defaults = True
  LastChance == LastChance = True
  _ == _ = False

retry : {auto c : Ref Ctxt Defs} ->
        {auto u : Ref UST UState} ->
        UnifyMode -> Int -> Core UnifyResult
retry mode c
    = do ust <- get UST
         case lookup c (constraints ust) of
              Nothing => pure success
              Just Resolved => pure success
              Just (MkConstraint loc env x y)
                  => catch (do logTerm 5 "Retrying" x 
                               logTerm 5 "....with" y
                               cs <- unify mode loc env x y 
                               case constraints cs of
                                 [] => do deleteConstraint c
                                          pure success
                                 _ => pure cs)
                       (\err => throw (WhenUnifying loc env x y err)) 
              Just (MkSeqConstraint loc env xs ys)
                  => do cs <- unifyArgs mode loc env xs ys
                        case constraints cs of
                             [] => do deleteConstraint c 
                                      pure success
                             _ => pure cs

-- Retry the given constraint, return True if progress was made
retryGuess : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             UnifyMode -> (smode : SolveMode) -> (hole : (Int, (FC, Name))) ->
             Core Bool
retryGuess mode smode (hid, (loc, hname))
    = do defs <- get Ctxt
         case !(lookupCtxtExact (Resolved hid) (gamma defs)) of
           Nothing => pure False
           Just def =>
             case definition def of
               BySearch rig depth defining =>
                 handleUnify
                   (do tm <- search loc rig (smode == Defaults) depth defining
                                    (type def) []
                       let gdef = record { definition = PMDef [] (STerm tm) (STerm tm) [] } def
                       logTerm 5 ("Solved " ++ show hname) tm
                       addDef (Resolved hid) gdef
                       removeGuess hid
                       pure True)
                   (\err => case err of
                              DeterminingArg _ n i _ _ => 
                                  do logTerm 5 ("Failed (det " ++ show hname ++ ")")
                                               (type def)
                                     setInvertible loc i
                                     pure False -- progress made!
                              _ => do logTerm 5 ("Search failed for " ++ show hname) 
                                                (type def)
                                      case smode of
                                           LastChance => throw err
                                           _ => pure False) -- Postpone again
               Guess tm constrs => 
                 do cs' <- traverse (retry mode) constrs
                    let csAll = unionAll cs'
                    case constraints csAll of
                         -- All constraints resolved, so turn into a
                         -- proper definition and remove it from the
                         -- hole list
                         [] => do let gdef = record { definition = PMDef [] (STerm tm) (STerm tm) [] } def
                                  logTerm 5 ("Resolved " ++ show hname) tm
                                  addDef (Resolved hid) gdef
                                  removeGuess hid
                                  pure (holesSolved csAll)
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
         progress <- traverse (retryGuess umode smode) (toList (guesses ust))
         when (or (map Delay progress)) $ solveConstraints umode smode

-- Replace any 'BySearch' with 'Hole', so that we don't keep searching 
-- fruitlessly while elaborating the rest of a source file
export
giveUpSearch : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               Core ()
giveUpSearch
    = do ust <- get UST
         traverse_ searchToHole (toList (guesses ust))
  where
    searchToHole : (Int, (FC, Name)) -> Core ()
    searchToHole (hid, (_, _))
        = do defs <- get Ctxt
             case !(lookupDefExact (Resolved hid) (gamma defs)) of
                  Just (BySearch _ _ _) =>
                         updateDef (Resolved hid) (const (Just (Hole 0 False)))
                  _ => pure ()


export
checkDots : {auto u : Ref UST UState} ->
            {auto c : Ref Ctxt Defs} ->
            Core ()
checkDots
    = do ust <- get UST
         hs <- getCurrentHoles
         traverse_ checkConstraint (reverse (dotConstraints ust))
         hs <- getCurrentHoles
         ust <- get UST
         put UST (record { dotConstraints = [] } ust)
  where
    checkConstraint : (Name, String, Constraint) -> Core ()
    checkConstraint (n, reason, MkConstraint fc env x y)
        = do logTermNF 10 "Dot" env y
             logTermNF 10 "  =" env x
             catch
               (do cs <- unify InTerm fc env x y
                   defs <- get Ctxt
                   Just ndef <- lookupDefExact n (gamma defs)
                        | Nothing => throw (UndefinedName fc n)
                   let h = case ndef of
                                Hole _ _ => True
                                _ => False
                   
                   when (not (isNil (constraints cs)) || h) $
                      throw (InternalError "Dot pattern match fail"))
               (\err => do defs <- get Ctxt
                           throw (BadDotPattern fc env reason 
                                   !(normaliseHoles defs env x) 
                                   !(normaliseHoles defs env y)))
    checkConstraint _ = pure ()


