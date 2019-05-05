module Core.Unify

import Core.CaseTree
import Core.Context
import Core.Core
import Core.Env
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
               | InDot
               | InSearch

Eq UnifyMode where
   InLHS == InLHS = True
   InTerm == InTerm = True
   InDot == InDot = True
   InSearch == InSearch = True
   _ == _ = False

public export
record UnifyResult where
  constructor MkUnifyResult
  constraints : List Int
  holesSolved : Bool

union : UnifyResult -> UnifyResult -> UnifyResult
union u1 u2 = MkUnifyResult (union (constraints u1) (constraints u2))
                            (holesSolved u1 || holesSolved u2)

unionAll : List UnifyResult -> UnifyResult
unionAll [] = MkUnifyResult [] False
unionAll [c] = c
unionAll (c :: cs) = union c (unionAll cs)

constrain : Int -> UnifyResult
constrain c = MkUnifyResult [c] False

success : UnifyResult
success = MkUnifyResult [] False

solvedHole : UnifyResult
solvedHole = MkUnifyResult [] True

public export
interface Unify (tm : List Name -> Type) where
  -- Unify returns a list of ids referring to newly added constraints
  unifyD : Ref Ctxt Defs ->
           Ref UST UState ->
           UnifyMode ->
           FC -> Env Term vars ->
           tm vars -> tm vars -> 
           Core UnifyResult

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
getVars : List (NF vars) -> Maybe (List (Var vars))
getVars [] = Just []
getVars (NApp fc (NLocal r idx v) [] :: xs) 
    = if vIn xs then Nothing
         else do xs' <- getVars xs
                 pure (MkVar v :: xs')
  where
    -- Check the variable doesn't appear later
    vIn : List (NF vars) -> Bool
    vIn [] = False
    vIn (NApp _ (NLocal r idx' el') [] :: xs)
        = if idx == idx' then True else vIn xs
    vIn (_ :: xs) = vIn xs
getVars (_ :: xs) = Nothing

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

    dropFirst : List (Var (n :: ns)) -> List (Var ns) 
    dropFirst [] = []
    dropFirst (MkVar First :: xs) = dropFirst xs
    dropFirst (MkVar (Later p) :: xs) = MkVar p :: dropFirst xs

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
             Core (Maybe (newvars ** (List (Var newvars),
                                     SubVars newvars vars)))
patternEnv env args
    = do defs <- get Ctxt
         empty <- clearDefs defs
         args' <- traverse (evalClosure empty) args
         case getVars args' of
              Nothing => pure Nothing
              Just vs => 
                 let (newvars ** svs) = toSubVars _ vs in
                     pure (Just (newvars ** (updateVars vs svs, svs)))
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
instantiate : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {newvars : _} ->
              FC -> Env Term vars -> 
              (metavar : Name) -> (mref : Int) -> (mdef : GlobalDef) ->
              List (Var newvars) -> -- Variable each argument maps to
              Term vars -> -- original, just for error message
              Term newvars -> -- shrunk environment
              Core ()
instantiate {newvars} loc env mname mref mdef locs otm tm
    = do log 5 $ "Instantiating " ++ show tm ++ " in " ++ show newvars 
         let ty = type mdef
         case mkDef [] newvars (snocList newvars) CompatPre
                     (rewrite appendNilRightNeutral newvars in locs)
                     (rewrite appendNilRightNeutral newvars in tm) ty of
               Nothing => ufail loc $ "Can't make solution for " ++ show mname
               Just rhs =>
                  do logTerm 5 ("Instantiated: " ++ show mname) ty
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

    updateLocs locs (App fc f i a)
        = Just (App fc !(updateLocs locs f) i !(updateLocs locs a))
    updateLocs locs tm = Just tm

    mkDef : (got : List Name) -> (vs : List Name) -> SnocList vs ->
            CompatibleVars got rest ->
            List (Var (vs ++ got)) -> Term (vs ++ got) -> 
            Term rest -> Maybe (Term rest)
    mkDef got [] Empty cvs locs tm ty 
        = do tm' <- updateLocs (reverse locs) tm
             pure (renameVars cvs tm')
    mkDef got (vs ++ [v]) (Snoc rec) cvs locs tm (Bind bfc x (Pi c _ ty) sc) 
        = do sc' <- mkDef (v :: got) vs rec (CompatExt cvs)
                       (rewrite appendAssociative vs [v] got in locs)
                       (rewrite appendAssociative vs [v] got in tm)
                       sc
             pure (Bind bfc x (Lam c Explicit (Erased bfc)) sc')
    mkDef got (vs ++ [v]) (Snoc rec) cvs locs tm ty = Nothing
    

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
  
  unifyPatVar : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {vars : _} ->
                UnifyMode -> FC -> Env Term vars ->
                (metaname : Name) -> (metaref : Int) ->
                (args : List (AppInfo, Closure vars)) ->
                (soln : NF vars) ->
                Core UnifyResult
  -- TODO: if either side is a pattern variable application, and we're in a term,
  -- (which will be a type) we can proceed because the pattern variable
  -- has to end up pi bound. Unify the right most variables, and continue.
  unifyPatVar mode loc env mname mref args tm
      = postpone loc "Not in pattern fragment" env 
                 (NApp loc (NMeta mname mref args) []) tm

  solveHole : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars : _} ->
              FC -> Env Term vars ->
              (metaname : Name) -> (metaref : Int) ->
              (margs : List (AppInfo, Closure vars)) ->
              (margs' : List (AppInfo, Closure vars)) ->
              List (Var newvars) ->
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
           if !(convert empty env (NApp loc (NMeta mname mref margs) margs')
                                  solnf)
              then pure success
              else -- TODO: Occurs check
                   do Just hdef <- lookupCtxtExact (Resolved mref) (gamma defs)
                           | Nothing => throw (InternalError ("Can't happen: Lost hole " ++ show mname))
                      instantiate loc env mname mref hdef locs solfull stm
                      pure solvedHole

  unifyHole : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars : _} ->
              UnifyMode -> FC -> Env Term vars ->
              FC -> (metaname : Name) -> (metaref : Int) ->
              (args : List (AppInfo, Closure vars)) ->
              (args' : List (AppInfo, Closure vars)) ->
              (soln : NF vars) ->
              Core UnifyResult
  unifyHole mode loc env fc mname mref margs margs' tmnf
      = do defs <- get Ctxt
           empty <- clearDefs defs
           let args = margs ++ margs'
           logC 10 (do args' <- traverse (evalClosure empty) (map snd args)
                       qargs <- traverse (quote empty env) args'
                       qtm <- quote empty env tmnf
                       pure $ "Unifying: " ++ show mname ++ " " ++ show qargs ++
                              " with " ++ show qtm)
           case !(patternEnv env (map snd args)) of
                Nothing => unifyPatVar mode loc env mname mref args tmnf
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
             NHead vars -> List (AppInfo, Closure vars) -> NF vars ->
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
                    FC -> NHead vars -> List (AppInfo, Closure vars) -> 
                    FC -> NHead vars -> List (AppInfo, Closure vars) ->
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
           then unifyArgs InTerm loc env (map snd xargs) (map snd yargs)
           else postpone loc "Postponing local app"
                         env (NApp xfc (NLocal xr x xp) xargs)
                             (NApp yfc (NLocal yr y yp) yargs)
  doUnifyBothApps _ loc env xfc (NLocal xr x xp) xargs yfc (NLocal yr y yp) yargs
      = unifyIfEq True loc env (NApp xfc (NLocal xr x xp) xargs)
                               (NApp yfc (NLocal yr y yp) yargs)
  -- If they're both holes, solve the one with the bigger context
  doUnifyBothApps mode loc env xfc (NMeta xn xi xargs) xargs' yfc (NMeta yn yi yargs) yargs'
      = if xi == yi && False -- ahem. If it's invertible (TODO!)
           then unifyArgs mode loc env (map snd (xargs ++ xargs'))
                                       (map snd (yargs ++ yargs'))
           else if length xargs >= length yargs
                   then unifyApp False mode loc env xfc (NMeta xn xi xargs) xargs'
                                       (NApp yfc (NMeta yn yi yargs) yargs')
                   else unifyApp False mode loc env yfc (NMeta yn yi yargs) yargs'
                                       (NApp xfc (NMeta xn xi xargs) xargs')
  doUnifyBothApps mode loc env xfc fx ax yfc fy ay
      = unifyApp False mode loc env xfc fx ax (NApp yfc fy ay)

  unifyBothApps : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {vars : _} ->
                  UnifyMode -> FC -> Env Term vars ->
                  FC -> NHead vars -> List (AppInfo, Closure vars) -> 
                  FC -> NHead vars -> List (AppInfo, Closure vars) ->
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
                            tscy <- scy defs (toClosure defaultOpts env (App loc c (explApp Nothing) (Ref loc Bound xn)))
                            tmx <- quote empty env tscx
                            tmy <- quote empty env tscy
                            cs' <- unify mode loc env' (refsToLocals (Add x xn None) tmx)
                                                       (refsToLocals (Add x xn None) tmy)
                            pure (union ct cs')

  unifyBothBinders mode loc env xfc x bx scx yfc y by scy
      = convertError loc env 
                  (NBind xfc x bx scx)
                  (NBind yfc y by scy)


  unifyNoEta : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {vars : _} ->
               UnifyMode -> FC -> Env Term vars ->
               NF vars -> NF vars ->
               Core UnifyResult
  unifyNoEta mode loc env (NDCon xfc x tagx ax xs) (NDCon yfc y tagy ay ys)
      = do gam <- get Ctxt
           if tagx == tagy
             then unifyArgs mode loc env (map snd xs) (map snd ys)
             else convertError loc env 
                       (NDCon xfc x tagx ax xs)
                       (NDCon yfc y tagy ay ys)
  unifyNoEta mode loc env (NTCon xfc x tagx ax xs) (NTCon yfc y tagy ay ys)
      = if x == y
           then unifyArgs mode loc env (map snd xs) (map snd ys)
             -- TODO: Type constructors are not necessarily injective.
             -- If we don't know it's injective, need to postpone the
             -- constraint. But before then, we need some way to decide
             -- what's injective...
--                then postpone loc env (quote empty env (NTCon x tagx ax xs))
--                                      (quote empty env (NTCon y tagy ay ys))
           else convertError loc env 
                     (NTCon xfc x tagx ax xs)
                     (NTCon yfc y tagy ay ys)

  unifyNoEta mode loc env (NApp xfc fx axs) (NApp yfc fy ays)
      = unifyBothApps mode loc env xfc fx axs yfc fy ays
  unifyNoEta mode loc env (NApp xfc hd args) y 
      = unifyApp False mode loc env xfc hd args y
  unifyNoEta mode loc env y (NApp yfc hd args)
      = unifyApp True mode loc env yfc hd args y
  unifyNoEta mode loc env x y 
      = do defs <- get Ctxt
           empty <- clearDefs defs
           unifyIfEq False loc env x y

  export
  Unify NF where
    -- TODO: Eta!
    unifyD _ _ mode loc env (NBind xfc x bx scx) (NBind yfc y by scy) 
        = unifyBothBinders mode loc env xfc x bx scx yfc y by scy
    unifyD _ _ mode loc env tmx tmy = unifyNoEta mode loc env tmx tmy

  export
  Unify Term where
    unifyD _ _ mode loc env x y 
          = do defs <- get Ctxt
               if !(convert defs env x y)
                  then do log 10 $ "Skipped unification (convert already): "
                                 ++ show x ++ " and " ++ show y
                          pure success
                  else unify mode loc env !(nf defs env x) !(nf defs env y)

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
                  => catch (do log 5 $ "Retrying " ++ show x ++ " and " ++ show y
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
                              DeterminingArg _ n i _ _ => ?setInvertible
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

