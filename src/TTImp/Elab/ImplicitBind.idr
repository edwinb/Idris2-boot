module TTImp.Elab.ImplicitBind
-- Machinery needed for handling implicit name bindings (either pattern
-- variables or unbound implicits as type variables)

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.TTImp

import Data.NameMap

%default covering

varEmbedSub : SubVars small vars -> IsVar n idx small -> 
              (idx' ** IsVar n idx' vars)
varEmbedSub SubRefl y = (_ ** y)
varEmbedSub (DropCons prf) y 
    = let (_ ** y') = varEmbedSub prf y in
          (_ ** Later y')
varEmbedSub (KeepCons prf) First = (_ ** First)
varEmbedSub (KeepCons prf) (Later p)
    = let (_ ** p') = varEmbedSub prf p in
          (_ ** Later p')

embedVar : SubVars small vars -> Var small -> Var vars
embedVar sub (MkVar x) = let (_ ** x') = varEmbedSub sub x in MkVar x'

mutual
  embedSub : SubVars small vars -> Term small -> Term vars
  embedSub sub (Local fc x idx y) 
      = let (_ ** y') = varEmbedSub sub y in Local fc x _ y'
  embedSub sub (Ref fc x name) = Ref fc x name
  embedSub sub (Meta fc x y xs) 
      = Meta fc x y (map (embedSub sub) xs)
  embedSub sub (Bind fc x b scope) 
      = Bind fc x (map (embedSub sub) b) (embedSub (KeepCons sub) scope)
  embedSub sub (App fc fn p arg) 
      = App fc (embedSub sub fn) p (embedSub sub arg)
  embedSub sub (Case fc cs ty tree alts) 
      = Case fc (map (embedVar sub) cs) (embedSub sub ty)
                (map (embedTree sub) tree) (map (embedPatAlt sub) alts)
  embedSub sub (As fc idx x y) 
      = let (_ ** x') = varEmbedSub sub x in
            As fc _ x' (embedSub sub y)
  embedSub sub (TDelayed fc x y) = TDelayed fc x (embedSub sub y)
  embedSub sub (TDelay fc x y) = TDelay fc x (embedSub sub y)
  embedSub sub (TForce fc x) = TForce fc (embedSub sub x)
  embedSub sub (PrimVal fc c) = PrimVal fc c
  embedSub sub (Erased fc) = Erased fc
  embedSub sub (TType fc) = TType fc

  embedTree : SubVars small vars -> CaseTree small -> CaseTree vars
  embedTree sub (Switch idx x scTy xs) 
      = let (_ ** x') = varEmbedSub sub x in
            Switch _ x' (embedSub sub scTy) (map (embedCaseAlt sub) xs)
  embedTree sub (STerm x) = STerm (embedSub sub x)
  embedTree sub (Unmatched msg) = Unmatched msg
  embedTree sub Impossible = Impossible

  embedCaseAlt : SubVars small vars -> CaseAlt small -> CaseAlt vars
  embedCaseAlt sub (ConCase x tag args t) 
      = ConCase x tag args (embedTree (subExtend args sub) t)
  embedCaseAlt sub (ConstCase x t) = ConstCase x (embedTree sub t)
  embedCaseAlt sub (DefaultCase t) = DefaultCase (embedTree sub t)

  embedPat : SubVars small vars -> Pat small -> Pat vars
  embedPat sub (PAs fc idx x y) 
      = let (_ ** x') = varEmbedSub sub x in
            PAs fc _ x' (embedPat sub y)
  embedPat sub (PCon fc x tag arity xs) 
      = PCon fc x tag arity (map (embedPat sub) xs)
  embedPat sub (PLoc fc idx x) 
      = let (_ ** x') = varEmbedSub sub x in
            PLoc fc _ x'
  embedPat sub (PUnmatchable fc x) = PUnmatchable fc (embedSub sub x)

  embedPatAlt : SubVars small vars -> PatAlt small -> PatAlt vars
  embedPatAlt sub (CBind c n ty alt) 
      = CBind c n (embedSub sub ty) (embedPatAlt (KeepCons sub) alt)
  embedPatAlt sub (CPats xs rhs) 
      = CPats (map (embedPat sub) xs) (embedSub sub rhs)


-- Make a hole for an unbound implicit in the outer environment
export
mkOuterHole : {auto e : Ref EST (EState vars)} ->
              {auto c : Ref Ctxt Defs} ->
              {auto e : Ref UST UState} ->
              FC -> RigCount ->
              Name -> Env Term vars -> Maybe (Glued vars) ->
              Core (Term vars, Term vars)
mkOuterHole loc rig n topenv (Just expty_in)
    = do est <- get EST
         let sub = subEnv est
         expected <- getTerm expty_in
         case shrinkTerm expected sub of
              -- Can't shrink so rely on unification with expected type later
              Nothing => mkOuterHole loc rig n topenv Nothing
              Just exp' => 
                  do let env = outerEnv est
                     tm <- metaVar loc rig env n exp'
                     pure (embedSub sub tm, embedSub sub exp')
mkOuterHole loc rig n topenv Nothing
    = do est <- get EST
         let sub = subEnv est
         let env = outerEnv est
         nm <- genName "impty"
         ty <- metaVar loc Rig0 env nm (TType loc)
         put EST (addBindIfUnsolved nm rig topenv (embedSub sub ty) (TType loc) est)
         tm <- metaVar loc rig env n ty
         pure (embedSub sub tm, embedSub sub ty)

-- Make a hole standing for the pattern variable, which we'll instantiate
-- with a bound pattern variable later.
-- Returns the hole term, its expected type (this is the type we'll use when
-- we see the name later) and the type the binder will need to be when we
-- instantiate it.
export
mkPatternHole : {auto e : Ref EST (EState vars)} ->
                {auto c : Ref Ctxt Defs} ->
                {auto e : Ref UST UState} ->
                FC -> RigCount -> Name -> Env Term vars -> BindMode ->
                Maybe (Glued vars) ->
                Core (Term vars, Term vars, Term vars)
mkPatternHole loc rig n env (PI _) exp
    = do (tm, exp) <- mkOuterHole loc rig n env exp
         pure (tm, exp, exp)
mkPatternHole {vars} loc rig n topenv imode (Just expty_in)
    = do est <- get EST
         let sub = subEnv est
         let env = outerEnv est
         expected <- getTerm expty_in
         case bindInner topenv expected sub of
              Nothing => mkPatternHole loc rig n topenv imode Nothing
              Just exp' =>
                  do tm <- metaVar loc rig env n exp'
                     pure (apply loc (explApp Nothing)
                                 (embedSub sub tm) (mkArgs sub), 
                           expected,
                           embedSub sub exp')
  where
    mkArgs : SubVars newvars vs -> List (Term vs)
    mkArgs SubRefl = []
    mkArgs (DropCons p) = Local loc Nothing 0 First :: map weaken (mkArgs p)
    mkArgs _ = []

    -- This is for the specific situation where we're pattern matching on
    -- function types, which is realistically the only time we'll legitimately
    -- encounter a type variable under a binder
    bindInner : Env Term vs -> Term vs -> SubVars newvars vs -> 
                Maybe (Term newvars)
    bindInner env ty SubRefl = Just ty
    bindInner {vs = x :: _} (b :: env) ty (DropCons p)
        = bindInner env (Bind loc x b ty) p
    bindInner _ _ _ = Nothing

mkPatternHole loc rig n env _ _
    = throw (GenericMsg loc ("Unknown type for pattern variable " ++ show n))

-- For any of the 'bindIfUnsolved' - these were added as holes during
-- elaboration, but are as yet unsolved, so create a pattern variable for
-- them and unify.
-- (This is only when we're in a mode that allows unbound implicits)
bindUnsolved : {auto c : Ref Ctxt Defs} -> {auto e : Ref EST (EState vars)} ->
               {auto u : Ref UST UState} ->
               FC -> ElabMode -> BindMode -> Core ()
bindUnsolved fc elabmode NONE = pure ()
bindUnsolved {vars} fc elabmode _ 
    = do est <- get EST
         defs <- get Ctxt
         let bifs = bindIfUnsolved est
         log 10 $ "Bindable unsolved implicits: " ++ show (map fst bifs)
         traverse (mkImplicit defs (outerEnv est) (subEnv est)) (bindIfUnsolved est)
         pure ()
  where
    makeBoundVar : Name -> RigCount -> Env Term outer ->
                   SubVars outer vs -> SubVars outer vars ->
                   Term vs -> Core (Term vs)
    makeBoundVar n rig env sub subvars expected
        = case shrinkTerm expected sub of
               Nothing => do tmn <- toFullNames expected
                             throw (GenericMsg fc ("Can't bind implicit of type " ++ show tmn))
               Just exp' => 
                    do impn <- genName (nameRoot n)
                       tm <- metaVar fc rig env impn exp'
                       est <- get EST
                       put EST (record { toBind $= ((impn, (embedSub subvars tm, 
                                                            embedSub subvars exp')) ::) } est)
                       pure (embedSub sub tm)

    mkImplicit : Defs -> Env Term outer -> SubVars outer vars ->
                 (Name, RigCount, (vars' ** 
                     (Env Term vars', Term vars', Term vars', SubVars outer vars'))) -> 
                 Core ()
    mkImplicit defs outerEnv subEnv (n, rig, (vs ** (env, tm, exp, sub)))
        = do Just (Hole _) <- lookupDefExact n (gamma defs)
                  | _ => pure ()
             bindtm <- makeBoundVar n rig outerEnv
                                    sub subEnv
                                    !(normaliseHoles defs env exp)
             logTerm 5 ("Added unbound implicit") bindtm
             unify (case elabmode of
                         InLHS _ => InLHS
                         _ => InTerm)
                   fc env tm bindtm
             pure ()

swapIsVarH : IsVar name idx (x :: y :: xs) -> 
             (idx' ** IsVar name idx' (y :: x :: xs))
swapIsVarH First = (_ ** Later First)
swapIsVarH (Later First) = (_ ** First)
swapIsVarH (Later (Later x)) = (_ ** Later (Later x))

swapIsVar : (vs : List Name) ->
            IsVar name idx (vs ++ x :: y :: xs) -> 
            (idx' ** IsVar name idx' (vs ++ y :: x :: xs))
swapIsVar [] prf = swapIsVarH prf
swapIsVar (x :: xs) First = (_ ** First)
swapIsVar (x :: xs) (Later p) 
    = let (_ ** p') = swapIsVar xs p in (_ ** Later p')

mutual
  swapVars : {vs : List Name} ->
             Term (vs ++ x :: y :: ys) -> Term (vs ++ y :: x :: ys)
  swapVars (Local fc x idx p) 
      = let (_ ** p') = swapIsVar _ p in Local fc x _ p'
  swapVars (Ref fc x name) = Ref fc x name
  swapVars (Meta fc n i xs) = Meta fc n i (map swapVars xs)
  swapVars {vs} (Bind fc x b scope) 
      = Bind fc x (map swapVars b) (swapVars {vs = x :: vs} scope)
  swapVars (App fc fn p arg) = App fc (swapVars fn) p (swapVars arg)
  swapVars (Case fc cs ty tree alts) 
      = Case fc (map swapInVar cs) (swapVars ty) 
                (map swapTree tree) (map swapPatAlt alts)
    where
      swapInVar : Var (vs ++ x :: y :: ys) -> Var (vs ++ y :: x :: ys)
      swapInVar (MkVar p) = let (_ ** p') = swapIsVar _ p in MkVar p'
  swapVars (As fc idx p tm) 
      = let (_ ** p') = swapIsVar _ p in As fc _ p' (swapVars tm)
  swapVars (TDelayed fc x tm) = TDelayed fc x (swapVars tm)
  swapVars (TDelay fc x tm) = TDelay fc x (swapVars tm)
  swapVars (TForce fc tm) = TForce fc (swapVars tm)
  swapVars (PrimVal fc c) = PrimVal fc c
  swapVars (Erased fc) = Erased fc
  swapVars (TType fc) = TType fc

  swapTree : {vs : List Name} ->
             CaseTree (vs ++ x :: y :: ys) -> CaseTree (vs ++ y :: x :: ys)
  swapTree (Switch idx p scTy xs) 
      = let (_ ** p') = swapIsVar _ p in
            Switch _ p' (swapVars scTy) (map swapCaseAlt xs)
  swapTree (STerm x) = STerm (swapVars x)
  swapTree (Unmatched msg) = Unmatched msg
  swapTree Impossible = Impossible

  swapCaseAlt : {vs : List Name} ->
                CaseAlt (vs ++ x :: y :: ys) -> CaseAlt (vs ++ y :: x :: ys)
  swapCaseAlt {vs} {x} {y} {ys} (ConCase n tag args t) 
      = let t' = swapTree {vs = args ++ vs} {x} {y} {ys} 
                  (rewrite sym (appendAssociative args vs (x :: y :: ys)) in t)
                     in
            ConCase x tag args 
                (rewrite appendAssociative args vs (y :: x :: ys) in t')
  swapCaseAlt (ConstCase c t) = ConstCase c (swapTree t)
  swapCaseAlt (DefaultCase t) = DefaultCase (swapTree t)

  swapPatAlt : {vs : List Name} ->
               PatAlt (vs ++ x :: y :: ys) -> PatAlt (vs ++ y :: x :: ys)
  swapPatAlt {vs} (CBind c x ty alt) 
      = CBind c x (swapVars ty) (swapPatAlt {vs = x :: vs} alt)
  swapPatAlt (CPats xs rhs) = CPats (map swapPat xs) (swapVars rhs)

  swapPat : {vs : List Name} ->
            Pat (vs ++ x :: y :: ys) -> Pat (vs ++ y :: x :: ys)
  swapPat (PAs fc idx p pat) 
      = let (_ ** p') = swapIsVar _ p in PAs fc _ p' (swapPat pat)
  swapPat (PCon fc x tag arity xs) 
      = PCon fc x tag arity (map swapPat xs)
  swapPat (PLoc fc idx p) 
      = let (_ ** p') = swapIsVar _ p in PLoc fc _ p'
  swapPat (PUnmatchable fc x) = PUnmatchable fc (swapVars x)

-- Push an explicit pi binder as far into a term as it'll go. That is,
-- move it under implicit binders that don't depend on it, and stop
-- when hitting any non-implicit binder
push : FC -> (n : Name) -> Binder (Term vs) -> Term (n :: vs) -> Term vs
push ofc n b tm@(Bind fc (PV x i) (Pi c Implicit ty) sc) -- only push past 'PV's
    = case shrinkTerm ty (DropCons SubRefl) of
           Nothing => -- needs explicit pi, do nothing
                      Bind ofc n b tm
           Just ty' => Bind fc (PV x i) (Pi c Implicit ty') 
                            (push ofc n (map weaken b) (swapVars {vs = []} sc))
push ofc n b tm = Bind ofc n b tm

-- Move any implicit arguments as far to the left as possible - this helps
-- with curried applications
-- We only do this for variables named 'PV', since they are the unbound
-- implicits, and we don't want to move any given by the programmer
liftImps : BindMode -> (Term vars, Term vars) -> (Term vars, Term vars)
liftImps (PI _) (tm, TType) = (liftImps' tm, TType)
  where
    liftImps' : Term vars -> Term vars
    liftImps' (Bind fc (PV n i) (Pi c Implicit ty) sc) 
        = Bind fc (PV n i) (Pi c Implicit ty) (liftImps' sc)
    liftImps' (Bind fc n (Pi c p ty) sc)
        = push fc n (Pi c p ty) (liftImps' sc)
    liftImps' tm = tm
liftImps _ x = x

-- Bind implicit arguments, returning the new term and its updated type
bindImplVars : FC -> BindMode ->
               Defs ->
               Env Term vars ->
               List (Name, Term vars) ->
               Term vars -> Term vars -> (Term vars, Term vars)
bindImplVars fc NONE gam env imps_in scope scty = (scope, scty)
bindImplVars {vars} fc mode gam env imps_in scope scty 
    = let imps = map (\ (x, ty) => (dropNS x, x, ty)) imps_in in
          getBinds imps None scope scty
  where
    getBinds : (imps : List (Name, Name, Term vs)) -> 
               Bounds new -> (tm : Term vs) -> (ty : Term vs) ->
               (Term (new ++ vs), Term (new ++ vs))
    getBinds [] bs tm ty = (refsToLocals bs tm, refsToLocals bs ty)
    getBinds ((n, metan, bty) :: imps) bs tm ty
        = let (tm', ty') = getBinds imps (Add n metan bs) tm ty 
              bty' = refsToLocals bs bty in
              case mode of
                   PI c =>
                      (Bind fc _ (Pi c Implicit bty') tm', 
                       TType fc)
                   _ =>
                      (Bind fc _ (PVar RigW bty') tm', 
                       Bind fc _ (PVTy RigW bty') ty')

normaliseHolesScope : Defs -> Env Term vars -> Term vars -> Core (Term vars)
normaliseHolesScope defs env (Bind fc n b sc) 
    = pure $ Bind fc n b 
                  !(normaliseHolesScope defs 
                   -- use Lam because we don't want it reducing in the scope
                   (Lam (multiplicity b) Explicit (binderType b) :: env) sc)
normaliseHolesScope defs env tm = normaliseHoles defs env tm

export
bindImplicits : FC -> BindMode ->
                Defs -> Env Term vars ->
                List (Name, Term vars) ->
                Term vars -> Term vars -> Core (Term vars, Term vars)
bindImplicits fc NONE defs env hs tm ty = pure (tm, ty)
bindImplicits {vars} fc mode defs env hs tm ty 
   = do hs' <- traverse nHoles hs
        pure $ liftImps mode $ bindImplVars fc mode defs env hs' tm ty
  where
    nHoles : (Name, Term vars) -> Core (Name, Term vars)
    nHoles (n, ty) = pure (n, !(normaliseHolesScope defs env ty))

export
implicitBind : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               Name -> Core ()
implicitBind n 
    = do defs <- get Ctxt
         Just (Hole _) <- lookupDefExact n (gamma defs)
             | _ => pure ()
         updateDef n (const (Just ImpBind))

-- 'toBind' are the names which are to be implicitly bound (pattern bindings and
-- unbound implicits).
-- Return the names in the order they should be bound: i.e. respecting
-- dependencies between types, and putting @-patterns last because their
-- value is determined from the patterns
export
getToBind : {auto c : Ref Ctxt Defs} -> {auto e : Ref EST (EState vars)} ->
            {auto u : Ref UST UState} ->
            FC -> ElabMode -> BindMode ->
            Env Term vars -> (excepts : List Name) -> Term vars ->
            Core (List (Name, Term vars))
getToBind fc elabmode NONE env excepts toptom
    = pure [] -- We should probably never get here, but for completeness...
getToBind {vars} fc elabmode impmode env excepts toptm
    = do solveConstraints (case elabmode of
                                InLHS _ => InLHS
                                _ => InTerm) Normal
         bindUnsolved fc elabmode impmode
         solveConstraints (case elabmode of
                                InLHS _ => InLHS
                                _ => InTerm) Normal
         defs <- get Ctxt
         est <- get EST
         let tob = reverse $ filter (\x => not (fst x `elem` excepts)) $
                             toBind est
         -- Make sure all the hole names are normalised in the implicitly
         -- bound types, because otherwise we'll bind them too
         res <- normImps defs [] tob
         let hnames = map fst res 
         -- Return then in dependency order
         pure (depSort hnames res)
  where
    normImps : Defs -> List Name -> List (Name, Term vars, Term vars) -> 
               Core (List (Name, Term vars))
    normImps defs ns [] = pure []
    normImps defs ns ((PV n i, tm, ty) :: ts) 
        = if PV n i `elem` ns
             then normImps defs ns ts
             else do rest <- normImps defs (PV n i :: ns) ts
                     pure ((PV n i, !(normaliseHoles defs env ty)) :: rest)
    normImps defs ns ((n, tm, ty) :: ts)
        = do tmnf <- normaliseHoles defs env tm
             case getFnArgs tmnf of
                -- n reduces to another hole, n', so treat it as that as long
                -- as it isn't already done
                (Meta _ n' i margs, args) =>
                    if not (n' `elem` ns)
                       then do rest <- normImps defs (n' :: ns) ts
                               tynf <- normaliseHoles defs env ty
                               pure ((n', tynf) :: rest)
                       else normImps defs ns ts
                _ => do rest <- normImps defs (n :: ns) ts
                        tynf <- normaliseHoles defs env ty
                        pure ((n, tynf) :: rest)

    -- Insert the hole/binding pair into the list before the first thing
    -- which refers to it
    insert : (Name, Term vars) -> List Name -> List Name -> 
             List (Name, Term vars) -> 
             List (Name, Term vars)
    insert h ns sofar [] = [h]
    insert (hn, hty) ns sofar ((hn', hty') :: rest)
        = let used = filter (\n => elem n ns) (map fst (toList (getMetas hty'))) in
              -- 'used' is to make sure we're only worrying about metavariables
              -- introduced in *this* expression (there may be others unresolved
              -- from elsewhere, for type inference purposes)
              if hn `elem` used
                 then (hn, hty) :: (hn', hty') :: rest
                 else (hn', hty') :: 
                          insert (hn, hty) ns (hn' :: sofar) rest
    
    -- Sort the list of implicits so that each binding is inserted *after*
    -- all the things it depends on (assumes no cycles)
    depSort : List Name -> List (Name, Term vars) -> 
              List (Name, Term vars)
    depSort hnames [] = []
    depSort hnames (h :: hs) = insert h hnames [] (depSort hnames hs)

export
checkBindVar : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               RigCount -> ElabInfo -> Env Term vars -> 
               FC -> String -> -- string is base of the pattern name 
               Maybe (Glued vars) ->
               Core (Term vars, Glued vars)
checkBindVar rig elabinfo env fc str topexp
    = do let elabmode = elabMode elabinfo
         -- In types, don't rebind if the name is already in scope;
         -- Below, return True if we don't need to implicitly bind the name
         let False = case implicitMode elabinfo of
                          PI _ => maybe False (const True) (defined (UN str) env)
                          _ => False
               | _ => check rig elabinfo env (IVar fc (UN str)) topexp
         est <- get EST
         let n = PV (UN str) (defining est)
         noteLHSPatVar elabmode str
         notePatVar n
         est <- get EST
         case lookup n (boundNames est) of
              Nothing => 
                do (tm, exp, bty) <- mkPatternHole fc rig n env
                                              (implicitMode elabinfo)
                                              topexp
                   log 5 $ "Added Bound implicit " ++ show (n, (tm, exp, bty))
                   defs <- get Ctxt
                   est <- get EST
                   put EST 
                       (record { boundNames $= ((n, (tm, exp)) ::),
                                 toBind $= ((n, (tm, bty)) :: ) } est)
                   -- addNameType loc (UN str) env exp
                   checkExp rig elabinfo env fc tm (gnf defs env exp) topexp
              Just (tm, ty) =>
                do -- TODO: for metadata addNameType loc (UN str) env ty
                   defs <- get Ctxt
                   checkExp rig elabinfo env fc tm (gnf defs env ty) topexp

export
checkBindHere : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto e : Ref EST (EState vars)} ->
                RigCount -> ElabInfo -> Env Term vars -> 
                FC -> BindMode -> RawImp ->
                Maybe (Glued vars) ->
                Core (Term vars, Glued vars)
checkBindHere rig elabinfo env fc bindmode tm exp
    = do est <- get EST
         let oldenv = outerEnv est
         let oldsub = subEnv est
         let oldbif = bindIfUnsolved est
         let dontbind = map fst (toBind est)
         -- Set the binding environment in the elab state - unbound
         -- implicits should have access to whatever is in scope here
         put EST (updateEnv env SubRefl [] est)
         (tmv, tmt) <- check rig elabinfo env tm exp
         solveConstraints (case elabMode elabinfo of
                                InLHS c => InLHS
                                _ => InTerm) Normal
         argImps <- getToBind fc (elabMode elabinfo)
                              bindmode env dontbind tmv
         clearToBind dontbind
         defs <- get Ctxt
         est <- get EST
         put EST (updateEnv oldenv oldsub oldbif 
                     (record { boundNames = [] } est))
         (bv, bt) <- bindImplicits fc bindmode
                                   defs env argImps
                                   !(normaliseHoles defs env tmv)
                                   (TType fc)
         traverse implicitBind (map fst argImps)
         checkExp rig elabinfo env fc bv (gnf defs env bt) exp
