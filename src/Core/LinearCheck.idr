module Core.LinearCheck

import Core.CaseTree
import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.Options
import Core.UnifyState
import Core.Value
import Core.TT

%default covering

-- List of variable usages - we'll count the contents of specific variables
-- when discharging binders, to ensure that linear names are only used once
data Usage : List Name -> Type where
     Nil : Usage vars
     (::) : Var vars -> Usage vars -> Usage vars

Show (Usage vars) where
  show xs = "[" ++ showAll xs ++ "]"
    where
      showAll : Usage vs -> String
      showAll [] = ""
      showAll [el] = show el
      showAll (x :: xs) = show x ++ ", " ++ show xs

doneScope : Usage (n :: vars) -> Usage vars
doneScope [] = []
doneScope (MkVar First :: xs) = doneScope xs
doneScope (MkVar (Later p) :: xs) = MkVar p :: doneScope xs

(++) : Usage ns -> Usage ns -> Usage ns
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

count : Nat -> Usage ns -> Nat
count p [] = 0
count p (v :: xs)
    = if p == varIdx v then 1 + count p xs else count p xs

localPrf : {later : _} -> Var (later ++ n :: vars)
localPrf {later = []} = MkVar First
localPrf {n} {vars} {later = (x :: xs)}
    = let MkVar p = localPrf {n} {vars} {later = xs} in
          MkVar (Later p)

mutual
  updateHoleUsageArgs : {auto c : Ref Ctxt Defs} ->
                        {auto u : Ref UST UState} ->
                        (useInHole : Bool) ->
                        Var vars -> List (Var vars) ->
                        List (Term vars) -> Core Bool
  updateHoleUsageArgs useInHole var zs [] = pure False
  updateHoleUsageArgs useInHole var zs (a :: as)
      = do h <- updateHoleUsage useInHole var zs a
           h' <- updateHoleUsageArgs useInHole var zs as
           pure (h || h')

  -- The assumption here is that hole types are abstracted over the entire
  -- environment, so that they have the appropriate number of function
  -- arguments and there are no lets
  updateHoleType : {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   (useInHole : Bool) ->
                   Var vars -> List (Var vars) ->
                   Term vs -> List (Term vars) ->
                   Core (Term vs)
  updateHoleType useInHole var zs (Bind bfc nm (Pi c e ty) sc) (Local _ r v _ :: as)
      -- if the argument to the hole type is the variable of interest,
      -- and the variable should be used in the hole, set it to Rig1,
      -- otherwise set it to Rig0
      = if varIdx var == v
           then do scty <- updateHoleType False var zs sc as
                   let c' = if useInHole then c else Rig0
                   pure (Bind bfc nm (Pi c' e ty) scty)
           else if elem v (map varIdx zs)
                then do scty <- updateHoleType useInHole var zs sc as
                        pure (Bind bfc nm (Pi Rig0 e ty) scty)
                else do scty <- updateHoleType useInHole var zs sc as
                        pure (Bind bfc nm (Pi c e ty) scty)
  updateHoleType useInHole var zs (Bind bfc nm (Pi c e ty) sc) (a :: as)
      = do updateHoleUsage False var zs a
           scty <- updateHoleType useInHole var zs sc as
           pure (Bind bfc nm (Pi c e ty) scty)
  updateHoleType useInHole var zs ty as
      = do updateHoleUsageArgs False var zs as
           pure ty

  updateHoleUsagePats : {auto c : Ref Ctxt Defs} ->
                        {auto u : Ref UST UState} ->
                        (useInHole : Bool) ->
                        Var vars -> List (Term vars) ->
                        (vs ** (Env Term vs, Term vs, Term vs)) ->
                        Core Bool
  updateHoleUsagePats {vars} useInHole var args (vs ** (env, lhs, rhs))
      = do -- Find the argument which corresponds to var
           let argpos = findArg Z args
           log 10 $ "At positions " ++ show argpos
           -- Find what it's position is in env by looking at the lhs args
           let vars = mapMaybe (findLocal (getArgs lhs)) argpos
           hs <- traverse (\vsel => updateHoleUsage useInHole vsel [] rhs)
                          vars
           pure (or (map Delay hs))
    where
      findArg : Nat -> List (Term vars) -> List Nat
      findArg i [] = []
      findArg i (Local _ _ idx vel :: els)
          = if idx == varIdx var
               then i :: findArg (1 + i) els
               else findArg (1 + i) els
      findArg i (_ :: els) = findArg (1 + i) els

      findLocal : List (Term vs) -> Nat -> Maybe (Var vs)
      findLocal (Local _ _ _ p :: _) Z = Just (MkVar p)
      findLocal (As _ _ (Local _ _ _ p) _ :: _) Z = Just (MkVar p)
      findLocal (As _ _ _ (Local _ _ _ p) :: _) Z = Just (MkVar p)
      findLocal (_ :: els) (S k) = findLocal els k
      findLocal _ _ = Nothing

  updateHoleUsage : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    (useInHole : Bool) ->
                    Var vars -> List (Var vars) ->
                    Term vars -> Core Bool
  updateHoleUsage useInHole (MkVar var) zs (Bind _ n (Let c val ty) sc)
      = do h <- updateHoleUsage useInHole (MkVar var) zs val
           h' <- updateHoleUsage useInHole (MkVar (Later var)) (map weaken zs) sc
           pure (h || h')
  updateHoleUsage useInHole (MkVar var) zs (Bind _ n b sc)
      = updateHoleUsage useInHole (MkVar (Later var)) (map weaken zs) sc
  updateHoleUsage useInHole var zs (Meta fc n i args)
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
                | Nothing => updateHoleUsageArgs useInHole var zs args
           -- only update for holes with no definition yet
           case definition gdef of
                Hole _ _ =>
                   do let ty = type gdef
                      ty' <- updateHoleType useInHole var zs ty args
                      updateTy i ty'
                      pure True
                _ => updateHoleUsageArgs useInHole var zs args
  updateHoleUsage useInHole var zs (As _ _ a p)
      = do h <- updateHoleUsage useInHole var zs a
           h' <- updateHoleUsage useInHole var zs a
           pure (h || h')
  updateHoleUsage useInHole var zs (TDelayed _ _ t)
      = updateHoleUsage useInHole var zs t
  updateHoleUsage useInHole var zs (TDelay _ _ _ t)
      = updateHoleUsage useInHole var zs t
  updateHoleUsage useInHole var zs (TForce _ _ t)
      = updateHoleUsage useInHole var zs t
  updateHoleUsage useInHole var zs tm
      = case getFnArgs tm of
             (Ref _ _ fn, args) =>
                do aup <- updateHoleUsageArgs useInHole var zs args
                   defs <- get Ctxt
                   Just (NS _ (CaseBlock _ _), PMDef _ _ _ _ pats) <-
                         lookupExactBy (\d => (fullname d, definition d))
                                       fn (gamma defs)
                       | _ => pure aup
                   hs <- traverse (updateHoleUsagePats useInHole var args) pats
                   pure (or (aup :: map Delay hs))
             (f, []) => pure False
             (f, args) => updateHoleUsageArgs useInHole var zs (f :: args)

-- Linearity checking of an already checked term. This serves two purposes:
--  + Checking correct usage of linear bindings
--  + updating hole types to reflect usage counts correctly
-- Returns term, normalised type, and a list of used variables
mutual
  lcheck : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState } ->
           RigCount -> (erase : Bool) -> Env Term vars -> Term vars ->
           Core (Term vars, Glued vars, Usage vars)
  lcheck {vars} rig erase env (Local {name} fc x idx prf)
      = let b = getBinder prf env
            rigb = multiplicity b
            ty = binderType b in
            do when (not erase) $ rigSafe rigb rig
               pure (Local fc x idx prf, gnf env ty, used rig)
    where
      getName : {idx : _} -> (vs : List Name) -> .(IsVar n idx vs) -> Name
      getName (x :: _) First = x
      getName (x :: xs) (Later p) = getName xs p

      rigSafe : RigCount -> RigCount -> Core ()
      rigSafe Rig1 RigW = throw (LinearMisuse fc name Rig1 RigW)
      rigSafe Rig0 RigW = throw (LinearMisuse fc name Rig0 RigW)
      rigSafe Rig0 Rig1 = throw (LinearMisuse fc name Rig0 Rig1)
      rigSafe _ _ = pure ()

      -- count the usage if we're in a linear context. If not, the usage doesn't
      -- matter
      used : RigCount -> Usage vars
      used Rig1 = [MkVar prf]
      used _ = []

  lcheck rig erase env (Ref fc nt fn)
      = do ty <- lcheckDef fc rig erase env fn
           pure (Ref fc nt fn, gnf env (embed ty), [])

  -- If the meta has a definition, and we're not in Rig0, expand it first
  -- and check the result.
  -- Otherwise, don't count variable usage in holes, so as far as linearity
  -- checking is concerned, update the type so that the binders
  -- are in Rig0
  lcheck {vars} rig erase env (Meta fc n idx args)
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact (Resolved idx) (gamma defs)
                | _ => throw (UndefinedName fc n)
           let expand = case (definition gdef, rig) of
                             (_, Rig0) => False
                             (PMDef _ _ _ _ _, _) => True
                             _ => False
           logC 10 $ do
             def <- the (Core String) $ case definition gdef of
                         PMDef _ _ (STerm tm) _ _ => do tm' <- toFullNames tm
                                                        pure (show tm')
                         _ => pure ""
             pure (show rig ++ ": " ++ show n ++ " " ++ show fc ++ "\n"
                     ++ show def)
           if expand
              then expandMeta rig erase env n idx (definition gdef) args
              else do let ty : ClosedTerm
                             = case definition gdef of
                                    Hole _ _ => unusedHoleArgs args (type gdef)
                                    _ => type gdef
                      nty <- nf defs env (embed ty)
                      lcheckMeta rig erase env fc n idx args [] nty
    where
      unusedHoleArgs : List a -> Term vs -> Term vs
      unusedHoleArgs (_ :: args) (Bind bfc n (Pi _ e ty) sc)
          = Bind bfc n (Pi Rig0 e ty) (unusedHoleArgs args sc)
      unusedHoleArgs args (Bind bfc n (Let c e ty) sc)
          = Bind bfc n (Let c e ty) (unusedHoleArgs args sc)
      unusedHoleArgs _ ty = ty

  lcheck rig_in erase env (Bind fc nm b sc)
      = do (b', bt, usedb) <- lcheckBinder rig erase env b
           -- Anything linear can't be used in the scope of a lambda, if we're
           -- checking in general context
           let env' = case (rig_in, b) of
                           (RigW, Lam _ _ _) => eraseLinear env
                           _ => env
           (sc', sct, usedsc) <- lcheck rig erase (b' :: env') sc
           defs <- get Ctxt

           let used_in = count 0 usedsc
           holeFound <- if not erase && isLinear (multiplicity b)
                           then updateHoleUsage (used_in == 0)
                                         (MkVar First)
                                         (map weaken (getZeroes env'))
                                         sc'
                           else pure False

           -- if there's a hole, assume it will contain the missing usage
           -- if there is none already
           let used = case rigMult (multiplicity b) rig of
                           Rig1 => if holeFound && used_in == 0
                                      then 1
                                      else used_in
                           _ => used_in

           when (not erase) $
               checkUsageOK used (rigMult (multiplicity b) rig)
           defs <- get Ctxt
           discharge defs env fc nm b' bt sc' sct (usedb ++ doneScope usedsc)
    where
      rig : RigCount
      rig = case b of
                 Pi _ _ _ => Rig0
                 _ => case rig_in of
                           Rig0 => Rig0
                           _ => Rig1

      getZeroes : Env Term vs -> List (Var vs)
      getZeroes [] = []
      getZeroes (b :: bs)
          = case multiplicity b of
                 Rig0 => MkVar First :: map weaken (getZeroes bs)
                 _ => map weaken (getZeroes bs)

      eraseLinear : Env Term vs -> Env Term vs
      eraseLinear [] = []
      eraseLinear (b :: bs)
          = case multiplicity b of
                 Rig1 => setMultiplicity b Rig0 :: eraseLinear bs
                 _ => b :: eraseLinear bs

      checkUsageOK : Nat -> RigCount -> Core ()
      checkUsageOK used Rig0 = pure ()
      checkUsageOK used RigW = pure ()
      checkUsageOK used Rig1
          = if used == 1
               then pure ()
               else throw (LinearUsed fc used nm)

  lcheck rig erase env (App fc f a)
      = do (f', gfty, fused) <- lcheck rig erase env f
           defs <- get Ctxt
           fty <- getNF gfty
           case fty of
                NBind _ _ (Pi rigf _ ty) scdone =>
                     -- if the argument is borrowed, it's okay to use it in
                     -- unrestricted context, because we'll be out of the
                     -- application without spending it
                   do let checkRig = rigMult rigf rig
                      (a', gaty, aused) <- lcheck checkRig erase env a
                      sc' <- scdone defs (toClosure defaultOpts env a')
                      let aerased = if erase && rigf == Rig0 then Erased fc False else a'
                      -- Possibly remove this check, or make it a compiler
                      -- flag? It is a useful double check on the result of
                      -- elaboration, but there are pathological cases where
                      -- it makes the check very slow (id id id id ... id id etc
                      -- for example) and there may be similar realistic cases.
                      -- If elaboration is correct, this should never fail!
                      opts <- getSession
                      when (debugElabCheck opts) $ do
                        aty <- getNF gaty
                        when (not !(convert defs env aty ty)) $
                           do ty' <- quote defs env ty
                              aty' <- quote defs env aty
                              throw (CantConvert fc env ty' aty')
                      pure (App fc f' aerased,
                            glueBack defs env sc',
                            fused ++ aused)
                _ => do tfty <- getTerm gfty
                        throw (GenericMsg fc ("Linearity checking failed on " ++ show f' ++
                              " (" ++ show tfty ++ " not a function type)"))

  lcheck rig erase env (As fc s as pat)
      = do (as', _, _) <- lcheck rig erase env as
           (pat', pty, u) <- lcheck rig erase env pat
           pure (As fc s as' pat', pty, u)
  lcheck rig erase env (TDelayed fc r ty)
      = do (ty', _, u) <- lcheck rig erase env ty
           pure (TDelayed fc r ty', gType fc, u)
  lcheck rig erase env (TDelay fc r ty val)
      = do (ty', _, _) <- lcheck Rig0 erase env ty
           (val', gty, u) <- lcheck rig erase env val
           ty <- getTerm gty
           pure (TDelay fc r ty' val', gnf env (TDelayed fc r ty), u)
  lcheck rig erase env (TForce fc r val)
      = do (val', gty, u) <- lcheck rig erase env val
           tynf <- getNF gty
           case tynf of
                NDelayed _ r narg
                    => do defs <- get Ctxt
                          pure (TForce fc r val', glueBack defs env narg, u)
                _ => throw (GenericMsg fc "Not a delayed tyoe")
  lcheck rig erase env (PrimVal fc c)
      = pure (PrimVal fc c, gErased fc, [])
  lcheck rig erase env (Erased fc i)
      = pure (Erased fc i, gErased fc, [])
  lcheck rig erase env (TType fc)
      = pure (TType fc, gType fc, [])

  lcheckBinder : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 RigCount -> (erase : Bool) -> Env Term vars ->
                 Binder (Term vars) ->
                 Core (Binder (Term vars), Glued vars, Usage vars)
  lcheckBinder rig erase env (Lam c x ty)
      = do (tyv, tyt, _) <- lcheck Rig0 erase env ty
           pure (Lam c x tyv, tyt, [])
  lcheckBinder rig erase env (Let rigc val ty)
      = do (tyv, tyt, _) <- lcheck Rig0 erase env ty
           (valv, valt, vs) <- lcheck (rigMult rig rigc) erase env val
           pure (Let rigc valv tyv, tyt, vs)
  lcheckBinder rig erase env (Pi c x ty)
      = do (tyv, tyt, _) <- lcheck Rig0 erase env ty
           pure (Pi c x tyv, tyt, [])
  lcheckBinder rig erase env (PVar c p ty)
      = do (tyv, tyt, _) <- lcheck Rig0 erase env ty
           pure (PVar c p tyv, tyt, [])
  lcheckBinder rig erase env (PLet rigc val ty)
      = do (tyv, tyt, _) <- lcheck Rig0 erase env ty
           (valv, valt, vs) <- lcheck (rigMult rig rigc) erase env val
           pure (PLet rigc valv tyv, tyt, vs)
  lcheckBinder rig erase env (PVTy c ty)
      = do (tyv, tyt, _) <- lcheck Rig0 erase env ty
           pure (PVTy c tyv, tyt, [])

  discharge : Defs -> Env Term vars ->
              FC -> (nm : Name) -> Binder (Term vars) -> Glued vars ->
              Term (nm :: vars) -> Glued (nm :: vars) -> Usage vars ->
              Core (Term vars, Glued vars, Usage vars)
  discharge defs env fc nm (Lam c x ty) gbindty scope gscopety used
       = do scty <- getTerm gscopety
            pure (Bind fc nm (Lam c x ty) scope,
                  gnf env (Bind fc nm (Pi c x ty) scty), used)
  discharge defs env fc nm (Let c val ty) gbindty scope gscopety used
       = do scty <- getTerm gscopety
            pure (Bind fc nm (Let c val ty) scope,
                  gnf env (Bind fc nm (Let c val ty) scty), used)
  discharge defs env fc nm (Pi c x ty) gbindty scope gscopety used
       = pure (Bind fc nm (Pi c x ty) scope, gbindty, used)
  discharge defs env fc nm (PVar c p ty) gbindty scope gscopety used
       = do scty <- getTerm gscopety
            pure (Bind fc nm (PVar c p ty) scope,
                  gnf env (Bind fc nm (PVTy c ty) scty), used)
  discharge defs env fc nm (PLet c val ty) gbindty scope gscopety used
       = do scty <- getTerm gscopety
            pure (Bind fc nm (PLet c val ty) scope,
                  gnf env (Bind fc nm (PLet c val ty) scty), used)
  discharge defs env fc nm (PVTy c ty) gbindty scope gscopety used
       = pure (Bind fc nm (PVTy c ty) scope, gbindty, used)

  data ArgUsage
       = UseAny -- RigW so we don't care
       | Use0 -- argument position not used
       | Use1 -- argument position used exactly once
       | UseKeep -- keep as is
       | UseUnknown -- hole, so can't tell

  Show ArgUsage where
    show UseAny = "any"
    show Use0 = "0"
    show Use1 = "1"
    show UseKeep = "keep"
    show UseUnknown = "unknown"

  -- Check argument usage in case blocks. Returns a list of how each argument
  -- in the case block is used, to build the appropriate type for the outer
  -- block.
  getArgUsage : {auto c : Ref Ctxt Defs} ->
                {auto e : Ref UST UState} ->
                FC -> RigCount -> ClosedTerm ->
                List (vs ** (Env Term vs, Term vs, Term vs)) ->
                Core (List ArgUsage)
  getArgUsage topfc rig ty pats
      = do us <- traverse (getPUsage ty) pats
           pure (map snd !(combine us))
    where
      getCaseUsage : Term ns -> Env Term vs -> List (Term vs) ->
                     Usage vs -> Term vs ->
                     Core (List (Name, ArgUsage))
      getCaseUsage ty env (As _ _ _ p :: args) used rhs
          = getCaseUsage ty env (p :: args) used rhs
      getCaseUsage (Bind _ n (Pi Rig1 e ty) sc) env (Local _ _ idx p :: args) used rhs
          = do rest <- getCaseUsage sc env args used rhs
               let used_in = count idx used
               holeFound <- updateHoleUsage (used_in == 0) (MkVar p) [] rhs
               let ause
                   = if holeFound && used_in == 0
                             then UseUnknown
                             else if used_in == 0
                                     then Use0
                                     else Use1
               pure ((n, ause) :: rest)
      getCaseUsage (Bind _ n (Pi c e ty) sc) env (arg :: args) used rhs
          = do rest <- getCaseUsage sc env args used rhs
               case c of
                    Rig0 => pure ((n, Use0) :: rest)
                    Rig1 => pure ((n, UseKeep) :: rest)
                    _ => pure ((n, UseKeep) :: rest)
      getCaseUsage tm env args used rhs = pure []

      checkUsageOK : FC -> Nat -> Name -> Bool -> RigCount -> Core ()
      checkUsageOK fc used nm isloc Rig0 = pure ()
      checkUsageOK fc used nm isloc RigW = pure ()
      checkUsageOK fc used nm True Rig1
          = if used > 1
               then throw (LinearUsed fc used nm)
               else pure ()
      checkUsageOK fc used nm isloc Rig1
          = if used == 1
               then pure ()
               else throw (LinearUsed fc used nm)

      -- Is the variable one of the lhs arguments; i.e. do we treat it as
      -- affine rather than linear
      isLocArg : Var vars -> List (Term vars) -> Bool
      isLocArg p [] = False
      isLocArg p (Local _ _ idx _ :: args)
          = if idx == varIdx p
               then True
               else isLocArg p args
      isLocArg p (As _ _ tm pat :: args)
          = isLocArg p (tm :: pat :: args)
      isLocArg p (_ :: args) = isLocArg p args

      -- As checkEnvUsage in general, but it's okay for local variables to
      -- remain unused (since in that case, they must be used outside the
      -- case block)
      checkEnvUsage : RigCount ->
                      Env Term vars -> Usage (done ++ vars) ->
                      List (Term (done ++ vars)) ->
                      Term (done ++ vars) -> Core ()
      checkEnvUsage rig [] usage args tm = pure ()
      checkEnvUsage rig {done} {vars = nm :: xs} (b :: env) usage args tm
          = do let pos = localPrf {later = done}
               let used_in = count (varIdx pos) usage

               holeFound <- if isLinear (multiplicity b)
                               then updateHoleUsage (used_in == 0) pos [] tm
                               else pure False
               let used = case rigMult (multiplicity b) rig of
                               Rig1 => if holeFound && used_in == 0
                                          then 1
                                          else used_in
                               _ => used_in
               checkUsageOK (getLoc (binderType b))
                            used nm (isLocArg pos args)
                                    (rigMult (multiplicity b) rig)
               checkEnvUsage {done = done ++ [nm]} rig env
                     (rewrite sym (appendAssociative done [nm] xs) in usage)
                     (rewrite sym (appendAssociative done [nm] xs) in args)
                     (rewrite sym (appendAssociative done [nm] xs) in tm)

      getPUsage : ClosedTerm -> (vs ** (Env Term vs, Term vs, Term vs)) ->
                  Core (List (Name, ArgUsage))
      getPUsage ty (_ ** (penv, lhs, rhs))
          = do logEnv 10 "Env" penv
               logTerm 10 "LHS" lhs
               logTerm 5 "Linear check in case RHS" rhs
               (rhs', _, used) <- lcheck rig False penv rhs
               log 10 $ "Used: " ++ show used
               let args = getArgs lhs
               checkEnvUsage {done = []} rig penv used args rhs'
               ause <- getCaseUsage ty penv args used rhs
               log 10 $ "Arg usage: " ++ show ause
               pure ause

      combineUsage : (Name, ArgUsage) -> (Name, ArgUsage) ->
                     Core (Name, ArgUsage)
      combineUsage (n, Use0) (_, Use1)
          = throw (GenericMsg topfc ("Inconsistent usage of " ++ show n ++ " in case branches"))
      combineUsage (n, Use1) (_, Use0)
          = throw (GenericMsg topfc ("Inconsistent usage of " ++ show n ++ " in case branches"))
      combineUsage (n, UseAny) _ = pure (n, UseAny)
      combineUsage _ (n, UseAny) = pure (n, UseAny)
      combineUsage (n, UseKeep) _ = pure (n, UseKeep)
      combineUsage _ (n, UseKeep) = pure (n, UseKeep)
      combineUsage (n, UseUnknown) _ = pure (n, UseUnknown)
      combineUsage _ (n, UseUnknown) = pure (n, UseUnknown)
      combineUsage x y = pure x

      combineUsages : List (Name, ArgUsage) -> List (Name, ArgUsage) ->
                      Core (List (Name, ArgUsage))
      combineUsages [] [] = pure []
      combineUsages (u :: us) (v :: vs)
          = do u' <- combineUsage u v
               us' <- combineUsages us vs
               pure (u' :: us')
      combineUsages _ _ = throw (InternalError "Argument usage lists inconsistent")

      combine : List (List (Name, ArgUsage)) ->
                Core (List (Name, ArgUsage))
      combine [] = pure []
      combine [x] = pure x
      combine (x :: xs)
          = do xs' <- combine xs
               combineUsages x xs'

  lcheckDef : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount -> (erase : Bool) -> Env Term vars -> Name ->
              Core ClosedTerm
  lcheckDef fc rig True env n
      = do defs <- get Ctxt
           Just def <- lookupCtxtExact n (gamma defs)
                | Nothing => throw (InternalError ("Linearity checking failed on " ++ show n))
           pure (type def)
  lcheckDef fc rig False env n
      = do defs <- get Ctxt
           let Just idx = getNameID n (gamma defs)
                | Nothing => throw (InternalError ("Linearity checking failed on " ++ show n))
           Just def <- lookupCtxtExact (Resolved idx) (gamma defs)
                | Nothing => throw (InternalError ("Linearity checking failed on " ++ show n))
           rigSafe (multiplicity def) rig
           if linearChecked def
              then pure (type def)
              else case definition def of
                        PMDef _ _ _ _ pats =>
                            do u <- getArgUsage (getLoc (type def))
                                                rig (type def) pats
                               log 5 $ "Overall arg usage " ++ show u
                               let ty' = updateUsage u (type def)
                               updateTy idx ty'
                               setLinearCheck idx True
                               logTerm 5 ("New type of " ++
                                          show (fullname def)) ty'
                               logTerm 5 ("Updated from " ++
                                          show (fullname def)) (type def)
                               pure ty'
                        _ => pure (type def)
    where
      updateUsage : List ArgUsage -> Term ns -> Term ns
      updateUsage (u :: us) (Bind bfc n (Pi c e ty) sc)
          = let sc' = updateUsage us sc
                c' = case u of
                          Use0 => Rig0
                          Use1 => Rig1 -- ignore usage elsewhere, we checked here
                          UseUnknown => c -- don't know, assumed unchanged and update hole types
                          UseKeep => c -- matched here, so count usage elsewhere
                          UseAny => c in -- no constraint, so leave alone
                Bind bfc n (Pi c' e ty) sc'
      updateUsage _ ty = ty

      rigSafe : RigCount -> RigCount -> Core ()
      rigSafe Rig1 RigW = throw (LinearMisuse fc !(getFullName n) Rig1 RigW)
      rigSafe Rig0 RigW = throw (LinearMisuse fc !(getFullName n) Rig0 RigW)
      rigSafe Rig0 Rig1 = throw (LinearMisuse fc !(getFullName n) Rig0 Rig1)
      rigSafe _ _ = pure ()

  expandMeta : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               RigCount -> (erase : Bool) -> Env Term vars ->
               Name -> Int -> Def -> List (Term vars) ->
               Core (Term vars, Glued vars, Usage vars)
  expandMeta rig erase env n idx (PMDef _ [] (STerm fn) _ _) args
      = do tm <- substMeta (embed fn) args []
           lcheck rig erase env tm
    where
      substMeta : Term (drop ++ vs) -> List (Term vs) -> SubstEnv drop vs ->
                  Core (Term vs)
      substMeta (Bind bfc n (Lam c e ty) sc) (a :: as) env
          = substMeta sc as (a :: env)
      substMeta (Bind bfc n (Let c val ty) sc) as env
          = substMeta (subst val sc) as env
      substMeta rhs [] env = pure (substs env rhs)
      substMeta rhs _ _ = throw (InternalError ("Badly formed metavar solution " ++ show n ++ " " ++ show fn))
  expandMeta rig erase env n idx def _
      = throw (InternalError ("Badly formed metavar solution " ++ show n ++ " " ++ show def))

  lcheckMeta : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               RigCount -> Bool -> Env Term vars ->
               FC -> Name -> Int ->
               (args : List (Term vars)) ->
               (checked : List (Term vars)) ->
               NF vars -> Core (Term vars, Glued vars, Usage vars)
  lcheckMeta rig erase env fc n idx
             (arg :: args) chk (NBind _ _ (Pi rigf _ ty) sc)
      = do let checkRig = rigMult rigf rig
           (arg', gargTy, aused) <- lcheck checkRig erase env arg
           defs <- get Ctxt
           sc' <- sc defs (toClosure defaultOpts env arg')
           let aerased = if erase && rigf == Rig0 then Erased fc False else arg'
           (tm, gty, u) <- lcheckMeta rig erase env fc n idx args
                                      (aerased :: chk) sc'
           pure (tm, gty, aused ++ u)
  lcheckMeta rig erase env fc n idx (arg :: args) chk nty
      = do defs <- get Ctxt
           empty <- clearDefs defs
           ty <- quote empty env nty
           throw (GenericMsg fc ("Linearity checking failed on metavar
                      " ++ show n ++ " (" ++ show ty ++
                      " not a function type)"))
  lcheckMeta rig erase env fc n idx [] chk nty
      = do defs <- get Ctxt
           pure (Meta fc n idx (reverse chk), glueBack defs env nty, [])


checkEnvUsage : {done : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                FC -> RigCount ->
                Env Term vars -> Usage (done ++ vars) ->
                Term (done ++ vars) ->
                Core ()
checkEnvUsage fc rig [] usage tm = pure ()
checkEnvUsage fc rig {done} {vars = nm :: xs} (b :: env) usage tm
    = do let pos = localPrf {later = done}
         let used_in = count (varIdx pos) usage

         holeFound <- if isLinear (multiplicity b)
                         then updateHoleUsage (used_in == 0) pos [] tm
                         else pure False
         let used = case rigMult (multiplicity b) rig of
                         Rig1 => if holeFound && used_in == 0
                                    then 1
                                    else used_in
                         _ => used_in
         checkUsageOK used (rigMult (multiplicity b) rig)
         checkEnvUsage {done = done ++ [nm]} fc rig env
               (rewrite sym (appendAssociative done [nm] xs) in usage)
               (rewrite sym (appendAssociative done [nm] xs) in tm)
  where
    checkUsageOK : Nat -> RigCount -> Core ()
    checkUsageOK used Rig0 = pure ()
    checkUsageOK used RigW = pure ()
    checkUsageOK used Rig1
        = if used == 1
             then pure ()
             else throw (LinearUsed fc used nm)

-- Linearity check an elaborated term. If 'erase' is set, erase anything that's in
-- a Rig0 argument position (we can't do this until typechecking is complete, though,
-- since it might be used for unification/reasoning elsewhere, so we only do this for
-- definitions ready for compilation).
export
linearCheck : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount -> (erase : Bool) ->
              Env Term vars -> Term vars ->
              Core (Term vars)
linearCheck fc rig erase env tm
    = do logTerm 5 "Linearity check on " tm
         logEnv 5 "In env" env
         (tm', _, used) <- lcheck rig erase env tm
         log 5 $ "Used: " ++ show used
         when (not erase) $ checkEnvUsage {done = []} fc rig env used tm'
         pure tm'

