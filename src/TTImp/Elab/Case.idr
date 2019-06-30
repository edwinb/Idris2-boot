module TTImp.Elab.Case

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.Elab.ImplicitBind
import TTImp.TTImp

import Data.NameMap

%default covering

export
changeVar : (old : Var vs) -> (new : Var vs) -> Term vs -> Term vs
changeVar (MkVar {i=x} old) (MkVar new) (Local fc r idx p)
    = if x == idx
         then Local fc r _ new
         else Local fc r _ p
changeVar old new (Meta fc nm i args)
    = Meta fc nm i (map (changeVar old new) args)
changeVar (MkVar old) (MkVar new) (Bind fc x b sc) 
    = Bind fc x (assert_total (map (changeVar (MkVar old) (MkVar new)) b)) 
		            (changeVar (MkVar (Later old)) (MkVar (Later new)) sc)
changeVar old new (App fc fn arg) 
    = App fc (changeVar old new fn) (changeVar old new arg)
changeVar old new (As fc nm p)
    = As fc (changeVar old new nm) (changeVar old new p)
changeVar old new (TDelayed fc r p)
    = TDelayed fc r (changeVar old new p)
changeVar old new (TDelay fc r t p)
    = TDelay fc r (changeVar old new t) (changeVar old new p)
changeVar old new (TForce fc p)
    = TForce fc (changeVar old new p)
changeVar old new tm = tm

findLater : (x : Name) -> (newer : List Name) -> Var (newer ++ x :: older)
findLater x [] = MkVar First
findLater {older} x (_ :: xs)
    = let MkVar p = findLater {older} x xs in
          MkVar (Later p)

-- For any variable *not* in vs', re-abstract over it in the term
absOthers : FC -> Env Term vs -> SubVars vs' vs -> 
            Term (done ++ vs) -> Term (done ++ vs)
absOthers fc _ SubRefl tm = tm
absOthers {done} {vs = x :: vars} fc (b :: env) (KeepCons sub) tm 
  = rewrite appendAssociative done [x] vars in
            absOthers {done = done ++ [x]} fc env sub
               (rewrite sym (appendAssociative done [x] vars) in tm)
absOthers {done} {vs = x :: vars} fc (b :: env) (DropCons sub) tm
  = let bindervs : Binder (Term (done ++ (x :: vars)))
                      = rewrite appendAssociative done [x] vars in
                                map (weakenNs (done ++ [x])) b
        b' = Pi (multiplicity b) Explicit (binderType bindervs)
        btm = Bind fc x b' 
                   (changeVar (findLater _ (x :: done)) (MkVar First) (weaken tm)) in
        rewrite appendAssociative done [x] vars in
                absOthers {done = done ++ [x]} fc env sub
                    (rewrite sym (appendAssociative done [x] vars) in btm)

-- Abstract over the environment, inserting binders for the
-- unbound implicits at the point in the environment where they were
-- created (which is after the outer environment was bound)
export
abstractOver : FC -> Defs -> BindMode -> Env Term vs -> 
               Maybe (SubVars outer vs) -> List (Name, ImplBinding outer) ->
               (tm : Term vs) -> Core ClosedTerm
abstractOver fc defs bindmode [] Nothing imps tm = pure tm
abstractOver fc defs bindmode [] (Just SubRefl) imps tm 
    = do tm' <- if isNil imps 
                   then pure tm
                   else normaliseHoles defs [] tm
         (bimptm, _) <- bindImplicits fc bindmode defs [] imps tm' (TType fc)
         pure bimptm
abstractOver fc defs bindmode (b :: env) (Just SubRefl) imps tm 
    = do let c : RigCount
            = case multiplicity b of
                   Rig1 => Rig0
                   r => r
         tm' <- if isNil imps 
                   then pure tm
                   else normaliseHoles defs (b :: env) tm
         (bimptm, _) <- bindImplicits fc bindmode defs (b :: env) imps
                                      tm' (TType fc)
         abstractOver fc defs bindmode env Nothing imps 
                  (Bind fc _ (Pi c Explicit (binderType b)) bimptm)
abstractOver fc defs bindmode (b :: env) (Just (DropCons p)) imps tm 
    = let c = case multiplicity b of
                   Rig1 => Rig0
                   r => r in
      abstractOver fc defs bindmode env (Just p) imps 
                   (Bind fc _ (Pi c Explicit (binderType b)) tm)
abstractOver fc defs bindmode (b :: env) _ imps tm 
    = let c = case multiplicity b of
                   Rig1 => Rig0
                   r => r in
      abstractOver fc defs bindmode env Nothing imps 
                   (Bind fc _ (Pi c Explicit (binderType b)) tm)

toRig1 : {idx : Nat} -> .(IsVar name idx vs) -> Env Term vs -> Env Term vs
toRig1 First (b :: bs) 
    = if multiplicity b == Rig0
         then setMultiplicity b Rig1 :: bs
         else b :: bs
toRig1 (Later p) (b :: bs) = b :: toRig1 p bs

toRig0 : {idx : Nat} -> .(IsVar name idx vs) -> Env Term vs -> Env Term vs
toRig0 First (b :: bs) = setMultiplicity b Rig0 :: bs
toRig0 (Later p) (b :: bs) = b :: toRig0 p bs

allow : Maybe (Var vs) -> Env Term vs -> Env Term vs
allow Nothing env = env
allow (Just (MkVar p)) env = toRig1 p env

-- If the name is used elsewhere, update its multiplicity so it's
-- not required to be used in the case block
updateMults : List (Var vs) -> Env Term vs -> Env Term vs
updateMults [] env = env
updateMults (MkVar p :: us) env = updateMults us (toRig0 p env)

shrinkImp : SubVars outer vars -> 
            (Name, ImplBinding vars) -> Maybe (Name, ImplBinding outer)
shrinkImp sub (n, NameBinding c tm ty)
    = do tm' <- shrinkTerm tm sub
         ty' <- shrinkTerm ty sub
         pure (n, NameBinding c tm' ty')
shrinkImp sub (n, AsBinding c tm ty pat)
    = do tm' <- shrinkTerm tm sub
         ty' <- shrinkTerm ty sub
         pat' <- shrinkTerm pat sub
         pure (n, AsBinding c tm' ty' pat')

findImpsIn : FC -> Env Term vars -> List (Name, Term vars) -> Term vars ->
             Core ()
findImpsIn fc env ns (Bind _ n b@(Pi _ Implicit ty) sc)
    = findImpsIn fc (b :: env) 
                 ((n, weaken ty) :: map (\x => (fst x, weaken (snd x))) ns)
                 sc
findImpsIn fc env ns (Bind _ n b sc)
    = findImpsIn fc (b :: env) 
                 (map (\x => (fst x, weaken (snd x))) ns)
                 sc
findImpsIn fc env ns ty
    = when (not (isNil ns)) $
           throw (TryWithImplicits fc env (reverse ns))

merge : {vs : List Name} ->
        List (Var vs) -> List (Var vs) -> List (Var vs)
merge [] xs = xs
merge (v :: vs) xs
    = merge vs (v :: filter (\p => not (sameVar v p)) xs)

-- Extend the list of variables we need in the environment so far, removing
-- duplicates
extendNeeded : Binder (Term vs) -> 
               Env Term vs -> List (Var vs) -> List (Var vs)
extendNeeded (Let c ty val) env needed
    = merge (findUsedLocs env ty) (merge (findUsedLocs env val) needed)
extendNeeded (PLet c ty val) env needed
    = merge (findUsedLocs env ty) (merge (findUsedLocs env val) needed)
extendNeeded b env needed
    = merge (findUsedLocs env (binderType b)) needed

isNeeded : Nat -> List (Var vs) -> Bool
isNeeded x [] = False
isNeeded x (MkVar {i} _ :: xs) = x == i || isNeeded x xs

-- Shrink the environment so that any generated lambdas are not
-- included.
-- Here, 'Keep' means keep it in the outer environment, i.e. not needed
-- for the case block. So, if it's already in the SubVars set, keep it,
-- if it's not in the SubVars, keep it if it's a non-user name and
-- doesn't appear in any types later in the environment
-- (Yes, this is the opposite of what might seem natural, but we're
-- starting from the 'outerEnv' which is the fragment of the environment
-- used for the outer scope)
shrinkEnv : Defs -> SubVars outer vs -> List (Var vs) ->
            (done : List Name) -> Env Term vs -> 
            Core (outer' ** SubVars outer' vs)
shrinkEnv defs SubRefl needed done env 
    = pure (_ ** SubRefl) -- keep them all
-- usable name, so drop from the outer environment
shrinkEnv {vs = UN n :: _} defs (DropCons p) needed done (b :: env) 
    = do b' <- traverse (normaliseHoles defs env) b
         (_ ** p') <- shrinkEnv defs p 
                        (extendNeeded b' 
                                      env (dropFirst needed)) 
                                      (UN n :: done) env
         -- if shadowed and not needed, keep in the outer env
         if (UN n `elem` done) && not (isNeeded 0 needed)
            then pure (_ ** KeepCons p')
            else pure (_ ** DropCons p')
shrinkEnv {vs = n :: _} defs (DropCons p) needed done (b :: env)
    = do b' <- traverse (normaliseHoles defs env) b
         (_ ** p') <- shrinkEnv defs p 
                        (extendNeeded b' 
                                      env (dropFirst needed)) 
                                      (n :: done) env
         if isNeeded 0 needed || notLam b
            then pure (_ ** DropCons p') 
            else pure (_ ** KeepCons p')
  where
    notLam : Binder t -> Bool
    notLam (Lam _ _ _) = False
    notLam _ = True
shrinkEnv {vs = n :: _} defs (KeepCons p) needed done (b :: env) 
    = do b' <- traverse (normaliseHoles defs env) b
         (_ ** p') <- shrinkEnv defs p 
                        (extendNeeded b'
                                      env (dropFirst needed)) 
                                      (n :: done) env
         pure (_ ** KeepCons p') -- still keep it

findScrutinee : Env Term vs -> SubVars vs' vs ->
                RawImp -> Maybe (Var vs)
findScrutinee {vs = n' :: _} (b :: bs) (DropCons p) (IVar loc' n)
    = if n' == n && notLet b
         then Just (MkVar First)
         else do MkVar p <- findScrutinee bs p (IVar loc' n)
                 Just (MkVar (Later p))
  where
    notLet : Binder t -> Bool
    notLet (Let _ _ _) = False
    notLet _ = True
findScrutinee (b :: bs) (KeepCons p) (IVar loc' n)
    = do MkVar p <- findScrutinee bs p (IVar loc' n)
         Just (MkVar (Later p))
findScrutinee _ _ _ = Nothing

export
caseBlock : {vars : _} ->
            {auto c : Ref Ctxt Defs} -> 
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            RigCount -> 
            ElabInfo -> FC -> 
            NestedNames vars -> 
            Env Term vars -> 
            RawImp -> -- original scrutinee
            Term vars -> -- checked scrutinee
            Term vars -> -- its type
            RigCount -> -- its multiplicity
            List ImpClause -> Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
caseBlock {vars} rigc elabinfo fc nest env scr scrtm scrty caseRig alts expected
    = do -- TODO (or to decide): Blodwen allowed ambiguities in the scrutinee
         -- to be delayed, but now I think it's better to have simpler
         -- resolution rules, and not delay

         est <- get EST
         fullImps_in <- getToBind fc (elabMode elabinfo)
                               (implicitMode elabinfo) env []
         let fullImps = mapMaybe (shrinkImp (subEnv est)) fullImps_in
         log 5 $ "Doing a case under unbound implicits " ++ show fullImps
         
         scrn <- genVarName "scr"
         casen <- genCaseName (defining est)

         -- Update environment so that linear bindings which were used
         -- (esp. in the scrutinee!) are set to 0 in the case type
         let env = updateMults (linearUsed est) env

         -- The 'pre_env' is the environment we apply any local (nested)
         -- names to. Here *all* the names have multiplicity 0 (we're
         -- going to abstract over them all again, in case the case block
         -- does any refining of their types/values)
         let pre_env = mkLocalEnv env

         defs <- get Ctxt
         -- To build the type, we abstract over the whole environment (so that
         -- we can use the nested names which might use that environment) and the
         -- part of the environment which is not the outer environment (so that we
         -- can dependent pattern match on parts of it). "smaller" is the outer
         -- environment, taken from the elaboration state, also removing
         -- things we can't match on and nothing depends on
         (svars ** smaller) <- shrinkEnv defs (subEnv est) [] [] env

         -- if the scrutinee is ones of the arguments in 'env' we should
         -- split on that, rather than adding it as a new argument
         let splitOn = findScrutinee env smaller scr
         
         caseretty <- the (Core (Term vars)) $ case expected of
                           Just ty => getTerm ty
                           _ =>
                              do nmty <- genName "caseTy"
                                 metaVar fc Rig0 env nmty (TType fc)

         let envscope = absOthers {done = []} fc (allow splitOn env) smaller 
                            (maybe (Bind fc scrn (Pi caseRig Explicit scrty) 
                                       (weaken caseretty))
                                   (const caseretty) splitOn)
         casefnty <- abstractOver fc defs (implicitMode elabinfo)
                                     env (Just (subEnv est)) fullImps envscope

         logEnv 10 "Case env" env
         logTermNF 2 ("Case function type: " ++ show casen) [] casefnty

         -- If we've had to add implicits to the case type (because there
         -- were unbound implicits) then we're in a bit of a mess. Easiest
         -- way out is to throw an error and try again with the implicits
         -- actually bound! This is rather hacky, but a lot less fiddly than
         -- the alternative of fixing up the environment
         when (not (isNil fullImps)) $ findImpsIn fc [] [] casefnty

         cidx <- addDef casen (newDef fc casen rigc [] casefnty Private None)
         let caseRef = Ref fc Func (Resolved cidx)
         setFlag fc casen Inline

         let alts' = map (updateClause casen splitOn env smaller) alts
         log 2 $ "Generated alts: " ++ show alts'
         let nest' = record { names $= ((Resolved cidx, (Nothing, 
                                  (\fc, nt => applyToFull fc caseRef pre_env))) ::) } 
                            nest
         processDecl [InCase] nest' pre_env (IDef fc casen alts')

         let applyEnv = applyToOthers fc (applyToFull fc caseRef env) env smaller
         pure (maybe (App fc applyEnv scrtm) 
                     (const applyEnv) splitOn, 
               gnf env caseretty)

  where
    mkLocalEnv : Env Term vs -> Env Term vs
    mkLocalEnv [] = []
    mkLocalEnv (b :: bs) 
        = let b' = if isLinear (multiplicity b)
                      then setMultiplicity b Rig0
                      else b in
              b' :: mkLocalEnv bs

    canBindName : Name -> List Name -> Maybe Name
    canBindName n@(UN _) vs
       = if n `elem` vs then Nothing else Just n
    canBindName _ vs = Nothing

    addEnv : Env Term vs -> SubVars vs' vs -> List Name -> 
             (List (Maybe RawImp), List Name)
    addEnv [] sub used = ([], used)
    addEnv {vs = v :: vs} (b :: bs) SubRefl used
        = let (rest, used') = addEnv bs SubRefl used in
              (Nothing :: rest, used')
    addEnv (b :: bs) (KeepCons p) used
        = let (rest, used') = addEnv bs p used in
              (Nothing :: rest, used')
    addEnv {vs = v :: vs} (b :: bs) (DropCons p) used
        = let (rest, used') = addEnv bs p used in
              case canBindName v used' of
                   Just n => (Just (IAs fc UseLeft n (Implicit fc True)) :: rest, n :: used')
                   _ => (Just (Implicit fc True) :: rest, used')

    -- Replace a variable in the argument list; if the reference is to
    -- a variable kept in the outer environment (therefore not an argument
    -- in the list) don't consume it
    replace : {idx : Nat} -> .(IsVar name idx vs) -> 
              RawImp -> List (Maybe RawImp) ->
              List RawImp
    replace First lhs (old :: xs) 
       = let lhs' = case old of
                         Just (IAs loc' side n _) => IAs loc' side n lhs 
                         _ => lhs in
             lhs' :: mapMaybe id xs
    replace (Later p) lhs (Nothing :: xs) 
        = replace p lhs xs
    replace (Later p) lhs (Just x :: xs) 
        = x :: replace p lhs xs
    replace _ _ xs = mapMaybe id xs

    mkSplit : Maybe (Var vs) -> 
              RawImp -> List (Maybe RawImp) -> 
              List RawImp
    mkSplit Nothing lhs args = reverse (lhs :: mapMaybe id args)
    mkSplit (Just (MkVar prf)) lhs args
        = reverse (replace prf lhs args)

    -- Names used in the pattern we're matching on, so don't bind them
    -- in the generated case block
    usedIn : RawImp -> List Name
    usedIn (IBindVar _ n) = [UN n]
    usedIn (IApp _ f a) = usedIn f ++ usedIn a
    usedIn (IAs _ _ n a) = n :: usedIn a
    usedIn (IAlternative _ _ alts) = concatMap usedIn alts
    usedIn _ = []

    updateClause : Name -> Maybe (Var vars) ->
                   Env Term vars -> SubVars vs' vars ->
                   ImpClause -> ImpClause
    updateClause casen splitOn env sub (PatClause loc' lhs rhs)
        = let args = fst (addEnv env sub (usedIn lhs))
              args' = mkSplit splitOn lhs args in
              PatClause loc' (apply (IVar loc' casen) args') rhs
    -- With isn't allowed in a case block but include for completeness
    updateClause casen splitOn env sub (WithClause loc' lhs wval cs)
        = let args = fst (addEnv env sub (usedIn lhs))
              args' = mkSplit splitOn lhs args in
              WithClause loc' (apply (IVar loc' casen) args') wval cs
    updateClause casen splitOn env sub (ImpossibleClause loc' lhs)
        = let args = fst (addEnv env sub (usedIn lhs))
              args' = mkSplit splitOn lhs args in
              ImpossibleClause loc' (apply (IVar loc' casen) args')


export
checkCase : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            RigCount -> ElabInfo ->
            NestedNames vars -> Env Term vars -> 
            FC -> (scr : RawImp) -> (ty : RawImp) -> List ImpClause -> 
            Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
checkCase rig elabinfo nest env fc scr scrty_exp alts exp
    = do (scrtyv, scrtyt) <- check Rig0 elabinfo nest env scrty_exp 
                                   (Just (gType fc))
                                   
         logTerm 10 "Expected scrutinee type" scrtyv
         -- Try checking at the given multiplicity; if that doesn't work,
         -- try checking at Rig1 (meaning that we're using a linear variable
         -- so the scrutinee should be linear)
         (scrtm_in, gscrty, caseRig) <- handle
            (do c <- check RigW elabinfo nest env scr (Just (gnf env scrtyv))
                pure (fst c, snd c, RigW))
            (\err => case err of
                          LinearMisuse _ _ Rig1 _
                            => do c <- check Rig1 elabinfo nest env scr 
                                             (Just (gnf env scrtyv))
                                  pure (fst c, snd c, Rig1)
                          e => throw e)
         scrty <- getTerm gscrty
         logTermNF 5 "Scrutinee type" env scrty
         checkConcrete !(getNF gscrty)
         caseBlock rig elabinfo fc nest env scr scrtm_in scrty caseRig alts exp
  where
    -- For the moment, throw an error if we haven't been able to work out
    -- the type of the case scrutinee, because we'll need it to build the
    -- type of the case block. But (TODO) consider delaying on failure?
    checkConcrete : NF vs -> Core ()
    checkConcrete (NApp _ (NMeta n i _) _)
        = throw (GenericMsg (getFC scr) "Can't infer type for case scrutinee")
    checkConcrete _ = pure ()

