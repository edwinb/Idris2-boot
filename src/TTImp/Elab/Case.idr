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
import TTImp.Elab.Delayed
import TTImp.Elab.ImplicitBind
import TTImp.TTImp
import TTImp.Utils

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
changeVar old new (As fc s nm p)
    = As fc s (changeVar old new nm) (changeVar old new p)
changeVar old new (TDelayed fc r p)
    = TDelayed fc r (changeVar old new p)
changeVar old new (TDelay fc r t p)
    = TDelay fc r (changeVar old new t) (changeVar old new p)
changeVar old new (TForce fc r p)
    = TForce fc r (changeVar old new p)
changeVar old new tm = tm

findLater : (x : Name) -> (newer : List Name) -> Var (newer ++ x :: older)
findLater x [] = MkVar First
findLater {older} x (_ :: xs)
    = let MkVar p = findLater {older} x xs in
          MkVar (Later p)

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

findScrutinee : Env Term vs -> RawImp -> Maybe (Var vs)
findScrutinee {vs = n' :: _} (b :: bs) (IVar loc' n)
    = if n' == n && notLet b
         then Just (MkVar First)
         else do MkVar p <- findScrutinee bs (IVar loc' n)
                 Just (MkVar (Later p))
  where
    notLet : Binder t -> Bool
    notLet (Let _ _ _) = False
    notLet _ = True
findScrutinee _ _ = Nothing

getNestData : (Name, (Maybe Name, List Name, a)) ->
              (Name, Maybe Name, List Name)
getNestData (n, (mn, enames, _)) = (n, mn, enames)

bindCaseLocals : FC -> List (Name, Maybe Name, List Name) ->
                 List (Name, Name)-> RawImp -> RawImp
bindCaseLocals fc [] args rhs = rhs
bindCaseLocals fc ((n, mn, envns) :: rest) argns rhs
    = --trace ("Case local " ++ show (renvns ++ " from " ++ show argns) $
        ICaseLocal fc n (fromMaybe n mn)
                 (map getNameFrom (reverse envns))
                 (bindCaseLocals fc rest argns rhs)
  where
    getNameFrom : Name -> Name
    getNameFrom n
        = case lookup n argns of
               Nothing => n
               Just n' => n'

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
         fullImps <- getToBind fc (elabMode elabinfo)
                               (implicitMode elabinfo) env []
         log 5 $ "Doing a case under unbound implicits " ++ show fullImps

         scrn <- genVarName "scr"
         casen <- genCaseName (defining est)

         -- Update environment so that linear bindings which were used
         -- (esp. in the scrutinee!) are set to 0 in the case type
         let env = updateMults (linearUsed est) env
         defs <- get Ctxt

         -- if the scrutinee is ones of the arguments in 'env' we should
         -- split on that, rather than adding it as a new argument
         let splitOn = findScrutinee env scr

         caseretty_in <- the (Core (Term vars)) $ case expected of
                           Just ty => getTerm ty
                           _ =>
                              do nmty <- genName "caseTy"
                                 metaVar fc Rig0 env nmty (TType fc)

         (caseretty, _) <- bindImplicits fc (implicitMode elabinfo) defs env
                                         fullImps caseretty_in (TType fc)
         let casefnty
               = abstractFullEnvType fc (allow splitOn env)
                            (maybe (Bind fc scrn (Pi caseRig Explicit scrty)
                                       (weaken caseretty))
                                   (const caseretty) splitOn)

         logEnv 10 "Case env" env
         logTermNF 2 ("Case function type: " ++ show casen) [] casefnty

         -- If we've had to add implicits to the case type (because there
         -- were unbound implicits) then we're in a bit of a mess. Easiest
         -- way out is to throw an error and try again with the implicits
         -- actually bound! This is rather hacky, but a lot less fiddly than
         -- the alternative of fixing up the environment
         when (not (isNil fullImps)) $ findImpsIn fc [] [] casefnty
         cidx <- addDef casen (newDef fc casen (if rigc == Rig0 then Rig0 else RigW)
                                      [] casefnty Private None)
         let caseRef : Term vars = Ref fc Func (Resolved cidx)

         -- If there's no duplication of the scrutinee in the block,
         -- inline it.
         -- This will be the case either if the scrutinee is a variable, in
         -- which case the duplication won't hurt, or if (TODO) none of the
         -- case patterns in alts are just a variable
         maybe (pure ()) (const (setFlag fc casen Inline)) splitOn

         let applyEnv = applyToFull fc caseRef env
         let appTm : Term vars
                   = maybe (App fc applyEnv scrtm)
                           (const applyEnv)
                           splitOn

         let alts' = map (updateClause casen splitOn nest env) alts
         log 2 $ "Nested: " ++ show (map getNestData (names nest))
         log 2 $ "Generated alts: " ++ show alts'
         logTermNF 2 "Case application" env appTm

         -- Start with empty nested names, since we've extended the rhs with
         -- ICaseLocal so they'll get rebuilt with the right environment
         let nest' = MkNested []
         processDecl [InCase] nest' [] (IDef fc casen alts')

         pure (appTm, gnf env caseretty)
  where
    mkLocalEnv : Env Term vs -> Env Term vs
    mkLocalEnv [] = []
    mkLocalEnv (b :: bs)
        = let b' = if isLinear (multiplicity b)
                      then setMultiplicity b Rig0
                      else b in
              b' :: mkLocalEnv bs

    -- Return the original name in the environment, and what it needs to be
    -- called in the case block. We need to mapping to build the ICaseLocal
    -- so that it applies to the right original variable
    getBindName : Int -> Name -> List Name -> (Name, Name)
    getBindName idx n@(UN un) vs
       = if n `elem` vs then (n, MN un idx) else (n, n)
    getBindName idx n vs
       = if n `elem` vs then (n, MN "_cn" idx) else (n, n)

    -- Returns a list of names that nestednames should be applied to, mapped
    -- to what the name has become in the case block, and a list of terms for
    -- the LHS of the case to be applied to.
    addEnv : Int -> Env Term vs -> List Name -> (List (Name, Name), List RawImp)
    addEnv idx [] used = ([], [])
    addEnv idx {vs = v :: vs} (b :: bs) used
        = let n = getBindName idx v used
              (ns, rest) = addEnv (idx + 1) bs (snd n :: used)
              ns' = n :: ns in
              (ns', IAs fc UseLeft (snd n) (Implicit fc True) :: rest)

    -- Replace a variable in the argument list; if the reference is to
    -- a variable kept in the outer environment (therefore not an argument
    -- in the list) don't consume it
    replace : (idx : Nat) -> RawImp -> List RawImp -> List RawImp
    replace Z lhs (old :: xs)
       = let lhs' = case old of
                         IAs loc' side n _ => IAs loc' side n lhs
                         _ => lhs in
             lhs' :: xs
    replace (S k) lhs (x :: xs)
        = x :: replace k lhs xs
    replace _ _ xs = xs

    mkSplit : Maybe (Var vs) ->
              RawImp -> List RawImp ->
              List RawImp
    mkSplit Nothing lhs args = reverse (lhs :: args)
    mkSplit (Just (MkVar {i} prf)) lhs args
        = reverse (replace i lhs args)

    -- Names used in the pattern we're matching on, so don't bind them
    -- in the generated case block
    usedIn : RawImp -> List Name
    usedIn (IBindVar _ n) = [UN n]
    usedIn (IApp _ f a) = usedIn f ++ usedIn a
    usedIn (IAs _ _ n a) = n :: usedIn a
    usedIn (IAlternative _ _ alts) = concatMap usedIn alts
    usedIn _ = []

    -- Get a name update for the LHS (so that if there's a nested data declaration
    -- the constructors are applied to the environment in the case block)
    nestLHS : FC -> (Name, (Maybe Name, List Name, a)) -> (Name, RawImp)
    nestLHS fc (n, (mn, ns, t))
        = (n, apply (IVar fc (fromMaybe n mn))
                    (map (const (Implicit fc False)) ns))

    applyNested : NestedNames vars -> RawImp -> RawImp
    applyNested nest lhs
        = let fc = getFC lhs in
              substNames [] (map (nestLHS fc) (names nest)) lhs

    updateClause : Name -> Maybe (Var vars) ->
                   NestedNames vars ->
                   Env Term vars -> ImpClause -> ImpClause
    updateClause casen splitOn nest env (PatClause loc' lhs rhs)
        = let (ns, args) = addEnv 0 env (usedIn lhs)
              args' = mkSplit splitOn lhs args
              lhs' = apply (IVar loc' casen) args' in
              PatClause loc' (applyNested nest lhs')
                        (bindCaseLocals loc' (map getNestData (names nest))
                                        (reverse ns) rhs)
    -- With isn't allowed in a case block but include for completeness
    updateClause casen splitOn nest env (WithClause loc' lhs wval cs)
        = let (_, args) = addEnv 0 env (usedIn lhs)
              args' = mkSplit splitOn lhs args
              lhs' = apply (IVar loc' casen) args' in
              WithClause loc' (applyNested nest lhs') wval cs
    updateClause casen splitOn nest env (ImpossibleClause loc' lhs)
        = let (_, args) = addEnv 0 env (usedIn lhs)
              args' = mkSplit splitOn lhs args
              lhs' = apply (IVar loc' casen) args' in
              ImpossibleClause loc' (applyNested nest lhs')


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
checkCase rig elabinfo nest env fc scr scrty_in alts exp
    = delayElab fc rig env exp 0 $
        do scrty_exp <- case scrty_in of
                             Implicit _ _ => guessScrType alts
                             _ => pure scrty_in
           (scrtyv, scrtyt) <- check Rig0 elabinfo nest env scrty_exp
                                     (Just (gType fc))
           logTerm 10 "Expected scrutinee type" scrtyv
           -- Try checking at the given multiplicity; if that doesn't work,
           -- try checking at Rig1 (meaning that we're using a linear variable
           -- so the scrutinee should be linear)
           let chrig = case rig of
                            Rig0 => Rig0
                            _ => RigW
           log 5 $ "Checking " ++ show scr ++ " at " ++ show chrig

           (scrtm_in, gscrty, caseRig) <- handle
              (do c <- runDelays 10 $ check chrig elabinfo nest env scr (Just (gnf env scrtyv))
                  pure (fst c, snd c, chrig))
              (\err => case err of
                            LinearMisuse _ _ Rig1 _
                              => do c <- runDelays 10 $ check Rig1 elabinfo nest env scr
                                               (Just (gnf env scrtyv))
                                    pure (fst c, snd c, Rig1)
                            e => throw e)

           scrty <- getTerm gscrty
           logTermNF 5 "Scrutinee type" env scrty
           defs <- get Ctxt
           checkConcrete !(nf defs env scrty)
           caseBlock rig elabinfo fc nest env scr scrtm_in scrty caseRig alts exp
  where
    -- For the moment, throw an error if we haven't been able to work out
    -- the type of the case scrutinee, because we'll need it to build the
    -- type of the case block. But (TODO) consider delaying on failure?
    checkConcrete : NF vs -> Core ()
    checkConcrete (NApp _ (NMeta n i _) _)
        = throw (GenericMsg (getFC scr) "Can't infer type for case scrutinee")
    checkConcrete _ = pure ()

    applyTo : Defs -> RawImp -> NF [] -> Core RawImp
    applyTo defs ty (NBind fc _ (Pi _ Explicit _) sc)
        = applyTo defs (IApp fc ty (Implicit fc False))
               !(sc defs (toClosure defaultOpts [] (Erased fc False)))
    applyTo defs ty (NBind _ x (Pi _ _ _) sc)
        = applyTo defs (IImplicitApp fc ty (Just x) (Implicit fc False))
               !(sc defs (toClosure defaultOpts [] (Erased fc False)))
    applyTo defs ty _ = pure ty

    -- Get the name and type of the family the scrutinee is in
    getRetTy : Defs -> NF [] -> Core (Maybe (Name, NF []))
    getRetTy defs (NBind fc _ (Pi _ _ _) sc)
        = getRetTy defs !(sc defs (toClosure defaultOpts [] (Erased fc False)))
    getRetTy defs (NTCon _ n _ arity _)
        = do Just ty <- lookupTyExact n (gamma defs)
                  | Nothing => pure Nothing
             pure (Just (n, !(nf defs [] ty)))
    getRetTy _ _ = pure Nothing

    -- Guess a scrutinee type by looking at the alternatives, so that we
    -- have a hint for building the case type
    guessScrType : List ImpClause -> Core RawImp
    guessScrType [] = pure $ Implicit fc False
    guessScrType (PatClause _ x _ :: xs)
        = case getFn x of
               IVar _ n =>
                  do defs <- get Ctxt
                     [(n', (_, ty))] <- lookupTyName n (gamma defs)
                         | _ => guessScrType xs
                     Just (tyn, tyty) <- getRetTy defs !(nf defs [] ty)
                         | _ => guessScrType xs
                     applyTo defs (IVar fc tyn) tyty
               _ => guessScrType xs
    guessScrType (_ :: xs) = guessScrType xs
