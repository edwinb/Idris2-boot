module TTImp.PartialEval

import Core.CaseTree
import Core.Context
import Core.Core
import Core.Env
import Core.Hash
import Core.Metadata
import Core.Normalise
import Core.Value
import Core.UnifyState

import TTImp.Elab.Check
import TTImp.TTImp
import TTImp.Unelab

import Utils.Hex

%default covering

data ArgMode = Static (Term []) | Dynamic

Show ArgMode where
  show (Static tm) = "Static " ++ show tm
  show Dynamic = "Dynamic"

getStatic : ArgMode -> Maybe (Term [])
getStatic Dynamic = Nothing
getStatic (Static t) = Just t

unload : List (FC, Term vars) -> Term vars -> Term vars
unload [] fn = fn
unload ((fc, arg) :: args) fn = unload args (App fc fn arg)

specialiseTy : Nat -> List (Nat, Term []) -> Term vars -> Term vars
specialiseTy i specs (Bind fc x (Pi c p ty) sc)
    = case lookup i specs of
           Nothing => Bind fc x (Pi c Explicit ty) $ -- easier later if everything explicit
                        specialiseTy (1 + i) specs sc
           Just tm => specialiseTy (1 + i) specs (subst (embed tm) sc)
specialiseTy i specs tm = tm

substLoc : Nat -> Term vs -> Term vs -> Term vs
substLoc i tm (Local fc l idx p)
    = if i == idx then tm else (Local fc l idx p)
substLoc i tm (Bind fc x b sc)
    = Bind fc x (map (substLoc i tm) b) (substLoc (1 + i) (weaken tm) sc)
substLoc i tm (Meta fc n r args)
    = Meta fc n r (map (substLoc i tm) args)
substLoc i tm (App fc f a) = App fc (substLoc i tm f) (substLoc i tm a)
substLoc i tm (As fc s f a) = As fc s (substLoc i tm f) (substLoc i tm a)
substLoc i tm (TDelayed fc r d) = TDelayed fc r (substLoc i tm d)
substLoc i tm (TDelay fc r ty d) = TDelay fc r (substLoc i tm ty) (substLoc i tm d)
substLoc i tm (TForce fc r d) = TForce fc r (substLoc i tm d)
substLoc i tm x = x

substLocs : List (Nat, Term vs) -> Term vs -> Term vs
substLocs [] tm = tm
substLocs ((i, tm') :: subs) tm = substLocs subs (substLoc i tm' tm)

mkSubsts : Nat -> List (Nat, Term []) ->
           List (Term vs) -> Term vs -> Maybe (List (Nat, Term vs))
mkSubsts i specs [] rhs = Just []
mkSubsts i specs (arg :: args) rhs
    = do subs <- mkSubsts (1 + i) specs args rhs
         case lookup i specs of
              Nothing => Just subs
              Just tm => case arg of
                              Local _ _ idx _ =>
                                   Just ((idx, embed tm) :: subs)
                              As _ _ (Local _ _ idx1 _) (Local _ _ idx2 _) =>
                                   Just ((idx1, embed tm) :: (idx2, embed tm) :: subs)
                              As _ _ _ (Local _ _ idx _) =>
                                   Just ((idx, embed tm) :: subs)
                              _ => Nothing

-- In the case where all the specialised positions are variables on the LHS,
-- substitute the term in on the RHS
specPatByVar : List (Nat, Term []) ->
                (vs ** (Env Term vs, Term vs, Term vs)) ->
                Maybe (vs ** (Env Term vs, Term vs, Term vs))
specPatByVar specs (vs ** (env, lhs, rhs))
    = do let (fn, args) = getFnArgs lhs
         psubs <- mkSubsts 0 specs args rhs
         let lhs' = apply (getLoc fn) fn args
         pure (vs ** (env, substLocs psubs lhs', substLocs psubs rhs))

specByVar : List (Nat, Term []) ->
            List (vs ** (Env Term vs, Term vs, Term vs)) ->
            Maybe (List (vs ** (Env Term vs, Term vs, Term vs)))
specByVar specs [] = pure []
specByVar specs (p :: ps)
    = do p' <- specPatByVar specs p
         ps' <- specByVar specs ps
         pure (p' :: ps')

dropSpec : Nat -> List (Nat, Term []) -> List a -> List a
dropSpec i sargs [] = []
dropSpec i sargs (x :: xs)
    = case lookup i sargs of
           Nothing => x :: dropSpec (1 + i) sargs xs
           Just _ => dropSpec (1 + i) sargs xs

getSpecPats : {auto c : Ref Ctxt Defs} ->
              FC -> Name ->
              Env Term vars -> (fn : Name) -> (stk : List (FC, Term vars)) ->
              NF [] -> -- Type of 'fn'
              List (Nat, ArgMode) -> -- All the arguments
              List (Nat, Term []) -> -- Just the static ones
              List (vs ** (Env Term vs, Term vs, Term vs)) ->
              Core (Maybe (List ImpClause))
getSpecPats fc pename env fn stk fnty args sargs pats
   = do -- First, see if all the specialised positions are variables. If so,
        -- substitute the arguments directly into the RHS
        let Nothing = specByVar sargs pats
            | Just specpats =>
                   do ps <- traverse (unelabPat pename) specpats
                      pure (Just ps)
        -- Otherwise, build a new definition by taking the remaining arguments
        -- on the lhs, and using the specialised function application on the rhs.
        -- Then, this will get evaluated on elaboration.
        let dynnames = mkDynNames 0 args
        let lhs = apply (IVar fc pename) (map (IBindVar fc) dynnames)
        rhs <- mkRHSargs fnty (IVar fc fn) dynnames args
        pure (Just [PatClause fc lhs rhs])
  where
    mkDynNames : Int -> List (Nat, ArgMode) -> List String
    mkDynNames i [] = []
    mkDynNames i ((_, Dynamic) :: as)
        = ("_pe" ++ show i) :: mkDynNames (1 + i) as
    mkDynNames i (_ :: as) = mkDynNames i as

    -- Build a RHS from the type of the function to be specialised, the
    -- dynamic argument names, and the list of given arguments. We assume
    -- the latter two correspond appropriately.
    mkRHSargs : NF [] -> RawImp -> List String -> List (Nat, ArgMode) ->
                Core RawImp
    mkRHSargs (NBind _ x (Pi _ Explicit _) sc) app (a :: as) ((_, Dynamic) :: ds)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts [] (Erased fc False))
             mkRHSargs sc' (IApp fc app (IVar fc (UN a))) as ds
    mkRHSargs (NBind _ x (Pi _ _ _) sc) app (a :: as) ((_, Dynamic) :: ds)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts [] (Erased fc False))
             mkRHSargs sc' (IImplicitApp fc app (Just x) (IVar fc (UN a))) as ds
    mkRHSargs (NBind _ x (Pi _ Explicit _) sc) app as ((_, Static tm) :: ds)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts [] (Erased fc False))
             tm' <- unelabNoSugar [] tm
             mkRHSargs sc' (IApp fc app tm') as ds
    mkRHSargs (NBind _ x (Pi _ _ _) sc) app as ((_, Static tm) :: ds)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts [] (Erased fc False))
             tm' <- unelabNoSugar [] tm
             mkRHSargs sc' (IImplicitApp fc app (Just x) tm') as ds
    mkRHSargs _ app _ _ = pure app

    getRawArgs : List (Maybe Name, RawImp) -> RawImp -> List (Maybe Name, RawImp)
    getRawArgs args (IApp _ f arg) = getRawArgs ((Nothing, arg) :: args) f
    getRawArgs args (IImplicitApp _ f (Just n) arg)
        = getRawArgs ((Just n, arg) :: args) f
    getRawArgs args tm = args

    reapply : RawImp -> List (Maybe Name, RawImp) -> RawImp
    reapply f [] = f
    reapply f ((Nothing, arg) :: args) = reapply (IApp fc f arg) args
    reapply f ((Just t, arg) :: args)
        = reapply (IImplicitApp fc f (Just t) arg) args

    dropArgs : Name -> RawImp -> RawImp
    dropArgs pename tm = reapply (IVar fc pename) (dropSpec 0 sargs (getRawArgs [] tm))

    unelabPat : Name -> (vs ** (Env Term vs, Term vs, Term vs)) ->
                Core ImpClause
    unelabPat pename (_ ** (env, lhs, rhs))
        = do lhsapp <- unelabNoSugar env lhs
             let lhs' = dropArgs pename lhsapp
             defs <- get Ctxt
             rhsnf <- normaliseArgHoles defs env rhs
             rhs' <- unelabNoSugar env rhsnf
             pure (PatClause fc lhs' rhs')

    unelabLHS : Name -> (vs ** (Env Term vs, Term vs, Term vs)) ->
                Core RawImp
    unelabLHS pename (_ ** (env, lhs, rhs))
        = do lhsapp <- unelabNoSugar env lhs
             pure $ dropArgs pename lhsapp

mkSpecDef : {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            FC -> Env Term vars -> GlobalDef ->
            Name -> List (Nat, ArgMode) -> Name -> List (FC, Term vars) ->
            Core (Term vars)
mkSpecDef {vars} fc env gdef pename sargs fn stk
    = do defs <- get Ctxt
         let staticargs
               = mapMaybe (\ (x, s) => case s of
                                            Dynamic => Nothing
                                            Static t => Just (x, t)) sargs
         let peapp = unload (dropSpec 0 staticargs stk) (Ref fc Func pename)
         Nothing <- lookupCtxtExact pename (gamma defs)
             | Just _ => -- already specialised
                         pure peapp
         logC 0 (do fnfull <- toFullNames fn
                    args' <- traverse (\ (i, arg) =>
                                 do arg' <- the (Core ArgMode) $ case arg of
                                                 Static a =>
                                                    pure $ Static !(toFullNames a)
                                                 Dynamic => pure Dynamic
                                    pure (show (i, arg'))) sargs
                    pure $ "Specialising " ++ show fnfull ++ " by " ++
                           showSep ", " args')
         let sty = specialiseTy 0 staticargs (type gdef)
         logTermNF 0 ("Specialised type " ++ show pename) [] sty

         -- Add as RigW - if it's something else, we don't need it at
         -- runtime anyway so this is wasted effort, therefore a failure
         -- is okay!
         peidx <- addDef pename (newDef fc pename top [] sty Public None)
         addToSave (Resolved peidx)
         let PMDef pminfo pmargs ct tr pats = definition gdef
             | _ => pure (unload stk (Ref fc Func fn))
         logC 0 (do inpats <- traverse unelabDef pats
                    pure $ "Attempting to specialise:\n" ++
                           showSep "\n" (map showPat inpats))

         Just newpats <- getSpecPats fc pename env fn stk !(nf defs [] (type gdef))
                                     sargs staticargs pats
              | Nothing => pure (unload stk (Ref fc Func fn))
         log 0 $ "New patterns for " ++ show pename ++ ":\n" ++
                  showSep "\n" (map showPat newpats)

         processDecl [] (MkNested []) [] (IDef fc (Resolved peidx) newpats)
         pure peapp
  where
    updateApp : Name -> RawImp -> RawImp
    updateApp n (IApp fc f a) = IApp fc (updateApp n f) a
    updateApp n (IImplicitApp fc f m a) = IImplicitApp fc (updateApp n f) m a
    updateApp n f = IVar fc n

    unelabDef : (vs ** (Env Term vs, Term vs, Term vs)) ->
                Core ImpClause
    unelabDef (_ ** (env, lhs, rhs))
        = do lhs' <- unelabNoSugar env lhs
             defs <- get Ctxt
             rhsnf <- normaliseArgHoles defs env rhs
             rhs' <- unelabNoSugar env rhsnf
             pure (PatClause fc lhs' rhs')

    showPat : ImpClause -> String
    showPat (PatClause _ lhs rhs) = show lhs ++ " = " ++ show rhs
    showPat _ = "Can't happen"

specialise : {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             FC -> Env Term vars -> GlobalDef ->
             Name -> List (FC, Term vars) ->
             Core (Term vars)
specialise {vars} fc env gdef fn stk
    = case specArgs gdef of
        [] => pure $ unload stk (Ref fc Func fn)
        specs =>
            do fnfull <- toFullNames fn
               -- If all the arguments are concrete (meaning, no local variables
               -- or holes in them, so they can be a Term []) we can specialise
               Just sargs <- getSpecArgs 0 specs stk
                   | Nothing => pure (unload stk (Ref fc Func fn))
               let nhash = hash (mapMaybe getStatic (map snd sargs))
               let pename = NS ["_PE"]
                            (UN ("PE_" ++ nameRoot fnfull ++ "_" ++ asHex nhash))
               mkSpecDef fc env gdef pename sargs fn stk
  where
    dropAll : {vs : _} -> SubVars [] vs
    dropAll {vs = []} = SubRefl
    dropAll {vs = v :: vs} = DropCons dropAll

    concrete : Term vars -> Maybe (Term [])
    concrete tm = shrinkTerm tm dropAll

    getSpecArgs : Nat -> List Nat -> List (FC, Term vars) ->
                  Core (Maybe (List (Nat, ArgMode)))
    getSpecArgs i specs [] = pure (Just [])
    getSpecArgs i specs ((_, x) :: xs)
        = do Just xs' <- getSpecArgs (1 + i) specs xs
                 | Nothing => pure Nothing
             if i `elem` specs
                then do defs <- get Ctxt
                        x' <- normaliseHoles defs env x
                        let Just xok = concrete x'
                            | Nothing => pure Nothing
                        pure $ Just ((i, Static xok) :: xs')
                else pure $ Just ((i, Dynamic) :: xs')

findSpecs : {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            Env Term vars -> List (FC, Term vars) -> Term vars ->
            Core (Term vars)
findSpecs env stk (Ref fc Func fn)
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact fn (gamma defs)
              | Nothing => pure (unload stk (Ref fc Func fn))
         specialise fc env gdef fn stk
findSpecs env stk (Meta fc n i args)
    = do args' <- traverse (findSpecs env []) args
         pure $ unload stk (Meta fc n i args')
findSpecs env stk (Bind fc x b sc)
    = do b' <- traverse (findSpecs env []) b
         sc' <- findSpecs (b' :: env) [] sc
         pure $ unload stk (Bind fc x b' sc')
findSpecs env stk (App fc fn arg)
    = do arg' <- findSpecs env [] arg
         findSpecs env ((fc, arg') :: stk) fn
findSpecs env stk (TDelayed fc r tm)
    = do tm' <- findSpecs env [] tm
         pure $ unload stk (TDelayed fc r tm')
findSpecs env stk (TDelay fc r ty tm)
    = do ty' <- findSpecs env [] ty
         tm' <- findSpecs env [] tm
         pure $ unload stk (TDelay fc r ty' tm')
findSpecs env stk (TForce fc r tm)
    = do tm' <- findSpecs env [] tm
         pure $ unload stk (TForce fc r tm')
findSpecs env stk tm = pure $ unload stk tm

export
applySpecialise : {auto c : Ref Ctxt Defs} ->
                  {auto m : Ref MD Metadata} ->
                  {auto u : Ref UST UState} ->
                  Env Term vars -> Term vars ->
                  Core (Term vars)
applySpecialise env tm
    = findSpecs env [] tm
