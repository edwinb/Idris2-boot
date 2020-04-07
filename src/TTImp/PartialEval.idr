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

unload : List (FC, Term vars) -> Term vars -> Term vars
unload [] fn = fn
unload ((fc, arg) :: args) fn = unload args (App fc fn arg)

specialiseTy : Nat -> List (Nat, Term []) -> Term vars -> Term vars
specialiseTy i specs (Bind fc x (Pi c p ty) sc)
    = case lookup i specs of
           Nothing => Bind fc x (Pi c p ty) $
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

specialisePat : List (Nat, Term []) ->
                (vs ** (Env Term vs, Term vs, Term vs)) ->
                Maybe (vs ** (Env Term vs, Term vs, Term vs))
specialisePat specs (vs ** (env, lhs, rhs))
    = do let (fn, args) = getFnArgs lhs
         psubs <- mkSubsts 0 specs args rhs
         let lhs' = apply (getLoc fn) fn args
         pure (vs ** (env, substLocs psubs lhs', substLocs psubs rhs))

specialisePats : List (Nat, Term []) ->
                 List (vs ** (Env Term vs, Term vs, Term vs)) ->
                 Maybe (List (vs ** (Env Term vs, Term vs, Term vs)))
specialisePats specs [] = pure []
specialisePats specs (p :: ps)
    = do p' <- specialisePat specs p
         ps' <- specialisePats specs ps
         pure (p' :: ps')

mkSpecDef : {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            FC -> Env Term vars -> GlobalDef ->
            Name -> List (Nat, Term []) -> Name -> List (FC, Term vars) ->
            Core (Term vars)
mkSpecDef {vars} fc env gdef pename sargs fn stk
    = do defs <- get Ctxt
         let peapp = unload (dropSpec 0 stk) (Ref fc Func pename)
         Nothing <- lookupCtxtExact pename (gamma defs)
             | Just _ => -- already specialised
                         pure peapp
         logC 3 (do fnfull <- toFullNames fn
                    args' <- traverse (\ (i, arg) =>
                                 do arg' <- toFullNames arg
                                    pure (show (i, arg'))) sargs
                    pure $ "Specialising " ++ show fnfull ++ " by " ++
                           showSep ", " args')
         let sty = specialiseTy 0 sargs (type gdef)
         logTermNF 3 ("Specialised type " ++ show pename) [] sty

         -- Add as RigW - if it's something else, we don't need it at
         -- runtime anyway so this is wasted effort, therefore a failure
         -- is okay!
         peidx <- addDef pename (newDef fc pename RigW [] sty Public None)
         addToSave (Resolved peidx)

         let PMDef pminfo pmargs ct tr pats = definition gdef
             | _ => pure (unload stk (Ref fc Func fn))
         let Just specpats = specialisePats sargs pats
             | _ => pure (unload stk (Ref fc Func fn))
         newpats <- traverse (unelabPat pename) specpats

         log 5 $ "New patterns for " ++ show pename ++ ":\n" ++
                  showSep "\n" (map showPat newpats)

         processDecl [] (MkNested []) [] (IDef fc (Resolved peidx) newpats)
         pure peapp
  where
    dropSpec : Nat -> List a -> List a
    dropSpec i [] = []
    dropSpec i (x :: xs)
        = case lookup i sargs of
               Nothing => x :: dropSpec (1 + i) xs
               Just _ => dropSpec (1 + i) xs

    updateApp : Name -> RawImp -> RawImp
    updateApp n (IApp fc f a) = IApp fc (updateApp n f) a
    updateApp n (IImplicitApp fc f m a) = IImplicitApp fc (updateApp n f) m a
    updateApp n f = IVar fc n

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
    dropArgs pename tm = reapply (IVar fc pename) (dropSpec 0 (getRawArgs [] tm))

    unelabPat : Name -> (vs ** (Env Term vs, Term vs, Term vs)) ->
                Core ImpClause
    unelabPat pename (_ ** (env, lhs, rhs))
        = do lhsapp <- unelabNoSugar env lhs
             let lhs' = dropArgs pename lhsapp
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
               sargs <- getSpecArgs 0 specs stk
               -- If all the arguments are concrete (meaning, no local variables
               -- or holes in them, so they can be a Term []) we can specialise
               let Just sargs = allConcrete sargs
                   | Nothing => pure (unload stk (Ref fc Func fn))
               let hash = hash (map snd sargs)
               let pename = NS ["_PE"]
                            (UN ("PE_" ++ nameRoot fnfull ++ "_" ++ asHex hash))
               mkSpecDef fc env gdef pename sargs fn stk
  where
    getSpecArgs : Nat -> List Nat -> List (FC, Term vars) ->
                  Core (List (Nat, Term vars))
    getSpecArgs i specs [] = pure []
    getSpecArgs i specs ((_, x) :: xs)
        = if i `elem` specs
             then do defs <- get Ctxt
                     x' <- normaliseHoles defs env x
                     pure $ (i, x') :: !(getSpecArgs (1 + i) specs xs)
             else getSpecArgs (1 + i) specs xs

    dropAll : {vs : _} -> SubVars [] vs
    dropAll {vs = []} = SubRefl
    dropAll {vs = v :: vs} = DropCons dropAll

    concrete : Term vars -> Maybe (Term [])
    concrete tm = shrinkTerm tm dropAll

    allConcrete : List (Nat, Term vars) -> Maybe (List (Nat, Term []))
    allConcrete [] = pure []
    allConcrete ((i, tm) :: ts)
        = do tm' <- concrete tm
             ts' <- allConcrete ts
             pure ((i, tm') :: ts')

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
