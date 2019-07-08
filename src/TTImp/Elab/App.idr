module TTImp.Elab.App

import Core.CaseTree
import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.TTImp

%default covering

-- Get the type of a variable, assuming we haven't found it in the nested
-- names. Look in the Env first, then the global context.
getNameType : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto e : Ref EST (EState vars)} ->
              RigCount -> Env Term vars ->
              FC -> Name ->
              Core (Term vars, Glued vars)
getNameType rigc env fc x
    = case defined x env of
           Just (MkIsDefined rigb lv) => 
              do rigSafe rigb rigc
                 let binder = getBinder lv env
                 let bty = binderType binder
                 addNameType fc x env bty
                 when (isLinear rigb) $
                      do est <- get EST
                         put EST 
                            (record { linearUsed $= ((MkVar lv) :: ) } est)
                 pure (Local fc (Just (isLet binder)) _ lv, gnf env bty)
           Nothing => 
              do defs <- get Ctxt
                 [(pname, i, def)] <- lookupCtxtName x (gamma defs)
                      | [] => throw (UndefinedName fc x)
                      | ns => throw (AmbiguousName fc (map fst ns))
                 checkVisibleNS !(getFullName pname) (visibility def)
                 let nt = case definition def of
                               PMDef _ _ _ _ _ => Func
                               DCon t a => DataCon t a
                               TCon t a _ _ _ _ => TyCon t a
                               _ => Func
                 addNameType fc x env (embed (type def))
                 pure (Ref fc nt (Resolved i), gnf env (embed (type def)))
  where
    isLet : Binder t -> Bool
    isLet (Let _ _ _) = True
    isLet _ = False

    rigSafe : RigCount -> RigCount -> Core ()
    rigSafe Rig1 RigW = throw (LinearMisuse fc x Rig1 RigW)
    rigSafe Rig0 RigW = throw (LinearMisuse fc x Rig0 RigW)
    rigSafe Rig0 Rig1 = throw (LinearMisuse fc x Rig0 Rig1)
    rigSafe _ _ = pure ()

    checkVisibleNS : Name -> Visibility -> Core ()
    checkVisibleNS (NS ns x) vis
        = if !(isVisible ns)
             then if visibleIn !getNS (NS ns x) vis
                     then pure ()
                     else throw $ InvisibleName fc (NS ns x) Nothing
             else throw $ InvisibleName fc (NS ns x) (Just ns)
    checkVisibleNS _ _ = pure ()
          

-- Get the type of a variable, looking it up in the nested names first.
getVarType : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto e : Ref EST (EState vars)} ->
             RigCount -> NestedNames vars -> Env Term vars ->
             FC -> Name ->
             Core (Term vars, Glued vars)
getVarType rigc nest env fc x
    = case lookup x (names nest) of
           Nothing => getNameType rigc env fc x
           Just (nestn, tmf) =>
              do defs <- get Ctxt
                 let n' = maybe x id nestn
                 case !(lookupCtxtExact n' (gamma defs)) of
                      Nothing => throw (UndefinedName fc n')
                      Just ndef =>
                         let nt = case definition ndef of
                                       PMDef _ _ _ _ _ => Func
                                       DCon t a => DataCon t a
                                       TCon t a _ _ _ _ => TyCon t a
                                       _ => Func
                             tm = tmf fc nt
                             tyenv = useVars (getArgs tm)
                                             (embed (type ndef)) in
                             do logTerm 10 ("Type of " ++ show n') tyenv
                                logTerm 10 ("Expands to") tm
                                pure (tm, gnf env tyenv)
    where
      useVars : List (Term vars) -> Term vars -> Term vars
      useVars [] sc = sc
      useVars (a :: as) (Bind bfc n (Pi c _ ty) sc) 
           = Bind bfc n (Let c a ty) (useVars (map weaken as) sc)
      useVars as (Bind bfc n (Let c v ty) sc) 
           = Bind bfc n (Let c v ty) (useVars (map weaken as) sc)
      useVars _ sc = sc -- Can't happen?

isHole : NF vars -> Bool
isHole (NApp _ (NMeta _ _ _) _) = True
isHole _ = False

-- Return whether we already know the return type of the given function
-- type. If we know this, we can possibly infer some argument types before
-- elaborating them, which might help us disambiguate things more easily.
concrete : Defs -> Env Term vars -> NF vars -> Core Bool
concrete defs env (NBind fc _ (Pi _ _ _) sc)
    = do sc' <- sc defs (toClosure defaultOpts env (Erased fc))
         concrete defs env sc'
concrete defs env (NDCon _ _ _ _ _) = pure True
concrete defs env (NTCon _ _ _ _ _) = pure True
concrete defs env (NPrimVal _ _) = pure True
concrete defs env _ = pure False

mutual
  makeImplicit : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 RigCount -> RigCount -> ElabInfo -> 
                 NestedNames vars -> Env Term vars -> 
                 FC -> (fntm : Term vars) -> 
                 Name -> NF vars -> (Defs -> Closure vars -> Core (NF vars)) ->
                 (expargs : List RawImp) ->
                 (impargs : List (Maybe Name, RawImp)) ->
                 (knownret : Bool) ->
                 (expected : Maybe (Glued vars)) ->
                 Core (Term vars, Glued vars)
  makeImplicit rig argRig elabinfo nest env fc tm x aty sc expargs impargs kr expty
      = do defs <- get Ctxt
           nm <- genMVName x
           empty <- clearDefs defs
           metaty <- quote empty env aty
           metaval <- metaVar fc argRig env nm metaty
           let fntm = App fc tm metaval
           fnty <- sc defs (toClosure defaultOpts env metaval)
           when (bindingVars elabinfo) $
                do est <- get EST
                   put EST (addBindIfUnsolved nm argRig Implicit env metaval metaty est)
           checkAppWith rig elabinfo nest env fc
                        fntm fnty expargs impargs kr expty

  makeAutoImplicit : {vars : _} ->
                     {auto c : Ref Ctxt Defs} ->
                     {auto m : Ref MD Metadata} ->
                     {auto u : Ref UST UState} ->
                     {auto e : Ref EST (EState vars)} ->
                     RigCount -> RigCount -> ElabInfo -> 
                     NestedNames vars -> Env Term vars -> 
                     FC -> (fntm : Term vars) -> 
                     Name -> NF vars -> (Defs -> Closure vars -> Core (NF vars)) ->
                     (expargs : List RawImp) ->
                     (impargs : List (Maybe Name, RawImp)) ->
                     (knownret : Bool) ->
                     (expected : Maybe (Glued vars)) ->
                     Core (Term vars, Glued vars)
  makeAutoImplicit rig argRig elabinfo nest env fc tm x aty sc expargs impargs kr expty
  -- on the LHS, just treat it as an implicit pattern variable.
  -- on the RHS, add a searchable hole
      = case elabMode elabinfo of
             InLHS _ => 
                do defs <- get Ctxt
                   nm <- genMVName x
                   empty <- clearDefs defs
                   metaty <- quote empty env aty
                   metaval <- metaVar fc argRig env nm metaty
                   let fntm = App fc tm metaval
                   fnty <- sc defs (toClosure defaultOpts env metaval)
                   est <- get EST
                   put EST (addBindIfUnsolved nm argRig AutoImplicit env metaval metaty est)
                   checkAppWith rig elabinfo nest env fc
                                fntm fnty expargs impargs kr expty
             _ =>
                do defs <- get Ctxt
                   nm <- genMVName x
                   empty <- clearDefs defs
                   metaty <- quote empty env aty
                   est <- get EST
                   metaval <- searchVar fc argRig 500 (Resolved (defining est))
                                        env nm metaty
                   let fntm = App fc tm metaval
                   fnty <- sc defs (toClosure defaultOpts env metaval)
                   checkAppWith rig elabinfo nest env fc
                                fntm fnty expargs impargs kr expty

  -- Defer elaborating anything which will be easier given a known target
  -- type (ambiguity, cases, etc)
  needsDelayExpr : {auto c : Ref Ctxt Defs} ->
                   (knownRet : Bool) -> RawImp ->
                   Core Bool
  needsDelayExpr False _ = pure False
  needsDelayExpr True (IVar fc n)
      = do defs <- get Ctxt
           case !(lookupCtxtName n (gamma defs)) of
                [] => pure False
                [x] => pure False
                _ => pure True
  needsDelayExpr True (IApp _ f _) = needsDelayExpr True f
  needsDelayExpr True (IImplicitApp _ f _ _) = needsDelayExpr True f
  needsDelayExpr True (ICase _ _ _ _) = pure True
  needsDelayExpr True (ILocal _ _ _) = pure True
  needsDelayExpr True (IUpdate _ _ _) = pure True
  needsDelayExpr True (IAlternative _ _ _) = pure True
  needsDelayExpr True (ISearch _ _) = pure True
  needsDelayExpr True (IRewrite _ _ _) = pure True
  needsDelayExpr True _ = pure False
  
  -- On the LHS, for any concrete thing, we need to make sure we know
  -- its type before we proceed so that we can reject it if the type turns
  -- out to be polymorphic
  needsDelayLHS : {auto c : Ref Ctxt Defs} ->
                  RawImp -> Core Bool
  needsDelayLHS (IVar fc n) = pure True
  needsDelayLHS (IApp _ f _) = needsDelayLHS f
  needsDelayLHS (IImplicitApp _ f _ _) = needsDelayLHS f
  needsDelayLHS (IAlternative _ _ _) = pure True
  needsDelayLHS (ISearch _ _) = pure True
  needsDelayLHS (IPrimVal _ _) = pure True
  needsDelayLHS (IType _) = pure True
  needsDelayLHS _ = pure False

  onLHS : ElabMode -> Bool
  onLHS (InLHS _) = True
  onLHS _ = False

  needsDelay : {auto c : Ref Ctxt Defs} ->
               ElabMode ->
               (knownRet : Bool) -> RawImp ->
               Core Bool
  needsDelay (InLHS _) _ tm = needsDelayLHS tm
  needsDelay _ kr tm = needsDelayExpr kr tm

  checkPatTyValid : {auto c : Ref Ctxt Defs} ->
                    FC -> Defs -> Env Term vars ->
                    NF vars -> Term vars -> Glued vars -> Core ()
  checkPatTyValid fc defs env (NApp _ (NMeta n i _) _) arg got
      = do Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
                | Nothing => pure ()
           case multiplicity gdef of
                Rig0 =>
                   do -- Argument is only valid if gotnf is not a concrete type
                      gotnf <- getNF got
                      if !(concrete defs env gotnf)
                         then throw (MatchTooSpecific fc env arg)
                         else pure ()
                _ => pure ()
  checkPatTyValid fc defs env _ _ _ = pure ()

  -- Check the rest of an application given the argument type and the
  -- raw argument. We choose elaboration order depending on whether we know
  -- the return type now. If we know it, elaborate the rest of the
  -- application first and come back to it, because that might infer types
  -- for implicit arguments, which might in turn help with type-directed
  -- disambiguation when elaborating the argument.
  checkRestApp : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 RigCount -> RigCount -> ElabInfo -> 
                 NestedNames vars -> Env Term vars -> 
                 FC -> (fntm : Term vars) -> Name ->
                 (aty : NF vars) -> (sc : Defs -> Closure vars -> Core (NF vars)) ->
                 (arg : RawImp) ->
                 (expargs : List RawImp) ->
                 (impargs : List (Maybe Name, RawImp)) ->
                 (knownret : Bool) ->
                 (expected : Maybe (Glued vars)) ->
                 Core (Term vars, Glued vars)
  checkRestApp rig argRig elabinfo nest env fc tm x aty sc
               arg expargs impargs knownret expty
     = do defs <- get Ctxt
          kr <- if knownret
                   then pure True
                   else do sc' <- sc defs (toClosure defaultOpts env (Erased fc))
                           concrete defs env sc'
          if !(needsDelay (elabMode elabinfo) kr arg) then do
             nm <- genMVName x
             empty <- clearDefs defs
             metaty <- quote empty env aty
             (idx, metaval) <- argVar (getFC arg) argRig env nm metaty
             let fntm = App fc tm metaval
             logNF 10 ("Delaying " ++ show nm ++ " " ++ show arg) env aty
             logTerm 10 "...as" metaval
             fnty <- sc defs (toClosure defaultOpts env metaval)
             (tm, gty) <- checkAppWith rig elabinfo nest env fc
                                       fntm fnty expargs impargs kr expty
             defs <- get Ctxt
             aty' <- nf defs env metaty
             logNF 10 ("Now trying " ++ show nm ++ " " ++ show arg) env aty'
             (argv, argt) <- check argRig elabinfo
                                   nest env arg (Just (glueBack defs env aty'))
             when (onLHS (elabMode elabinfo)) $
                  checkPatTyValid fc defs env aty' argv argt
             defs <- get Ctxt
             -- If we're on the LHS, reinstantiate it with 'argv' because it
             -- *may* have as patterns in it and we need to retain them.
             -- (As patterns are a bit of a hack but I don't yet see a 
             -- better way that leads to good code...)
             logTerm 5 ("Solving " ++ show metaval ++ " with") argv
             ok <- solveIfUndefined env metaval argv
             when (not ok) $
                do res <- convert fc elabinfo env (gnf env metaval)
                                                 (gnf env argv)
                   let [] = constraints res
                      | cs => throw (CantConvert fc env metaval argv)
                   pure ()
             case elabMode elabinfo of
                  InLHS _ => -- reset hole and redo it with the unexpanded definition
                     do updateDef (Resolved idx) (const (Just (Hole 0 False False)))
                        solveIfUndefined env metaval argv
                        pure ()
                  _ => pure ()
             removeHole idx
             pure (tm, gty)
           else do
             logNF 10 ("Argument type " ++ show x) env aty
             logNF 10 ("Full function type") env
                      (NBind fc x (Pi argRig Explicit aty) sc)
             logC 10 (do ety <- maybe (pure Nothing)
                                     (\t => pure (Just !(toFullNames!(getTerm t))))
                                     expty
                         pure ("Overall expected type: " ++ show ety))
             (argv, argt) <- check argRig elabinfo
                                   nest env arg (Just (glueBack defs env aty))
             logGlueNF 10 "Got arg type" env argt
             defs <- get Ctxt
             let fntm = App fc tm argv
             fnty <- sc defs (toClosure defaultOpts env argv)
             checkAppWith rig elabinfo nest env fc
                          fntm fnty expargs impargs kr expty

  -- Check an application of 'fntm', with type 'fnty' to the given list
  -- of explicit and implicit arguments.
  -- Returns the checked term and its (weakly) normalised type
  checkAppWith : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 RigCount -> ElabInfo -> 
                 NestedNames vars -> Env Term vars -> 
                 FC -> (fntm : Term vars) -> (fnty : NF vars) ->
                 (expargs : List RawImp) ->
                 (impargs : List (Maybe Name, RawImp)) ->
                 (knownret : Bool) -> -- Do we know what the return type is yet?
                              -- if we do, we might be able to use it to work 
                              -- out the types of arguments before elaborating them
                 (expected : Maybe (Glued vars)) ->
                 Core (Term vars, Glued vars)
  -- Ordinary explicit argument
  checkAppWith rig elabinfo nest env fc tm (NBind tfc x (Pi rigb Explicit aty) sc)
               (arg :: expargs) impargs kr expty 
      = do let argRig = rigMult rig rigb
           checkRestApp rig argRig elabinfo nest env fc 
                        tm x aty sc arg expargs impargs kr expty
  -- Function type is delayed, so force the term and continue
  checkAppWith rig elabinfo nest env fc tm (NDelayed dfc r ty) expargs impargs kr expty
      = checkAppWith rig elabinfo nest env fc (TForce dfc tm) ty expargs impargs kr expty
  -- If there's no more arguments given, and the plicities of the type and
  -- the expected type line up, stop
  checkAppWith rig elabinfo nest env fc tm ty@(NBind tfc x (Pi rigb Implicit aty) sc)
               [] [] kr (Just expty_in)
      = do let argRig = rigMult rig rigb
           expty <- getNF expty_in
           defs <- get Ctxt
           case expty of
                NBind tfc' x' (Pi rigb' Implicit aty') sc'
                   => checkExp rig elabinfo env fc tm (glueBack defs env ty) (Just expty_in)
                _ => makeImplicit rig argRig elabinfo nest env fc tm x aty sc [] [] kr (Just expty_in)
  checkAppWith rig elabinfo nest env fc tm ty@(NBind tfc x (Pi rigb AutoImplicit aty) sc)
               [] [] kr (Just expty_in)
      = do let argRig = rigMult rig rigb
           expty <- getNF expty_in
           defs <- get Ctxt
           case expty of
                NBind tfc' x' (Pi rigb' AutoImplicit aty') sc'
                   => checkExp rig elabinfo env fc tm (glueBack defs env ty) (Just expty_in)
                _ => makeAutoImplicit rig argRig elabinfo nest env fc tm x aty sc [] [] kr (Just expty_in)

  -- Check next auto implicit argument
  checkAppWith rig elabinfo nest env fc tm (NBind tfc x (Pi rigb AutoImplicit aty) sc)
               expargs impargs kr expty
      = let argRig = rigMult rig rigb in
            case useAutoImp [] impargs of
               Nothing => makeAutoImplicit rig argRig elabinfo nest env fc tm 
                                           x aty sc expargs impargs kr expty
               Just (arg, impargs') =>
                     checkRestApp rig argRig elabinfo nest env fc 
                                  tm x aty sc arg expargs impargs' kr expty
    where
      useAutoImp : List (Maybe Name, RawImp) -> List (Maybe Name, RawImp) ->
                   Maybe (RawImp, List (Maybe Name, RawImp))
      useAutoImp acc [] = Nothing
      useAutoImp acc ((Nothing, xtm) :: rest)
          = Just (xtm, reverse acc ++ rest)
      useAutoImp acc ((Just x', xtm) :: rest)
          = if x == x'
               then Just (xtm, reverse acc ++ rest)
               else useAutoImp ((Just x', xtm) :: acc) rest
      useAutoImp acc (ximp :: rest)
          = useAutoImp (ximp :: acc) rest
  -- Check next implicit argument
  checkAppWith rig elabinfo nest env fc tm (NBind tfc x (Pi rigb Implicit aty) sc)
               expargs impargs kr expty
      = let argRig = rigMult rig rigb in
            case useImp [] impargs of
               Nothing => makeImplicit rig argRig elabinfo nest env fc tm 
                                       x aty sc expargs impargs kr expty
               Just (arg, impargs') =>
                     checkRestApp rig argRig elabinfo nest env fc 
                                  tm x aty sc arg expargs impargs' kr expty
    where
      useImp : List (Maybe Name, RawImp) -> List (Maybe Name, RawImp) ->
               Maybe (RawImp, List (Maybe Name, RawImp))
      useImp acc [] = Nothing
      useImp acc ((Just x', xtm) :: rest)
          = if x == x'
               then Just (xtm, reverse acc ++ rest)
               else useImp ((Just x', xtm) :: acc) rest
      useImp acc (ximp :: rest)
          = useImp (ximp :: acc) rest

  checkAppWith rig elabinfo nest env fc tm ty [] [] kr expty 
      = do defs <- get Ctxt
           checkExp rig elabinfo env fc tm (glueBack defs env ty) expty
  checkAppWith rig elabinfo nest env fc tm ty [] impargs kr expty 
      = case filter notInfer impargs of
             [] => checkAppWith rig elabinfo nest env fc tm ty [] [] kr expty
             is => throw (InvalidImplicits fc env (map fst is) tm)
    where
      notInfer : (Maybe Name, RawImp) -> Bool
      notInfer (_, Implicit _ _) = False
      notInfer (n, IAs _ _ _ i) = notInfer (n, i)
      notInfer _ = True
  checkAppWith {vars} rig elabinfo nest env fc tm ty (arg :: expargs) impargs kr expty 
      = -- Invent a function type,  and hope that we'll know enough to solve it
        -- later when we unify with expty
        do logNF 10 "Function type" env ty
           logTerm 10 "Function " tm
           argn <- genName "argTy"
           retn <- genName "retTy"
           argTy <- metaVar fc Rig0 env argn (TType fc)
           let argTyG = gnf env argTy
           retTy <- metaVar -- {vars = argn :: vars}
                            fc Rig0 env -- (Pi RigW Explicit argTy :: env) 
                            retn (TType fc)
           (argv, argt) <- check rig elabinfo
                                 nest env arg (Just argTyG)
           let fntm = App fc tm argv
           defs <- get Ctxt
           fnty <- nf defs env retTy -- (Bind fc argn (Let RigW argv argTy) retTy)
           let expfnty = gnf env (Bind fc argn (Pi RigW Explicit argTy) (weaken retTy))
           logGlue 10 "Expected function type" env expfnty
           maybe (pure ()) (logGlue 10 "Expected result type" env) expty
           res <- checkAppWith rig elabinfo nest env fc fntm fnty expargs impargs kr expty
           cres <- Check.convert fc elabinfo env (glueBack defs env ty) expfnty
           let [] = constraints cres
              | cs => do cty <- getTerm expfnty
                         ctm <- newConstant fc rig env (fst res) cty cs
                         pure (ctm, expfnty)
           pure res

export
checkApp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> ElabInfo -> 
           NestedNames vars -> Env Term vars -> 
           FC -> (fn : RawImp) -> 
           (expargs : List RawImp) -> 
           (impargs : List (Maybe Name, RawImp)) ->
           Maybe (Glued vars) ->
           Core (Term vars, Glued vars)
checkApp rig elabinfo nest env fc (IApp fc' fn arg) expargs impargs exp
   = checkApp rig elabinfo nest env fc' fn (arg :: expargs) impargs exp
checkApp rig elabinfo nest env fc (IImplicitApp fc' fn nm arg) expargs impargs exp
   = checkApp rig elabinfo nest env fc' fn expargs ((nm, arg) :: impargs) exp
checkApp rig elabinfo nest env fc (IVar fc' n) expargs impargs exp
   = do (ntm, nty_in) <- getVarType rig nest env fc n
        nty <- getNF nty_in
        elabinfo <- updateElabInfo (elabMode elabinfo) n expargs elabinfo
        logC 10 (do defs <- get Ctxt
                    fnty <- quote defs env nty
                    exptyt <- maybe (pure Nothing) 
                                       (\t => do ety <- getTerm t
                                                 etynf <- normaliseHoles defs env ety
                                                 pure (Just !(toFullNames etynf)))
                                       exp
                    pure ("Checking application of " ++ show !(getFullName n) ++
                          " to " ++ show expargs ++ "\n\tFunction type " ++
                          (show !(toFullNames fnty)) ++ "\n\tExpected app type "
                                ++ show exptyt))
        checkAppWith rig elabinfo nest env fc ntm nty expargs impargs False exp
  where
    isPrimName : List Name -> Name -> Bool
    isPrimName [] fn = False
    isPrimName (p :: ps) fn 
        = dropNS fn == p || isPrimName ps fn
        
    updateElabInfo : ElabMode -> Name -> List RawImp -> ElabInfo -> Core ElabInfo
    -- If it's a primitive function applied to a constant on the LHS, treat it
    -- as an expression because we'll normalise the function away and match on
    -- the result
    updateElabInfo (InLHS _) n [IPrimVal fc c] elabinfo =
        do let prims = mapMaybe id 
                          [!fromIntegerName, !fromStringName, !fromCharName]
           if isPrimName prims !(getFullName n)
              then pure (record { elabMode = InExpr } elabinfo)
              else pure elabinfo
    updateElabInfo _ _ _ info = pure info

checkApp rig elabinfo nest env fc fn expargs impargs exp
   = do (fntm, fnty_in) <- checkImp rig elabinfo nest env fn Nothing
        fnty <- getNF fnty_in
        checkAppWith rig elabinfo nest env fc fntm fnty expargs impargs False exp

