module TTImp.Elab.Binders

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

-- Drop the name from the nested function declarations. We do this when
-- going into a new scope, so that we're resolving to the most recently
-- bound name.
export
dropName : Name -> NestedNames vars -> NestedNames vars
dropName n nest = record { names $= drop } nest
  where
    drop : List (Name, a) -> List (Name, a)
    drop [] = []
    drop ((x, y) :: xs) 
        = if x == n then drop xs 
             else (x, y) :: drop xs

export
checkPi : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          {auto e : Ref EST (EState vars)} ->
          RigCount -> ElabInfo -> 
          NestedNames vars -> Env Term vars -> 
          FC -> 
          RigCount -> PiInfo -> (n : Name) -> 
          (argTy : RawImp) -> (retTy : RawImp) ->
          (expTy : Maybe (Glued vars)) ->
          Core (Term vars, Glued vars)
checkPi rig elabinfo nest env fc rigf info n argTy retTy expTy
    = do let pirig = getRig (elabMode elabinfo)
         (tyv, tyt) <- check pirig elabinfo nest env argTy 
                             (Just (gType fc))
         let env' : Env Term (n :: _) = Pi rigf info tyv :: env
         let nest' = weaken (dropName n nest)
         (scopev, scopet) <- 
            inScope fc env' (\e' => 
              check {e=e'} pirig elabinfo nest' env' retTy (Just (gType fc)))
         checkExp rig elabinfo env fc (Bind fc n (Pi rigf info tyv) scopev) (gType fc) expTy
  where
    -- Might want to match on the LHS, so use the context rig, otherwise
    -- it's always erased
    getRig : ElabMode -> RigCount
    getRig (InLHS _) = rig
    getRig _ = Rig0

findLamRig : {auto c : Ref Ctxt Defs} ->
             Maybe (Glued vars) -> Core RigCount
findLamRig Nothing = pure RigW
findLamRig (Just expty)
    = do tynf <- getNF expty
         case tynf of
              NBind _ _ (Pi c _ _) sc => pure c
              _ => pure RigW

inferLambda : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              RigCount -> ElabInfo -> 
              NestedNames vars -> Env Term vars -> 
              FC -> 
              RigCount -> PiInfo -> (n : Name) -> 
              (argTy : RawImp) -> (scope : RawImp) ->
              (expTy : Maybe (Glued vars)) ->
              Core (Term vars, Glued vars)
inferLambda rig elabinfo nest env fc rigl info n argTy scope expTy
    = do rigb_in <- findLamRig expTy
         let rigb = min rigb_in rigl
         (tyv, tyt) <- check Rig0 elabinfo nest env argTy (Just (gType fc))
         let env' : Env Term (n :: _) = Lam rigb info tyv :: env
         let nest' = weaken (dropName n nest)
         (scopev, scopet) <- inScope fc env' (\e' =>
                                check {e=e'} rig elabinfo 
                                      nest' env' scope Nothing)
         let lamty = gnf env (Bind fc n (Pi rigb info tyv) !(getTerm scopet))
         logGlue 5 "Inferred lambda type" env lamty
         checkExp rig elabinfo env fc
                  (Bind fc n (Lam rigb info tyv) scopev)
                  lamty expTy

getTyNF : {auto c : Ref Ctxt Defs} ->
          Env Term vars -> Term vars -> Core (Term vars)
getTyNF env x@(Bind _ _ _ _) = pure x
getTyNF env x
    = do defs <- get Ctxt
         xnf <- nf defs env x
         empty <- clearDefs defs
         quote empty env xnf

export
checkLambda : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              RigCount -> ElabInfo -> 
              NestedNames vars -> Env Term vars -> 
              FC -> 
              RigCount -> PiInfo -> (n : Name) -> 
              (argTy : RawImp) -> (scope : RawImp) ->
              (expTy : Maybe (Glued vars)) ->
              Core (Term vars, Glued vars)
checkLambda rig_in elabinfo nest env fc rigl info n argTy scope Nothing
    = let rig = if rig_in == Rig0 then Rig0 else Rig1 in
          inferLambda rig elabinfo nest env fc rigl info n argTy scope Nothing
checkLambda rig_in elabinfo nest env fc rigl info n argTy scope (Just expty_in)
    = do let rig = if rig_in == Rig0 then Rig0 else Rig1
         expty <- getTerm expty_in
         exptynf <- getTyNF env expty
         defs <- get Ctxt
         case exptynf of
              Bind bfc bn (Pi c _ pty) psc =>
                 do (tyv, tyt) <- check Rig0 elabinfo nest env 
                                        argTy (Just (gType fc))
                    let rigb = min rigl c
                    let env' : Env Term (n :: _) = Lam rigb info tyv :: env
                    convert fc elabinfo env (gnf env tyv) (gnf env pty) 
                    let nest' = weaken (dropName n nest)
                    (scopev, scopet) <-
                       inScope fc env' (\e' =>
                          check {e=e'} rig elabinfo nest' env' scope 
                                (Just (gnf env' (renameTop n psc))))
                    logTermNF 10 "Lambda type" env exptynf
                    logGlueNF 10 "Got scope type" env' scopet
                    checkExp rig elabinfo env fc 
                             (Bind fc n (Lam rigb info tyv) scopev)
                             (gnf env 
                                  (Bind fc n (Pi rigb info tyv) !(getTerm scopet)))
                             (Just (gnf env
                                       (Bind fc bn (Pi rigb info pty) psc)))
              _ => inferLambda rig elabinfo nest env fc rigl info n argTy scope (Just expty_in)

weakenExp : Env Term (x :: vars) ->
            Maybe (Glued vars) -> Core (Maybe (Glued (x :: vars)))
weakenExp env Nothing = pure Nothing
weakenExp env (Just gtm)
    = do tm <- getTerm gtm
         pure (Just (gnf env (weaken tm)))

export
checkLet : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> ElabInfo -> 
           NestedNames vars -> Env Term vars -> 
           FC -> 
           RigCount -> (n : Name) -> 
           (nTy : RawImp) -> (nVal : RawImp) -> (scope : RawImp) ->
           (expTy : Maybe (Glued vars)) ->
           Core (Term vars, Glued vars)
checkLet rigc_in elabinfo nest env fc rigl n nTy nVal scope expty
    = do let rigc = if rigc_in == Rig0 then Rig0 else Rig1
         (tyv, tyt) <- check Rig0 elabinfo nest env nTy (Just (gType fc))
         -- Try checking at the given multiplicity; if that doesn't work,
         -- try checking at Rig1 (meaning that we're using a linear variable
         -- so the resulting binding should be linear)
         (valv, valt, rigb) <- handle
              (do c <- check (rigMult rigl rigc) elabinfo
                             nest env nVal (Just (gnf env tyv))
                  pure (fst c, snd c, rigMult rigl rigc))
              (\err => case err of
                            LinearMisuse _ _ Rig1 _
                              => do c <- check Rig1 elabinfo 
                                               nest env nVal (Just (gnf env tyv))
                                    pure (fst c, snd c, Rig1)
                            e => throw e)
         let env' : Env Term (n :: _) = Lam rigb Explicit tyv :: env
         let nest' = weaken (dropName n nest)
         expScope <- weakenExp env' expty 
         (scopev, gscopet) <- 
            inScope fc env' (\e' => 
              check {e=e'} rigc elabinfo nest' env' scope expScope)
         scopet <- getTerm gscopet
         checkExp rigc elabinfo env fc
                  (Bind fc n (Let rigb valv tyv) scopev)
                  (gnf env (Bind fc n (Let rigb valv tyv) scopet))
                  expty

