module TTImp.Elab.Local

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

export
checkLocal : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto e : Ref EST (EState vars)} ->
             RigCount -> ElabInfo ->
             NestedNames vars -> Env Term vars ->
             FC -> List ImpDecl -> (scope : RawImp) ->
             (expTy : Maybe (Glued vars)) ->
             Core (Term vars, Glued vars)
checkLocal {vars} rig elabinfo nest env fc nestdecls scope expty
    = do let defNames = definedInBlock [] nestdecls
         est <- get EST
         let f = defining est
         names' <- traverse (applyEnv f)
                            (nub defNames) -- binding names must be unique
                                           -- fixes bug #115
         let nest' = record { names $= (names' ++) } nest
         let env' = dropLinear env
         traverse (processDecl [] nest' env') (map (updateName nest') nestdecls)
         check rig elabinfo nest' env scope expty
  where
    -- For the local definitions, don't allow access to linear things
    -- unless they're explicitly passed.
    -- This is because, at the moment, we don't have any mechanism of
    -- ensuring the nested definition is used exactly once
    dropLinear : Env Term vs -> Env Term vs
    dropLinear [] = []
    dropLinear (b :: bs)
        = if isLinear (multiplicity b)
             then setMultiplicity b erased :: dropLinear bs
             else b :: dropLinear bs

    applyEnv : {auto c : Ref Ctxt Defs} -> Int -> Name ->
               Core (Name, (Maybe Name, List Name, FC -> NameType -> Term vars))
    applyEnv outer inner
          = do ust <- get UST
               put UST (record { nextName $= (+1) } ust)
               let nestedName_in = Nested (outer, nextName ust) inner
               nestedName <- inCurrentNS nestedName_in
               n' <- addName nestedName
               pure (inner, (Just nestedName, namesNoLet env,
                        \fc, nt => applyTo fc
                               (Ref fc nt (Resolved n')) env))

    -- Update the names in the declarations to the new 'nested' names.
    -- When we encounter the names in elaboration, we'll update to an
    -- application of the nested name.
    newName : NestedNames vars -> Name -> Name
    newName nest n
        = case lookup n (names nest) of
               Just (Just n', _) => n'
               _ => n

    updateTyName : NestedNames vars -> ImpTy -> ImpTy
    updateTyName nest (MkImpTy loc' n ty)
        = MkImpTy loc' (newName nest n) ty

    updateDataName : NestedNames vars -> ImpData -> ImpData
    updateDataName nest (MkImpData loc' n tycons dopts dcons)
        = MkImpData loc' (newName nest n) tycons dopts
                         (map (updateTyName nest) dcons)
    updateDataName nest (MkImpLater loc' n tycons)
        = MkImpLater loc' (newName nest n) tycons

    updateName : NestedNames vars -> ImpDecl -> ImpDecl
    updateName nest (IClaim loc' r vis fnopts ty)
         = IClaim loc' r vis fnopts (updateTyName nest ty)
    updateName nest (IDef loc' n cs)
         = IDef loc' (newName nest n) cs
    updateName nest (IData loc' vis d)
         = IData loc' vis (updateDataName nest d)
    updateName nest i = i

getLocalTerm : {auto c : Ref Ctxt Defs} ->
               FC -> Env Term vars -> Term vars -> List Name -> Core (Term vars)
getLocalTerm fc env f [] = pure f
getLocalTerm fc env f (a :: as)
    = case defined a env of
           Just (MkIsDefined rigb lv) =>
                getLocalTerm fc env (App fc f (Local fc Nothing _ lv)) as
           Nothing => throw (InternalError "Case Local failed")

export
checkCaseLocal : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 RigCount -> ElabInfo ->
                 NestedNames vars -> Env Term vars ->
                 FC -> Name -> Name -> List Name -> RawImp ->
                 (expTy : Maybe (Glued vars)) ->
                 Core (Term vars, Glued vars)
checkCaseLocal {vars} rig elabinfo nest env fc uname iname args sc expty
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact iname (gamma defs)
              | Nothing => check rig elabinfo nest env sc expty
         let name = case definition def of
                         PMDef _ _ _ _ _ => Ref fc Func iname
                         DCon t a _ => Ref fc (DataCon t a) iname
                         TCon t a _ _ _ _ _ _ => Ref fc (TyCon t a) iname
                         _ => Ref fc Func iname
         app <- getLocalTerm fc env name args
         log 5 $ "Updating case local " ++ show uname ++ " " ++ show args
         logTermNF 10 "To" env app
         let nest' = record { names $= ((uname, (Just iname, reverse args,
                                                (\fc, nt => app))) :: ) }
                            nest
         check rig elabinfo nest' env sc expty
