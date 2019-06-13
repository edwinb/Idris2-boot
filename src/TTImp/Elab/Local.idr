module TTImp.Elab.Local

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
    = do let defNames = definedInBlock nestdecls
         est <- get EST
         let f = defining est
         names' <- traverse (applyEnv f) defNames
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
               then setMultiplicity b Rig0 :: dropLinear bs
               else b :: dropLinear bs

      applyEnv : Int -> Name -> 
                 Core (Name, (Maybe Name, FC -> NameType -> Term vars))
      applyEnv outer inner 
            = do n' <- resolveName (Nested outer inner)
                 pure (inner, (Just (Resolved n'), 
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


