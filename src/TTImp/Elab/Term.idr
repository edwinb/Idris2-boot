module TTImp.Elab.Term

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.App
import TTImp.Elab.Binders
import TTImp.Elab.Check
import TTImp.Elab.ImplicitBind
import TTImp.Elab.Prim
import TTImp.TTImp

%default covering

-- If the expected type has an implicit pi, elaborate with leading
-- implicit lambdas if they aren't there already. 
insertImpLam : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               Env Term vars ->
               (term : RawImp) -> (expected : Maybe (Glued vars)) ->
               Core RawImp
insertImpLam {vars} env tm (Just ty) = bindLam tm ty
  where
    -- If we can decide whether we need implicit lambdas without looking
    -- at the normal form, do so
    bindLamTm : RawImp -> Term vs -> Core (Maybe RawImp)
    bindLamTm tm@(ILam _ _ Implicit _ _ _) (Bind fc n (Pi _ Implicit _) sc)
        = pure (Just tm)
    bindLamTm tm (Bind fc n (Pi c Implicit ty) sc)
        = do n' <- genName ("imp_" ++ show n)
             Just sc' <- bindLamTm tm sc
                 | Nothing => pure Nothing
             pure $ Just (ILam fc c Implicit (Just n') (Implicit fc False) sc')
    bindLamTm tm exp
        = case getFn exp of
               Ref _ Func _ => pure Nothing -- might still be implicit
               Case _ _ _ _ _ => pure Nothing
               TForce _ _ => pure Nothing
               Bind _ _ (Lam _ _ _) _ => pure Nothing
               _ => pure $ Just tm

    bindLamNF : RawImp -> NF vars -> Core RawImp
    bindLamNF tm@(ILam _ _ Implicit _ _ _) (NBind fc n (Pi _ Implicit _) sc)
        = pure tm
    bindLamNF tm (NBind fc n (Pi c Implicit ty) sc)
        = do n' <- genName ("imp_" ++ show n)
             sctm <- sc (toClosure defaultOpts env (Ref fc Bound n'))
             sc' <- bindLamNF tm sctm
             pure $ ILam fc c Implicit (Just n') (Implicit fc False) sc'
    bindLamNF tm sc = pure tm

    bindLam : RawImp -> Glued vars -> Core RawImp
    bindLam tm gty
        = do ty <- getTerm gty
             Just tm' <- bindLamTm tm ty
                | Nothing =>
                    do nf <- getNF gty
                       bindLamNF tm nf
             pure tm'
insertImpLam env tm _ = pure tm

-- Main driver for checking terms, after implicits have been added.
-- Implements 'checkImp' in TTImp.Elab.Check
checkTerm : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            RigCount -> ElabInfo -> Env Term vars -> RawImp -> Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
checkTerm rig elabinfo env (IVar fc n) exp 
    = -- It may actually turn out to be an application, if the expected
      -- type is expecting an implicit argument, so check it as an
      -- application with no arguments
      checkApp rig elabinfo env fc (IVar fc n) [] [] exp
checkTerm rig elabinfo env (IPi fc r p (Just n) argTy retTy) exp 
    = checkPi rig elabinfo env fc r p n argTy retTy exp
checkTerm rig elabinfo env (IPi fc r p Nothing argTy retTy) exp 
    = do n <- case p of
                   Explicit => genName "arg"
                   Implicit => genName "imp"
                   AutoImplicit => genName "con"
         checkPi rig elabinfo env fc r p n argTy retTy exp
checkTerm rig elabinfo env (ILam fc r p (Just n) argTy scope) exp 
    = checkLambda rig elabinfo env fc r p n argTy scope exp
checkTerm rig elabinfo env (ILam fc r p Nothing argTy scope) exp 
    = do n <- genName "lam"
         checkLambda rig elabinfo env fc r p n argTy scope exp
checkTerm rig elabinfo env (IApp fc fn arg) exp 
    = checkApp rig elabinfo env fc fn [arg] [] exp
checkTerm rig elabinfo env (IImplicitApp fc fn nm arg) exp
    = checkApp rig elabinfo env fc fn [] [(nm, arg)] exp

checkTerm rig elabinfo env (IBindHere fc binder sc) exp
    = checkBindHere rig elabinfo env fc binder sc exp
checkTerm rig elabinfo env (IBindVar fc n) exp
    = checkBindVar rig elabinfo env fc n exp
checkTerm rig elabinfo env (IAs fc n tm) exp
    = throw (InternalError "Not implemented")
checkTerm rig elabinfo env (IMustUnify fc n tm) exp
    = throw (InternalError "Not implemented")

checkTerm {vars} rig elabinfo env (IPrimVal fc c) exp 
    = do let (cval, cty) = checkPrim {vars} fc c
         defs <- get Ctxt
         checkExp rig elabinfo env fc cval (gnf defs env cty) exp
checkTerm rig elabinfo env (IType fc) exp 
    = checkExp rig elabinfo env fc (TType fc) (gType fc) exp

checkTerm rig elabinfo env (Implicit fc b) (Just gexpty)
    = do nm <- genName "imp"
         expty <- getTerm gexpty
         metaval <- metaVar fc rig env nm expty
         -- Add to 'bindIfUnsolved' if 'b' set
         when (b && bindingVars elabinfo) $
            do est <- get EST
               expty <- getTerm gexpty
               put EST (addBindIfUnsolved nm rig env metaval expty est)
         pure (metaval, gexpty)
checkTerm rig elabinfo env (Implicit fc b) Nothing
    = do nmty <- genName "impTy"
         ty <- metaVar fc Rig0 env nmty (TType fc)
         nm <- genName "imp"
         metaval <- metaVar fc rig env nm ty
         -- Add to 'bindIfUnsolved' if 'b' set
         when (b && bindingVars elabinfo) $
            do est <- get EST
               put EST (addBindIfUnsolved nm rig env metaval ty est)
         defs <- get Ctxt
         pure (metaval, gnf defs env ty)

-- Declared in TTImp.Elab.Check
TTImp.Elab.Check.check rigc elabinfo env tm exp 
    = do defs <- get Ctxt
         case elabMode elabinfo of
              InLHS _ => -- Don't expand implicit lambda on lhs
                 checkImp rigc elabinfo env tm exp
              _ => do tm' <- insertImpLam env tm exp
                      checkImp rigc elabinfo env tm' exp

TTImp.Elab.Check.checkImp rigc elabinfo env tm exp
    = checkTerm rigc elabinfo env tm exp

