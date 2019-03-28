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
import TTImp.TTImp

%default covering

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
checkTerm rig elabinfo env (IPrimVal fc c) exp 
    = ?checkTerm_rhs_6
checkTerm rig elabinfo env (IType fc) exp 
    = checkExp rig elabinfo env fc (TType fc) (gType fc) exp
checkTerm rig elabinfo env (Implicit fc) (Just gexpty)
    = do nm <- genName "imp"
         expty <- getTerm gexpty
         metaval <- newMeta fc rig env nm expty
         -- TODO: Add to 'bindIfUnsolved'
         pure (metaval, gexpty)
checkTerm rig elabinfo env (Implicit fc) Nothing
    = do nmty <- genName "impTy"
         ty <- newMeta fc Rig0 env nmty (TType fc)
         nm <- genName "imp"
         metaval <- newMeta fc rig env nm ty
         defs <- get Ctxt
         pure (metaval, gnf defs env ty)

-- Declared in TTImp.Elab.Check
TTImp.Elab.Check.check rigc elabinfo env tm exp 
    = checkImp rigc elabinfo env tm exp
TTImp.Elab.Check.checkImp rigc elabinfo env tm exp
    = checkTerm rigc elabinfo env tm exp

