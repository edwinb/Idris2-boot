module TTImp.Elab.Term

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.App
import TTImp.Elab.Check
import TTImp.TTImp

getNameType : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto e : Ref EST (EState vars)} ->
              RigCount -> Env Term vars -> FC -> Name -> Maybe (NF vars) ->
              Core (Term vars, NF vars)
getNameType rigc env fc x expected
    = case defined x env of
           Just (_ ** (rigb, lv)) => 
              do rigSafe rigb rigc
                 defs <- get Ctxt
                 let bty = binderType (getBinder lv env)
                 pure (Local fc (Just rigb) _ lv, !(nf defs env bty))
           Nothing => 
              do defs <- get Ctxt
                 Just def <- lookupCtxtExact x (gamma defs)
                      | Nothing => throw (UndefinedName fc x)
                 let nt = case definition def of
                               Fn _ => Func
                               DCon t a => DataCon t a
                               TCon t a _ _ _ => TyCon t a
                               _ => Func
                 pure (Ref fc nt x, !(nf defs env (embed (type def))))
  where
    rigSafe : RigCount -> RigCount -> Core ()
    rigSafe Rig1 RigW = throw (LinearMisuse fc x Rig1 RigW)
    rigSafe Rig0 RigW = throw (LinearMisuse fc x Rig0 RigW)
    rigSafe Rig0 Rig1 = throw (LinearMisuse fc x Rig0 Rig1)
    rigSafe _ _ = pure ()

-- Main driver for checking terms, after implicits have been added.
-- Implements 'checkImp' in TTImp.Elab.Check
checkTerm : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto e : Ref EST (EState vars)} ->
            RigCount -> Env Term vars -> RawImp -> Maybe (NF vars) ->
            Core (Term vars, NF vars)
checkTerm rig env (IVar fc n) exp 
    = do (ntm, nty) <- getNameType rig env fc n exp
         -- It may actually turn out to be an application, if the expected
         -- type is expecting an implicit argument...
         argMetas <- collectArgs rig env [] [] nty exp
         checkAppWith rig env fc ntm nty argMetas exp
checkTerm rig env (IPi fc r p mname argTy retTy) exp = ?checkTerm_rhs_2
checkTerm rig env (ILam fc r p mname argTy lamTy) exp = ?checkTerm_rhs_3
checkTerm rig env (IApp fc fn arg) exp 
    = checkApp rig env fc fn [arg] [] exp
checkTerm rig env (IImplicitApp fc fn nm arg) exp
    = checkApp rig env fc fn [] [(nm, arg)] exp
checkTerm rig env (IPrimVal fc c) exp = ?checkTerm_rhs_6
checkTerm rig env (IType fc) exp = ?checkTerm_rhs_7
checkTerm rig env (Implicit fc) exp = ?checkTerm_rhs_8

-- Declared in TTImp.Elab.Check
TTImp.Elab.Check.check rigc env tm exp = checkImp rigc env tm exp
TTImp.Elab.Check.checkImp rigc env tm exp = checkTerm rigc env tm exp

