module TTImp.Elab.Term

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
-- import Core.QUnify
import Core.TT
import Core.Value

import TTImp.TTImp

public export
data ExpType : Type -> Type where
     Unknown : ExpType a
     Args : List (Name, a) -> a -> ExpType a

public export
record EState (vars : List Name) where
  constructor MkEState
  nextVar : Int

export
data EST : Type where

mutual
  export
  check : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto e : Ref EST (EState vars)} ->
          {auto v : Ref UVars (UCtxt vars)} ->
          RigCount -> Env Term vars -> RawImp -> 
          ExpType (NF vars) ->
          Core (Term vars, NF vars)
  check rigc env tm exp = checkImp rigc env tm exp

  checkImp : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto e : Ref EST (EState vars)} ->
             {auto v : Ref UVars (UCtxt vars)} ->
             RigCount -> Env Term vars -> RawImp -> ExpType (NF vars) ->
             Core (Term vars, NF vars)
  checkImp rig env (IVar fc n) exp 
      = do (ntm, nty) <- getNameType rig env fc n exp
           checkAppWith rig env fc ntm nty [] [] exp
  checkImp rig env (IPi fc r p mname argTy retTy) exp = ?checkImp_rhs_2
  checkImp rig env (ILam fc r p mname argTy lamTy) exp = ?checkImp_rhs_3
  checkImp rig env (IApp fc fn arg) exp 
      = checkApp rig env fc fn [arg] [] exp
  checkImp rig env (IImplicitApp fc fn nm arg) exp
      = checkApp rig env fc fn [] [(nm, arg)] exp
  checkImp rig env (IPrimVal fc c) exp = ?checkImp_rhs_6
  checkImp rig env (IType fc) exp = ?checkImp_rhs_7
  checkImp rig env (Implicit fc) exp = ?checkImp_rhs_8

  checkApp : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto e : Ref EST (EState vars)} ->
             {auto v : Ref UVars (UCtxt vars)} ->
             RigCount -> Env Term vars -> 
             FC -> (fn : RawImp) -> 
             (expargs : List RawImp) -> 
             (impargs : List (Maybe Name, RawImp)) ->
             ExpType (NF vars) ->
             Core (Term vars, NF vars)
  checkApp rig env fc (IApp fc' fn arg) expargs impargs exp
     = checkApp rig env fc' fn (arg :: expargs) impargs exp
  checkApp rig env fc (IImplicitApp fc' fn nm arg) expargs impargs exp
     = checkApp rig env fc' fn expargs ((nm, arg) :: impargs) exp
  checkApp rig env fc fn expargs impargs exp
     = do (fntm, fnty) <- checkImp rig env fn Unknown
          checkAppWith rig env fc fntm fnty expargs impargs exp
  
  checkAppWith : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto e : Ref EST (EState vars)} ->
                 {auto v : Ref UVars (UCtxt vars)} ->
                 RigCount -> Env Term vars -> 
                 FC -> Term vars -> NF vars ->
                 (expargs : List RawImp) -> 
                 (impargs : List (Maybe Name, RawImp)) ->
                 ExpType (NF vars) ->
                 Core (Term vars, NF vars)
  checkAppWith rig env fc fntm (NBind _ x (Pi r Explicit aty) rty) 
               (arg :: expargs) impargs exp
      = ?doApp
  checkAppWith rig env fc fntm fnty expargs impargs exp
      = ?noMoreTy

  getNameType : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto e : Ref EST (EState vars)} ->
                {auto v : Ref UVars (UCtxt vars)} ->
                RigCount -> Env Term vars -> FC -> Name -> ExpType (NF vars) ->
                Core (Term vars, NF vars)
  getNameType rigc env fc x expected
      = case defined x env of
             Just (_ ** (rigb, lv)) => 
                do rigSafe rigb rigc
                   ucs <- get UVars
                   defs <- get Ctxt
                   let bty = binderType (getBinder lv env)
                   pure (Local fc (Just rigb) _ lv, !(nf defs ucs env bty))
             Nothing => 
                do ucs <- get UVars
                   defs <- get Ctxt
                   Just def <- lookupCtxtExact x (gamma defs)
                        | Nothing => throw (UndefinedName fc x)
                   let nt = case definition def of
                                 Fn _ => Func
                                 DCon t a => DataCon t a
                                 TCon t a _ _ _ => TyCon t a
                                 _ => Func
                   pure (Ref fc nt x, !(nf defs ucs env (embed (type def))))
    where
      rigSafe : RigCount -> RigCount -> Core ()
      rigSafe Rig1 RigW = throw (LinearMisuse fc x Rig1 RigW)
      rigSafe Rig0 RigW = throw (LinearMisuse fc x Rig0 RigW)
      rigSafe Rig0 Rig1 = throw (LinearMisuse fc x Rig0 Rig1)
      rigSafe _ _ = pure ()

