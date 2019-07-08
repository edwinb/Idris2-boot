module TTImp.Unelab

import TTImp.TTImp
import Core.CaseTree
import Core.Context
import Core.Env
import Core.Normalise
import Core.Options
import Core.Value
import Core.TT

%default covering

used : (idx : Nat) -> Term vars -> Bool
used idx (Local _ _ var _) = idx == var
used {vars} idx (Bind _ x b sc) = usedBinder b || used (1 + idx) sc
  where
    usedBinder : Binder (Term vars) -> Bool
    usedBinder (Let _ val ty) = used idx val || used idx ty
    usedBinder b = used idx (binderType b)
used idx (Meta _ _ _ args) = any (used idx) args
used idx (App _ f a) = used idx f || used idx a
used idx (As _ _ pat) = used idx pat
used idx (TDelayed _ _ tm) = used idx tm
used idx (TDelay _ _ _ tm) = used idx tm
used idx (TForce _ tm) = used idx tm
used idx _ = False

data IArg
   = Exp FC RawImp
   | Imp FC (Maybe Name) RawImp

data UnelabMode = Full | NoSugar | ImplicitHoles

Eq UnelabMode where
   Full == Full = True
   NoSugar == NoSugar = True
   ImplicitHoles == ImplicitHoles = True
   _ == _ = False

mutual
  unelabCase : {auto c : Ref Ctxt Defs} ->
               Name -> List IArg -> RawImp ->
               Core RawImp
  unelabCase n args orig
      = do defs <- get Ctxt
           Just glob <- lookupCtxtExact n (gamma defs)
                | Nothing => pure orig
           let PMDef _ pargs treect _ pats = definition glob
                | _ => pure orig
           let Just argpos = findArgPos treect
                | _ => pure orig
           if length args == length pargs
              then mkCase pats argpos 0 args
              else pure orig
    where
      -- Need to find the position of the scrutinee to rebuild original
      -- case correctly
      findArgPos : CaseTree as -> Maybe Nat
      findArgPos (Case idx p _ _) = Just idx
      findArgPos _ = Nothing

      idxOrDefault : Nat -> a -> List a -> a
      idxOrDefault Z def (x :: xs) = x
      idxOrDefault (S k) def (_ :: xs) = idxOrDefault k def xs
      idxOrDefault _ def [] = def

      getNth : Nat -> Term vars -> Term vars
      getNth n tm
          = case getFnArgs tm of
                 (f, as) => idxOrDefault n f as

      nthArg : FC -> Nat -> Term vars -> Term vars 
      nthArg fc drop (App afc f a) = getNth drop (App afc f a)
      nthArg fc drop tm = Erased fc

      mkClause : FC -> Nat ->
                 (vs ** (Env Term vs, Term vs, Term vs)) ->
                 Core ImpClause
      mkClause fc dropped (vs ** (env, lhs, rhs))
          = do let pat = nthArg fc dropped lhs
               lhs' <- unelabTy Full env pat
               rhs' <- unelabTy Full env rhs
               pure (PatClause fc (fst lhs') (fst rhs'))

      mkCase : List (vs ** (Env Term vs, Term vs, Term vs)) ->
               Nat -> Nat -> List IArg -> Core RawImp
      mkCase pats (S k) dropped (_ :: args) = mkCase pats k (S dropped) args
      mkCase pats Z dropped (Exp fc tm :: _)
          = do pats' <- traverse (mkClause fc dropped) pats
               pure $ ICase fc tm (Implicit fc False) pats'
      mkCase _ _ _ _ = pure orig

  unelabSugar : {auto c : Ref Ctxt Defs} ->
                (umode : UnelabMode) ->
                (RawImp, Term vars) ->
                Core (RawImp, Term vars)
  unelabSugar NoSugar res = pure res
  unelabSugar ImplicitHoles res = pure res
  unelabSugar _ (tm, ty) 
      = let (f, args) = getFnArgs tm [] in
            case f of
             IVar fc (NS ns (CaseBlock n i))
                 => pure (!(unelabCase (NS ns (CaseBlock n i)) args tm), ty)
             _ => pure (tm, ty)
    where
      getFnArgs : RawImp -> List IArg -> (RawImp, List IArg)
      getFnArgs (IApp fc f arg) args = getFnArgs f (Exp fc arg :: args)
      getFnArgs (IImplicitApp fc f n arg) args = getFnArgs f (Imp fc n arg :: args)
      getFnArgs tm args = (tm, args)

  -- Turn a term back into an unannotated TTImp. Returns the type of the
  -- unelaborated term so that we can work out where to put the implicit 
  -- applications
  -- NOTE: There is *no guarantee* that this will elaborate back successfully!
  -- It's only intended for display
  unelabTy : {auto c : Ref Ctxt Defs} ->
             (umode : UnelabMode) ->
             Env Term vars -> Term vars -> 
             Core (RawImp, Term vars)
  unelabTy umode env tm 
      = unelabSugar umode !(unelabTy' umode env tm)

  unelabTy' : {auto c : Ref Ctxt Defs} ->
              (umode : UnelabMode) ->
              Env Term vars -> Term vars -> 
              Core (RawImp, Term vars)
  unelabTy' umode env (Local {name} fc _ idx p) 
      = pure (IVar fc name, binderType (getBinder p env))
  unelabTy' umode env (Ref fc nt n)
      = do defs <- get Ctxt
           Just ty <- lookupTyExact n (gamma defs)
               | Nothing => case umode of
                                 ImplicitHoles => pure (Implicit fc True, Erased fc)
                                 _ => pure (IHole fc (nameRoot n), Erased fc)
           pure (IVar fc !(getFullName n), embed ty)
  unelabTy' umode env (Meta fc n i args)
      = do defs <- get Ctxt
           Just ty <- lookupTyExact (Resolved i) (gamma defs)
               | Nothing => case umode of
                                 ImplicitHoles => pure (Implicit fc True, Erased fc)
                                 _ => pure (IHole fc (nameRoot n), Erased fc)
           pure (IHole fc (nameRoot n), embed ty)
  unelabTy' umode env (Bind fc x b sc)
      = do (sc', scty) <- unelabTy umode (b :: env) sc
           unelabBinder umode fc env x b sc sc' scty
  unelabTy' umode env (App fc fn arg)
      = do (fn', fnty) <- unelabTy umode env fn
           (arg', argty) <- unelabTy umode env arg
           defs <- get Ctxt
           case !(nf defs env fnty) of
                NBind _ x (Pi rig Explicit ty) sc
                  => do sc' <- sc defs (toClosure defaultOpts env arg)
                        pure (IApp fc fn' arg',
                                !(quote defs env sc'))
                NBind _ x (Pi rig p ty) sc
                  => do sc' <- sc defs (toClosure defaultOpts env arg)
                        pure (IImplicitApp fc fn' (Just x) arg',
                                !(quote defs env sc'))
                _ => pure (IApp fc fn' arg', Erased fc)
  unelabTy' umode env (As fc p tm)
      = do (p', _) <- unelabTy' umode env p 
           (tm', ty) <- unelabTy' umode env tm
           case p' of
                IVar _ n => 
                    case umode of
                         NoSugar => pure (IAs fc UseRight n tm', ty)
                         _ => pure (tm', ty)
                _ => pure (tm', ty) -- Should never happen!
  unelabTy' umode env (TDelayed fc r tm)
      = do (tm', ty) <- unelabTy' umode env tm
           defs <- get Ctxt
           pure (IDelayed fc r tm', Erased fc)
  unelabTy' umode env (TDelay fc r _ tm)
      = do (tm', ty) <- unelabTy' umode env tm
           defs <- get Ctxt
           pure (IDelay fc tm', Erased fc)
  unelabTy' umode env (TForce fc tm)
      = do (tm', ty) <- unelabTy' umode env tm
           defs <- get Ctxt
           pure (IForce fc tm', Erased fc)
  unelabTy' umode env (PrimVal fc c) = pure (IPrimVal fc c, Erased fc)
  unelabTy' umode env (Erased fc) = pure (Implicit fc False, Erased fc)
  unelabTy' umode env (TType fc) = pure (IType fc, TType fc)
  unelabTy' umode _ tm 
      = let fc = getLoc tm in 
            pure (Implicit fc False, Erased fc)

  unelabBinder : {auto c : Ref Ctxt Defs} ->
                 (umode : UnelabMode) ->
                 FC -> Env Term vars -> (x : Name) ->
                 Binder (Term vars) -> Term (x :: vars) ->
                 RawImp -> Term (x :: vars) -> 
                 Core (RawImp, Term vars)
  unelabBinder umode fc env x (Lam rig p ty) sctm sc scty
      = do (ty', _) <- unelabTy umode env ty
           pure (ILam fc rig p (Just x) ty' sc, Bind fc x (Pi rig p ty) scty)
  unelabBinder umode fc env x (Let rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy umode env val
           (ty', _) <- unelabTy umode env ty
           pure (ILet fc rig x ty' val' sc, Bind fc x (Let rig val ty) scty)
  unelabBinder umode fc env x (Pi rig p ty) sctm sc scty 
      = do (ty', _) <- unelabTy umode env ty
           let nm = if used 0 sctm || rig /= RigW
                       then Just x else Nothing
           pure (IPi fc rig p nm ty' sc, TType fc)
  unelabBinder umode fc env x (PVar rig _ ty) sctm sc scty
      = do (ty', _) <- unelabTy umode env ty
           pure (sc, Bind fc x (PVTy rig ty) scty)
  unelabBinder umode fc env x (PLet rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy umode env val
           (ty', _) <- unelabTy umode env ty
           pure (ILet fc rig x ty' val' sc, Bind fc x (PLet rig val ty) scty)
  unelabBinder umode fc env x (PVTy rig ty) sctm sc scty
      = do (ty', _) <- unelabTy umode env ty
           pure (sc, TType fc)

export
unelabNoSugar : {auto c : Ref Ctxt Defs} ->
                Env Term vars -> Term vars -> Core RawImp
unelabNoSugar env tm
    = do tm' <- unelabTy NoSugar env tm
         pure $ fst tm'

export
unelabNoPatvars : {auto c : Ref Ctxt Defs} ->
                  Env Term vars -> Term vars -> Core RawImp
unelabNoPatvars env tm
    = do tm' <- unelabTy ImplicitHoles env tm
         pure $ fst tm'

export
unelab : {auto c : Ref Ctxt Defs} ->
         Env Term vars -> Term vars -> Core RawImp
unelab env tm
    = do tm' <- unelabTy Full env tm
         pure $ fst tm'

