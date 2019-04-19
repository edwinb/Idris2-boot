module TTImp.ProcessDef

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.UnifyState

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.TTImp

mkPat' : List (Pat vars) -> Term vars -> Term vars -> Pat vars
mkPat' [] orig (Local fc c idx p) = PLoc fc idx p
mkPat' args orig (Ref fc (DataCon t a) n) = PCon fc n t a args
mkPat' args orig (Ref fc (TyCon t a) n) = PTyCon fc n a args
mkPat' [] orig (Bind fc x (Pi _ _ s) t)
    = PArrow fc x (mkPat' [] s s) (mkPat' [] t t)
mkPat' args orig (App fc fn p arg) 
    = let parg = mkPat' [] arg arg in
          mkPat' (parg :: args) orig fn
mkPat' args orig (As fc idx p ptm) 
    = let pat = mkPat' args orig ptm in
          PAs fc idx p pat
mkPat' [] orig (PrimVal fc c) = PConst fc c
mkPat' args orig tm = PUnmatchable (getLoc orig) orig

mkPat : Term vars -> Pat vars
mkPat tm = mkPat' [] tm tm

-- Given a type checked LHS and its type, return the environment in which we
-- should check the RHS, the LHS and its type in that environment,
-- and a function which turns a checked RHS into a
-- pattern clause
extendEnv : Env Term vars -> 
            Term vars -> Term vars -> 
            (PatAlt vars -> a) ->
            Core (vars' ** (Env Term vars', 
                            Term vars', Term vars',
                            List (Pat vars') -> Term vars' -> a))
extendEnv env (Bind _ n (PVar c tmty) sc) (Bind _ n' (PVTy _ _) tysc) p with (nameEq n n')
  extendEnv env (Bind _ n (PVar c tmty) sc) (Bind _ n' (PVTy _ _) tysc) p | Nothing
      = throw (InternalError "Can't happen: names don't match in pattern type")
  extendEnv env (Bind _ n (PVar c tmty) sc) (Bind _ n (PVTy _ _) tysc) p | (Just Refl)
      = extendEnv (PVar c tmty :: env) sc tysc (\alt => p (CBind c n tmty alt))
extendEnv env tm ty p 
      = pure (_ ** (env, tm, ty, \pats, rhs => p (CPats pats rhs)))

-- Check a pattern clause, returning the component of the 'Case' expression it
-- represents, or Nothing if it's an impossible clause
export
checkClause : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              (mult : RigCount) -> (hashit : Bool) ->
              Name -> Env Term vars ->
              ImpClause -> Core (Maybe (PatAlt vars))
checkClause mult hashit n env (ImpossibleClause fc lhs)
    = throw (InternalError "impossible not implemented yet")
checkClause mult hashit n env (PatClause fc lhs_in rhs)
    = do lhs <- lhsInCurrentNS lhs_in 
         (lhstm, lhstyg) <- elabTerm n (InLHS mult) env 
                                (IBindHere fc PATTERN lhs) Nothing
         lhsty <- getTerm lhstyg

         logTermNF 0 "LHS term" env lhstm
         logTermNF 0 "LHS type" env lhsty

         (vars'  ** (env', lhstm', lhsty', mkAlt)) <- 
             extendEnv env lhstm lhsty id
         defs <- get Ctxt
         rhstm <- checkTerm n InExpr env' rhs (gnf defs env' lhsty')

         logTermNF 0 "RHS term" env' rhstm
         pure (Just (mkAlt (map (mkPat . snd) (getArgs lhstm')) rhstm))

export
processDef : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             Env Term vars -> FC ->
             Name -> List ImpClause -> Core ()
processDef env fc n_in cs_in
    = do n <- inCurrentNS n_in
         defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (NoDeclaration fc n)
         let None = definition gdef
              | _ => throw (AlreadyDefined fc n)
         let ty = type gdef
         let hashit = visibility gdef == Public
         let mult = if multiplicity gdef == Rig0
                       then Rig0
                       else Rig1
         cs <- traverse (checkClause mult hashit n env) cs_in
         ?something
