module TTImp.ProcessDef

-- import Core.CaseBuilder
import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.Value
import Core.UnifyState

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.TTImp

-- Given a type checked LHS and its type, return the environment in which we
-- should check the RHS, the LHS and its type in that environment,
-- and a function which turns a checked RHS into a
-- pattern clause
extendEnv : Env Term vars -> 
            Term vars -> Term vars -> 
            Core (vars' ** (Env Term vars', Term vars', Term vars'))
extendEnv env (Bind _ n (PVar c tmty) sc) (Bind _ n' (PVTy _ _) tysc) with (nameEq n n')
  extendEnv env (Bind _ n (PVar c tmty) sc) (Bind _ n' (PVTy _ _) tysc) | Nothing
      = throw (InternalError "Can't happen: names don't match in pattern type")
  extendEnv env (Bind _ n (PVar c tmty) sc) (Bind _ n (PVTy _ _) tysc) | (Just Refl)
      = extendEnv (PVar c tmty :: env) sc tysc
extendEnv env tm ty 
      = pure (_ ** (env, tm, ty))

-- Find names which are applied to a function in a Rig1/Rig0 position,
-- so that we know how they should be bound on the right hand side of the
-- pattern.
-- 'bound' counts the number of variables locally bound; these are the
-- only ones we're checking linearity of (we may be shadowing names if this
-- is a local definition, so we need to leave the earlier ones alone)
findLinear : {auto c : Ref Ctxt Defs} ->
             Bool -> Nat -> RigCount -> Term vars -> 
             Core (List (Name, RigCount))
findLinear top bound rig (Bind fc n b sc) 
    = findLinear top (S bound) rig sc
findLinear top bound rig tm
    = case getFnArgs tm of
           (Ref _ _ n, []) => pure []
           (Ref _ nt n, argsi)
              => do let args = map snd argsi
                    defs <- get Ctxt
                    Just nty <- lookupTyExact n (gamma defs)
                         | Nothing => pure []
                    findLinArg (accessible nt rig) !(nf defs [] nty) args
           _ => pure []
    where
      accessible : NameType -> RigCount -> RigCount
      accessible Func r = if top then r else Rig0
      accessible _ r = r

      findLinArg : RigCount -> NF [] -> List (Term vars) -> 
                   Core (List (Name, RigCount))
      findLinArg rig (NBind _ x (Pi c _ _) sc) (Local {name=a} fc _ idx prf :: as) 
          = if idx < bound
               then do sc' <- sc (toClosure defaultOpts [] (Ref fc Bound x))
                       pure $ (a, rigMult c rig) :: 
                                  !(findLinArg rig sc' as)
               else do sc' <- sc (toClosure defaultOpts [] (Ref fc Bound x))
                       findLinArg rig sc' as
      findLinArg rig (NBind fc x (Pi c _ _) sc) (a :: as) 
          = pure $ !(findLinear False bound (rigMult c rig) a) ++
                   !(findLinArg rig !(sc (toClosure defaultOpts [] (Ref fc Bound x))) as)
      findLinArg rig ty (a :: as) 
          = pure $ !(findLinear False bound rig a) ++ !(findLinArg rig ty as)
      findLinArg _ _ [] = pure []

setLinear : List (Name, RigCount) -> Term vars -> Term vars
setLinear vs (Bind fc x (PVar c ty) sc)
    = case lookup x vs of
           Just c' => Bind fc x (PVar c' ty) (setLinear vs sc)
           _ => Bind fc x (PVar c ty) (setLinear vs sc)
setLinear vs (Bind fc x (PVTy c ty) sc)
    = case lookup x vs of
           Just c' => Bind fc x (PVTy c' ty) (setLinear vs sc)
           _ => Bind fc x (PVTy c ty) (setLinear vs sc)
setLinear vs tm = tm

-- Combining multiplicities on LHS:
-- Rig1 + Rig1/W not valid, since it means we have repeated use of name
-- Rig0 + RigW = RigW
-- Rig0 + Rig1 = Rig1
combineLinear : FC -> List (Name, RigCount) ->
                Core (List (Name, RigCount))
combineLinear loc [] = pure []
combineLinear loc ((n, count) :: cs)
    = case lookupAll n cs of
           [] => pure $ (n, count) :: !(combineLinear loc cs)
           counts => do count' <- combineAll count counts
                        pure $ (n, count') :: 
                               !(combineLinear loc (filter notN cs))
  where
    notN : (Name, RigCount) -> Bool
    notN (n', _) = n /= n'

    lookupAll : Name -> List (Name, RigCount) -> List RigCount
    lookupAll n [] = []
    lookupAll n ((n', c) :: cs) 
       = if n == n' then c :: lookupAll n cs else lookupAll n cs

    combine : RigCount -> RigCount -> Core RigCount
    combine Rig1 Rig1 = throw (LinearUsed loc 2 n)
    combine Rig1 RigW = throw (LinearUsed loc 2 n)
    combine RigW Rig1 = throw (LinearUsed loc 2 n)
    combine RigW RigW = pure RigW
    combine Rig0 c = pure c
    combine c Rig0 = pure c

    combineAll : RigCount -> List RigCount -> Core RigCount
    combineAll c [] = pure c
    combineAll c (c' :: cs)
        = do newc <- combine c c'
             combineAll newc cs

-- Check a pattern clause, returning the component of the 'Case' expression it
-- represents, or Nothing if it's an impossible clause
export
checkClause : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              (mult : RigCount) -> (hashit : Bool) ->
              Name -> Env Term vars ->
              ImpClause -> Core (Maybe Clause)
checkClause mult hashit n env (ImpossibleClause fc lhs)
    = throw (InternalError "impossible not implemented yet")
checkClause mult hashit n env (PatClause fc lhs_in rhs)
    = do lhs <- lhsInCurrentNS lhs_in 
         (lhstm, lhstyg) <- elabTerm n (InLHS mult) env 
                                (IBindHere fc PATTERN lhs) Nothing
         lhsty <- getTerm lhstyg

         -- Normalise the LHS to get any functions or let bindings evaluated
         -- (this might be allowed, e.g. for 'fromInteger')
         defs <- get Ctxt
         lhstm <- normalise defs (noLet env) lhstm
         lhsty <- normaliseHoles defs env lhsty
         linvars_in <- findLinear True 0 Rig1 lhstm
         log 5 $ "Linearity of names in " ++ show n ++ ": " ++ 
                 show linvars_in

         linvars <- combineLinear fc linvars_in
         let lhstm_lin = setLinear linvars lhstm
         let lhsty_lin = setLinear linvars lhsty

         logTermNF 0 "LHS term" env lhstm_lin
         logTermNF 0 "LHS type" env lhsty_lin

         (vars'  ** (env', lhstm', lhsty')) <- 
             extendEnv env lhstm_lin lhsty_lin
         defs <- get Ctxt
         rhstm <- checkTerm n InExpr env' rhs (gnf defs env' lhsty')

         logTermNF 0 "RHS term" env' rhstm
         pure (Just (MkClause env' lhstm' rhstm))
  where
    noLet : Env Term vs -> Env Term vs
    noLet [] = []
    noLet (Let c v t :: env) = Lam c Explicit t :: noLet env
    noLet (b :: env) = b :: noLet env

export
processDef : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             Env Term vars -> FC ->
             Name -> List ImpClause -> Core ()
processDef {vars} env fc n_in cs_in
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
         ?foo
--          t <- getCaseTree env ty (mapMaybe id cs)
--          let def = abstractEnv fc env t
--          addDef n (record { definition = Fn def } gdef)
--          pure ()
