module TTImp.ProcessDef

import Core.CaseBuilder
import Core.CaseTree
import Core.Context
import Core.Core
import Core.Coverage
import Core.Env
import Core.Hash
import Core.LinearCheck
import Core.Metadata
import Core.Normalise
import Core.Termination
import Core.Value
import Core.UnifyState

import TTImp.BindImplicits
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.TTImp
import TTImp.Unelab
import TTImp.Utils

import Data.NameMap

mutual
  mismatchNF : Defs -> NF vars -> NF vars -> Core Bool
  mismatchNF defs (NTCon _ xn xt _ xargs) (NTCon _ yn yt _ yargs) 
      = if xn /= yn
           then pure True
           else anyM (mismatch defs) (zip xargs yargs) 
  mismatchNF defs (NDCon _ _ xt _ xargs) (NDCon _ _ yt _ yargs) 
      = if xt /= yt
           then pure True
           else anyM (mismatch defs) (zip xargs yargs) 
  mismatchNF defs (NPrimVal _ xc) (NPrimVal _ yc) = pure (xc /= yc)
  mismatchNF defs (NDelayed _ _ x) (NDelayed _ _ y) = mismatchNF defs x y
  mismatchNF defs (NDelay _ _ _ x) (NDelay _ _ _ y) 
      = mismatchNF defs !(evalClosure defs x) !(evalClosure defs y)
  mismatchNF _ _ _ = pure False

  mismatch : Defs -> (Closure vars, Closure vars) -> Core Bool
  mismatch defs (x, y) 
      = mismatchNF defs !(evalClosure defs x) !(evalClosure defs y)

-- If the terms have the same type constructor at the head, and one of
-- the argument positions has different constructors at its head, then this
-- is an impossible case, so return True
export
impossibleOK : Defs -> NF vars -> NF vars -> Core Bool
impossibleOK defs (NTCon _ xn xt xa xargs) (NTCon _ yn yt ya yargs)
    = if xn == yn
         then anyM (mismatch defs) (zip xargs yargs)
         else pure False
-- If it's a data constructor, any mismatch will do
impossibleOK defs (NDCon _ _ xt _ xargs) (NDCon _ _ yt _ yargs)
    = if xt /= yt
         then pure True
         else anyM (mismatch defs) (zip xargs yargs)
impossibleOK defs x y = pure False

-- Given a type checked LHS and its type, return the environment in which we
-- should check the RHS, the LHS and its type in that environment,
-- and a function which turns a checked RHS into a
-- pattern clause
-- The 'SubVars' proof contains a proof that refers to the *inner* environment,
-- so all the outer things are marked as 'DropCons'
extendEnv : Env Term vars -> SubVars inner vars ->
            NestedNames vars ->
            Term vars -> Term vars -> 
            Core (vars' ** 
                    (SubVars inner vars',
                     Env Term vars', NestedNames vars', 
                     Term vars', Term vars'))
extendEnv env p nest (Bind _ n (PVar c tmty) sc) (Bind _ n' (PVTy _ _) tysc) with (nameEq n n')
  extendEnv env p nest (Bind _ n (PVar c tmty) sc) (Bind _ n' (PVTy _ _) tysc) | Nothing
      = throw (InternalError "Can't happen: names don't match in pattern type")
  extendEnv env p nest (Bind _ n (PVar c tmty) sc) (Bind _ n (PVTy _ _) tysc) | (Just Refl)
      = extendEnv (PVar c tmty :: env) (DropCons p) (weaken nest) sc tysc
extendEnv env p nest (Bind _ n (PLet c tmval tmty) sc) (Bind _ n' (PLet _ _ _) tysc) with (nameEq n n')
  extendEnv env p nest (Bind _ n (PLet c tmval tmty) sc) (Bind _ n' (PLet _ _ _) tysc) | Nothing
      = throw (InternalError "Can't happen: names don't match in pattern type")
  -- PLet on the left becomes Let on the right, to give it computational force
  extendEnv env p nest (Bind _ n (PLet c tmval tmty) sc) (Bind _ n (PLet _ _ _) tysc) | (Just Refl)
      = extendEnv (Let c tmval tmty :: env) (DropCons p) (weaken nest) sc tysc
extendEnv env p nest tm ty 
      = pure (_ ** (p, env, nest, tm, ty))

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
findLinear top bound rig (As fc _ p)
    = findLinear top bound rig p
findLinear top bound rig tm
    = case getFnArgs tm of
           (Ref _ _ n, []) => pure []
           (Ref _ nt n, args)
              => do defs <- get Ctxt
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
      findLinArg rig ty (As fc _ p :: as) = findLinArg rig ty (p :: as)
      findLinArg rig (NBind _ x (Pi c _ _) sc) (Local {name=a} fc _ idx prf :: as) 
          = do defs <- get Ctxt
               if idx < bound
                 then do sc' <- sc defs (toClosure defaultOpts [] (Ref fc Bound x))
                         pure $ (a, rigMult c rig) :: 
                                    !(findLinArg rig sc' as)
                 else do sc' <- sc defs (toClosure defaultOpts [] (Ref fc Bound x))
                         findLinArg rig sc' as
      findLinArg rig (NBind fc x (Pi c _ _) sc) (a :: as) 
          = do defs <- get Ctxt
               pure $ !(findLinear False bound (rigMult c rig) a) ++
                      !(findLinArg rig !(sc defs (toClosure defaultOpts [] (Ref fc Bound x))) as)
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

export
checkLHS : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           (mult : RigCount) -> (hashit : Bool) ->
           Int -> List ElabOpt -> NestedNames vars -> Env Term vars ->
           FC -> RawImp -> 
           Core (vars' ** (SubVars vars vars',
                           Env Term vars', NestedNames vars', 
                           Term vars', Term vars'))
checkLHS {vars} mult hashit n opts nest env fc lhs_in
    = do defs <- get Ctxt
         lhs_raw <- lhsInCurrentNS nest lhs_in 
         autoimp <- isAutoImplicits
         autoImplicits True
         (_, lhs_bound) <- bindNames False lhs_raw
         autoImplicits autoimp
         lhs <- implicitsAs defs vars lhs_bound

         log 5 $ "Checking " ++ show lhs
         logEnv 5 "In env" env
         (lhstm, lhstyg) <- 
             wrapError (InLHS fc !(getFullName (Resolved n))) $
                     elabTerm n (InLHS mult) opts nest env 
                                (IBindHere fc PATTERN lhs) Nothing
         logTerm 10 "Checked LHS term" lhstm
         lhsty <- getTerm lhstyg

         -- Normalise the LHS to get any functions or let bindings evaluated
         -- (this might be allowed, e.g. for 'fromInteger')
         defs <- get Ctxt
         lhstm <- normaliseLHS defs (letToLam env) lhstm
         lhsty <- normaliseHoles defs env lhsty
         linvars_in <- findLinear True 0 Rig1 lhstm
         logTerm 10 "Checked LHS term after normalise" lhstm
         log 5 $ "Linearity of names in " ++ show n ++ ": " ++ 
                 show linvars_in

         linvars <- combineLinear fc linvars_in
         let lhstm_lin = setLinear linvars lhstm
         let lhsty_lin = setLinear linvars lhsty

         logTerm 5 "LHS term" lhstm_lin
         logTerm 5 "LHS type" lhsty_lin
         setHoleLHS (bindEnv fc env lhstm_lin)

         extendEnv env SubRefl nest lhstm_lin lhsty_lin

bindNotReq : FC -> Int -> Env Term vs -> (sub : SubVars pre vs) -> 
             Term vs -> Term pre
bindNotReq fc i [] SubRefl tm = embed tm
bindNotReq fc i (b :: env) SubRefl tm 
   = let tmptm = subst (Ref fc Bound (MN "arg" i)) tm 
         btm = bindNotReq fc (1 + i) env SubRefl tmptm in
         refToLocal (MN "arg" i) _ btm
bindNotReq fc i (b :: env) (KeepCons p) tm 
   = let tmptm = subst (Ref fc Bound (MN "arg" i)) tm 
         btm = bindNotReq fc (1 + i) env p tmptm in
         refToLocal (MN "arg" i) _ btm
bindNotReq fc i (b :: env) (DropCons p) tm 
   = bindNotReq fc i env p 
       (Bind fc _ (Pi (multiplicity b) Explicit (binderType b)) tm)

bindReq : FC -> Env Term vs -> (sub : SubVars pre vs) -> 
          Term pre -> Maybe ClosedTerm
bindReq fc env SubRefl tm = pure (bindEnv fc env tm)
bindReq fc (b :: env) (KeepCons p) tm 
   = do b' <- shrinkBinder b p
        bindReq fc env p 
           (Bind fc _ (Pi (multiplicity b) Explicit (binderType b')) tm)
bindReq fc (b :: env) (DropCons p) tm = bindReq fc env p tm

getReq : (vs : List Name) -> SubVars pre vs -> List Name
getReq vs SubRefl = vs
getReq _ (DropCons p) = getReq _ p
getReq (v :: vs) (KeepCons p) = v :: getReq _ p

getNotReq : (vs : List Name) -> SubVars pre vs -> List Name
getNotReq vs SubRefl = []
getNotReq (v :: vs) (DropCons p) = v :: getNotReq _ p
getNotReq _ (KeepCons p) = getNotReq _ p

-- Return whether any of the pattern variables are in a trivially empty
-- type, where trivally empty means one of:
--  * No constructors
--  * Every constructor of the family has a return type which conflicts with 
--    the given constructor's type
hasEmptyPat : Defs -> Env Term vars -> Term vars -> Core Bool
hasEmptyPat defs env (Bind fc x (PVar c ty) sc)
   = pure $ !(isEmpty defs !(nf defs env ty)) 
            || !(hasEmptyPat defs (PVar c ty :: env) sc)
hasEmptyPat defs env _ = pure False

-- Check a pattern clause, returning the component of the 'Case' expression it
-- represents, or Nothing if it's an impossible clause
export
checkClause : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              (mult : RigCount) -> (hashit : Bool) ->
              Int -> List ElabOpt -> NestedNames vars -> Env Term vars ->
              ImpClause -> Core (Maybe Clause)
checkClause mult hashit n opts nest env (ImpossibleClause fc lhs)
    = handleUnify
         (do lhs_raw <- lhsInCurrentNS nest lhs
             autoimp <- isAutoImplicits
             autoImplicits True
             (_, lhs) <- bindNames False lhs_raw
             autoImplicits autoimp

             log 5 $ "Checking " ++ show lhs
             logEnv 5 "In env" env
             (lhstm, lhstyg) <- 
                         elabTerm n (InLHS mult) opts nest env 
                                    (IBindHere fc PATTERN lhs) Nothing
             defs <- get Ctxt
             lhs <- normaliseHoles defs env lhstm
             if !(hasEmptyPat defs env lhs)
                then pure Nothing
                else throw (ValidCase fc env (Left lhs)))
         (\err => 
            case err of
                 ValidCase _ _ _ => throw err
                 WhenUnifying _ env l r err
                     => do defs <- get Ctxt
                           logTerm 10 "Impossible" !(normalise defs env l)
                           logTerm 10 "    ...and" !(normalise defs env r)
                           if !(impossibleOK defs !(nf defs env l)
                                                  !(nf defs env r))
                              then pure Nothing
                              else throw (ValidCase fc env (Right err))
                 _ => throw (ValidCase fc env (Right err)))
checkClause {vars} mult hashit n opts nest env (PatClause fc lhs_in rhs)
    = do (vars'  ** (sub', env', nest', lhstm', lhsty')) <- 
             checkLHS mult hashit n opts nest env fc lhs_in
         let rhsMode = case mult of
                            Rig0 => InType
                            _ => InExpr
         log 5 $ "Checking RHS " ++ show rhs
         rhstm <- wrapError (InRHS fc !(getFullName (Resolved n))) $
                       checkTermSub n rhsMode opts nest' env' env sub' rhs (gnf env' lhsty')
         clearHoleLHS

         logTerm 5 "RHS term" rhstm
         when hashit $ 
           do addHash lhstm'
              addHash rhstm

         -- If the rhs is a hole, record the lhs in the metadata because we 
         -- might want to split it interactively
         case rhstm of
              Meta _ _ _ _ => 
                 addLHS (getFC lhs_in) (length env) env' lhstm'
              _ => pure ()

         pure (Just (MkClause env' lhstm' rhstm))
checkClause {vars} mult hashit n opts nest env (WithClause fc lhs_in wval_raw cs)
    = do (vars'  ** (sub', env', nest', lhspat, reqty)) <- 
             checkLHS mult hashit n opts nest env fc lhs_in
         let wmode
               = case mult of
                      Rig0 => InType -- treat as used in type only
                      _ => InExpr

         (wval, gwvalTy) <- wrapError (InRHS fc !(getFullName (Resolved n))) $
                elabTermSub n wmode opts nest' env' env sub' wval_raw Nothing
         clearHoleLHS
         
         logTerm 5 "With value" wval
         logTerm 5 "Required type" reqty
         wvalTy <- getTerm gwvalTy
         defs <- get Ctxt
         wval <- normaliseHoles defs env' wval
         wvalTy <- normaliseHoles defs env' wvalTy

         let (wevars ** withSub) = keepOldEnv sub' (snd (findSubEnv env' wval))
         logTerm 5 "With value type" wvalTy
         log 5 $ "Using vars " ++ show wevars

         let Just wval = shrinkTerm wval withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #1")
         let Just wvalTy = shrinkTerm wvalTy withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #2")
         -- Should the env be normalised too? If the following 'impossible'
         -- error is ever thrown, that might be the cause!
         let Just wvalEnv = shrinkEnv env' withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #3")

         -- Abstracting over 'wval' in the scope of bNotReq in order
         -- to get the 'magic with' behaviour
         let wargn = MN "warg" 0
         let scenv = Pi RigW Explicit wvalTy :: wvalEnv

         wtyScope <- replace defs scenv !(nf defs scenv (weaken wval))
                            (Local fc (Just False) _ First)
                            !(nf defs scenv 
                                 (weaken (bindNotReq fc 0 env' withSub reqty)))
         let bNotReq = Bind fc wargn (Pi RigW Explicit wvalTy) wtyScope

         let Just wtype = bindReq fc env' withSub bNotReq
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #4")

         -- list of argument names - 'Just' means we need to match the name
         -- in the with clauses to find out what the pattern should be.
         -- 'Nothing' means it's the with pattern (so wargn)
         let wargNames 
                 = map Just (reverse (getReq _ withSub)) ++ 
                   Nothing :: reverse (map Just (getNotReq _ withSub))

         logTerm 5 "With function type" wtype 
         log 5 $ "Argument names " ++ show wargNames

         wname <- genWithName n
         widx <- addDef wname (newDef fc wname mult vars wtype Private None)
         let rhs_in = apply (IVar fc wname)
                        (map (maybe wval_raw (IVar fc)) wargNames)

         rhs <- wrapError (InRHS fc !(getFullName (Resolved n))) $
             checkTermSub n wmode opts nest' env' env sub' rhs_in 
                          (gnf env' reqty)

         -- Generate new clauses by rewriting the matched arguments
         cs' <- traverse (mkClauseWith 1 wname wargNames lhs_in) cs

         -- Elaborate the new definition here
         let wdef = IDef fc wname cs'
         processDecl [] nest env wdef

         pure (Just (MkClause env' lhspat rhs))
  where
    -- If it's 'KeepCons/SubRefl' in 'outprf', that means it was in the outer
    -- environment so we need to keep it in the same place in the 'with'
    -- function. Hence, turn it to KeepCons whatever
    keepOldEnv : (outprf : SubVars outer vs) -> SubVars vs' vs ->
                 (vs'' : List Name ** SubVars vs'' vs)
    keepOldEnv {vs} SubRefl p = (vs ** SubRefl)
    keepOldEnv {vs} p SubRefl = (vs ** SubRefl)
    keepOldEnv (DropCons p) (DropCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** DropCons rest)
    keepOldEnv (DropCons p) (KeepCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** KeepCons rest)
    keepOldEnv (KeepCons p) (DropCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** KeepCons rest)
    keepOldEnv (KeepCons p) (KeepCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** KeepCons rest)

    dropWithArgs : FC -> Nat -> RawImp -> 
                   Core (RawImp, List RawImp)
    dropWithArgs ploc Z tm = pure (tm, [])
    dropWithArgs ploc (S k) (IApp _ f arg)
        = do (tm, rest) <- dropWithArgs ploc k f
             pure (tm, arg :: rest)
    -- Shouldn't happen if parsed correctly, but there's no guarantee that
    -- inputs come from parsed source so throw an error.
    dropWithArgs ploc _ _ = throw (GenericMsg ploc "Badly formed 'with' clause")

    -- Get the arguments for the rewritten pattern clause of a with by looking
    -- up how the argument names matched
    getArgMatch : RawImp -> List (String, RawImp) ->
                  Maybe Name -> RawImp
    getArgMatch warg ms Nothing = warg
    getArgMatch warg ms (Just (UN n))
        = case lookup n ms of
               Nothing => Implicit fc True
               Just tm => tm
    getArgMatch warg ms _ = Implicit fc True

    getNewLHS : FC -> (drop : Nat) -> Name -> List (Maybe Name) ->
                RawImp -> RawImp -> Core RawImp
    getNewLHS ploc drop wname wargnames lhs_raw patlhs
        = do (mlhs_raw, wrest) <- dropWithArgs ploc drop patlhs
             autoimp <- isAutoImplicits
             autoImplicits True
             (_, lhs) <- bindNames False lhs_raw
             (_, mlhs) <- bindNames False mlhs_raw
             autoImplicits autoimp

             let (warg :: rest) = reverse wrest
                 | _ => throw (GenericMsg ploc "Badly formed 'with' clause")
             log 10 $ show lhs ++ " against " ++ show mlhs ++
                     " dropping " ++ show (warg :: rest)
             ms <- getMatch lhs mlhs
             log 10 $ "Matches: " ++ show ms
             let newlhs = apply (IVar ploc wname)
                                (map (getArgMatch warg ms) wargnames ++ rest)
             log 5 $ "New LHS: " ++ show newlhs
             pure newlhs

    -- Rewrite the clauses in the block to use an updated LHS.
    -- 'drop' is the number of additional with arguments we expect (i.e.
    -- the things to drop from the end before matching LHSs)
    mkClauseWith : (drop : Nat) -> Name -> List (Maybe Name) ->
                   RawImp -> ImpClause -> 
                   Core ImpClause
    mkClauseWith drop wname wargnames lhs (PatClause ploc patlhs rhs)
        = do newlhs <- getNewLHS ploc drop wname wargnames lhs patlhs
             pure (PatClause ploc newlhs rhs)
    mkClauseWith drop wname wargnames lhs (WithClause ploc patlhs rhs ws)
        = do newlhs <- getNewLHS ploc drop wname wargnames lhs patlhs
             ws' <- traverse (mkClauseWith (S drop) wname wargnames lhs) ws
             pure (WithClause ploc newlhs rhs ws')
    mkClauseWith drop wname wargnames lhs (ImpossibleClause ploc patlhs)
        = do newlhs <- getNewLHS ploc drop wname wargnames lhs patlhs
             pure (ImpossibleClause ploc newlhs)


nameListEq : (xs : List Name) -> (ys : List Name) -> Maybe (xs = ys)
nameListEq [] [] = Just Refl
nameListEq (x :: xs) (y :: ys) with (nameEq x y)
  nameListEq (x :: xs) (x :: ys) | (Just Refl) with (nameListEq xs ys)
    nameListEq (x :: xs) (x :: xs) | (Just Refl) | Just Refl= Just Refl
    nameListEq (x :: xs) (x :: ys) | (Just Refl) | Nothing = Nothing
  nameListEq (x :: xs) (y :: ys) | Nothing = Nothing
nameListEq _ _ = Nothing

-- Compile run time case trees for the given name
mkRunTime : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Name -> Core ()
mkRunTime n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | _ => pure ()
         let PMDef cargs tree_ct _ pats = definition gdef
              | _ => pure () -- not a function definition
         let ty = type gdef
         (rargs ** tree_rt) <- getPMDef (location gdef) RunTime n ty 
                                        !(traverse (toClause (location gdef)) pats)
         let Just Refl = nameListEq cargs rargs
                 | Nothing => throw (InternalError "WAT")
         addDef n (record { definition = PMDef cargs tree_ct tree_rt pats 
                          } gdef)
         pure ()
  where
    toClause : FC -> (vars ** (Env Term vars, Term vars, Term vars)) ->
               Core Clause
    toClause fc (_ ** (env, lhs, rhs)) 
        = do rhs_erased <- linearCheck fc Rig1 True env rhs
             pure $ MkClause env lhs rhs_erased

compileRunTime : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 Core ()
compileRunTime
    = do defs <- get Ctxt
         traverse_ mkRunTime (toCompile defs)
         defs <- get Ctxt
         put Ctxt (record { toCompile = [] } defs)

-- Calculate references for the given name, and recursively if they haven't
-- been calculated already
calcRefs : {auto c : Ref Ctxt Defs} ->
           (aTotal : Name) -> (fn : Name) -> Core ()
calcRefs at fn
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact fn (gamma defs)
              | _ => pure ()
         let PMDef cargs tree_ct _ pats = definition gdef
              | _ => pure () -- not a function definition
         let Nothing = refersToM gdef
              | Just _ => pure () -- already done
         let metas = getMetas tree_ct
         let refs = addRefs at metas tree_ct
         traverse_ addToSave (keys metas)

         logC 5 (do fulln <- getFullName fn
                    refns <- traverse getFullName (keys refs)
                    pure (show fulln ++ " refers to " ++ show refns))
         addDef fn (record { refersToM = Just refs } gdef)
         traverse_ (calcRefs at) (keys refs)

toPats : Clause -> (vs ** (Env Term vs, Term vs, Term vs))
toPats (MkClause {vars} env lhs rhs) 
    = (_ ** (env, lhs, rhs))

export
processDef : {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             List ElabOpt -> NestedNames vars -> Env Term vars -> FC ->
             Name -> List ImpClause -> Core ()
processDef opts nest env fc n_in cs_in
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
         nidx <- resolveName n
         cs <- traverse (checkClause mult hashit nidx opts nest env) cs_in
         let pats = map toPats (mapMaybe id cs)

         (cargs ** tree_ct) <- getPMDef fc CompileTime n ty 
                                        (mapMaybe id cs)
        
         logC 5 (do t <- toFullNames tree_ct
                    pure ("Case tree for " ++ show n ++ ": " ++ show t))

         -- Add compile time tree as a placeholder for the runtime tree,
         -- but we'll rebuild that in a later pass once all the case
         -- blocks etc are resolved
         addDef (Resolved nidx)
                  (record { definition = PMDef cargs tree_ct tree_ct pats
                          } gdef)

         let rmetas = getMetas tree_ct
         traverse_ addToSave (keys rmetas)
         let tymetas = getMetas (type gdef)
         traverse_ addToSave (keys tymetas)
         addToSave n
         log 10 $ "Saving from " ++ show n ++ ": " ++ show (keys rmetas)

         -- Flag this name as one which needs compiling
         defs <- get Ctxt
         put Ctxt (record { toCompile $= (n ::) } defs)

         when (not (InCase `elem` opts)) $
             do atotal <- toResolvedNames (NS ["Builtin"] (UN "assert_total"))
                calcRefs atotal (Resolved nidx)

                sc <- calculateSizeChange fc n
                setSizeChange fc n sc

         -- If we're not in a case tree, compile all the outstanding case
         -- trees
         when (not (elem InCase opts)) $
           compileRunTime

         cov <- checkCoverage nidx mult cs tree_ct
         setCovering fc n cov

  where
    simplePat : Term vars -> Bool
    simplePat (Local _ _ _ _) = True
    simplePat (Erased _) = True
    simplePat (As _ _ p) = simplePat p
    simplePat _ = False

    -- Is the clause returned from 'checkClause' a catch all clause, i.e.
    -- one where all the arguments are variables? If so, no need to do the
    -- (potentially expensive) coverage check
    catchAll : Maybe Clause -> Bool
    catchAll Nothing = False
    catchAll (Just (MkClause env lhs _))
       = all simplePat (getArgs lhs)
   
    -- Return 'Nothing' if the clause is impossible, otherwise return the
    -- original
    checkImpossible : Int -> RigCount -> ClosedTerm -> 
                      Core (Maybe ClosedTerm)
    checkImpossible n mult tm
        = do itm <- unelabNoPatvars [] tm
             handleUnify
               (do ctxt <- get Ctxt
                   log 3 $ "Checking for impossibility: " ++ show itm
                   ok <- checkClause mult False n [] (MkNested []) []
                                     (ImpossibleClause fc itm)
                   put Ctxt ctxt
                   maybe (pure Nothing) (\chktm => pure (Just tm)) ok)
               (\err => case err of
                             WhenUnifying _ env l r err
                               => do defs <- get Ctxt
                                     if !(impossibleOK defs !(nf defs env l) 
                                                            !(nf defs env r))
                                        then pure Nothing
                                        else pure (Just tm)
                             _ => pure (Just tm))

    checkCoverage : Int -> RigCount -> List (Maybe Clause) ->
                    CaseTree vs -> Core Covering
    checkCoverage n mult cs ctree
        = do missCase <- if any catchAll cs
                            then do log 3 $ "Catch all case in " ++ show n
                                    pure []
                            else getMissing fc (Resolved n) ctree
             logC 3 (do mc <- traverse toFullNames missCase
                        pure ("Initially missing in " ++ 
                                 show !(getFullName (Resolved n)) ++ ":\n" ++ 
                                showSep "\n" (map show mc)))
             missImp <- traverse (checkImpossible n mult) missCase
             let miss = mapMaybe id missImp
             if isNil miss
                then do [] <- getNonCoveringRefs fc (Resolved n)
                           | ns => toFullNames (NonCoveringCall ns)
                        pure IsCovering
                else pure (MissingCases miss)

