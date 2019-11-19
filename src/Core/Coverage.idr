module Core.Coverage

import Core.CaseTree
import Core.Context
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

import Data.NameMap

%default covering

-- Return whether any part of the type conflicts in such a way that they
-- can't possibly be equal (i.e. mismatched constructor)
conflict : Defs -> NF vars -> Name -> Core Bool
conflict defs nfty n
    = do Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure False
         case (definition gdef, type gdef) of
              (DCon t arity, dty)
                  => conflictNF nfty !(nf defs [] dty)
              _ => pure False
  where
    mutual
      conflictArgs : List (Closure vars) -> List (Closure []) -> Core Bool
      conflictArgs [] [] = pure False
      conflictArgs (c :: cs) (c' :: cs')
          = do cnf <- evalClosure defs c
               cnf' <- evalClosure defs c'
               pure $ !(conflictNF cnf cnf') || !(conflictArgs cs cs')
      conflictArgs _ _ = pure False

      conflictNF : NF vars -> NF [] -> Core Bool
      conflictNF t (NBind fc x b sc)
          = conflictNF t !(sc defs (toClosure defaultOpts [] (Erased fc)))
      conflictNF (NDCon _ n t a args) (NDCon _ n' t' a' args')
          = if t == t'
               then conflictArgs args args'
               else pure True
      conflictNF (NTCon _ n t a args) (NTCon _ n' t' a' args')
          = if n == n'
               then conflictArgs args args'
               else pure True
      conflictNF (NPrimVal _ c) (NPrimVal _ c') = pure (c /= c')
      conflictNF _ _ = pure False

-- Return whether the given type is definitely empty (due to there being
-- no constructors which can possibly match it.)
export
isEmpty : Defs -> NF vars -> Core Bool
isEmpty defs (NTCon fc n t a args)
     = case !(lookupDefExact n (gamma defs)) of
            Just (TCon _ _ _ _ _ cons)
                 => allM (conflict defs (NTCon fc n t a args)) cons
            _ => pure False
isEmpty defs _ = pure False

-- Need this to get a NF from a Term; the names are free in any case
freeEnv : FC -> (vs : List Name) -> Env Term vs
freeEnv fc [] = []
freeEnv fc (n :: ns) = PVar RigW Explicit (Erased fc) :: freeEnv fc ns

-- Given a normalised type, get all the possible constructors for that
-- type family, with their type, name, tag, and arity
getCons : Defs -> NF vars -> Core (List (NF [], Name, Int, Nat))
getCons defs (NTCon _ tn _ _ _)
    = case !(lookupDefExact tn (gamma defs)) of
           Just (TCon _ _ _ _ _ cons) =>
                do cs' <- traverse addTy cons
                   pure (mapMaybe id cs')
           _ => pure []
  where
    addTy : Name -> Core (Maybe (NF [], Name, Int, Nat))
    addTy cn
        = do Just gdef <- lookupCtxtExact cn (gamma defs)
                  | _ => pure Nothing
             case (definition gdef, type gdef) of
                  (DCon t arity, ty) =>
                        pure (Just (!(nf defs [] ty), cn, t, arity))
                  _ => pure Nothing
getCons defs _ = pure []

emptyRHS : FC -> CaseTree vars -> CaseTree vars
emptyRHS fc (Case idx el sc alts) = Case idx el sc (map emptyRHSalt alts)
  where
    emptyRHSalt : CaseAlt vars -> CaseAlt vars
    emptyRHSalt (ConCase n t args sc) = ConCase n t args (emptyRHS fc sc)
    emptyRHSalt (DelayCase c arg sc) = DelayCase c arg (emptyRHS fc sc)
    emptyRHSalt (ConstCase c sc) = ConstCase c (emptyRHS fc sc)
    emptyRHSalt (DefaultCase sc) = DefaultCase (emptyRHS fc sc)
emptyRHS fc (STerm s) = STerm (Erased fc)
emptyRHS fc sc = sc

mkAlt : FC -> CaseTree vars -> (Name, Int, Nat) -> CaseAlt vars
mkAlt fc sc (cn, t, ar)
    = ConCase cn t (map (MN "m") (take ar [0..]))
              (weakenNs _ (emptyRHS fc sc))

altMatch : CaseAlt vars -> CaseAlt vars -> Bool
altMatch _ (DefaultCase _) = True
altMatch (DelayCase _ _ t) (DelayCase _ _ t') = True
altMatch (ConCase _ t _ _) (ConCase _ t' _ _) = t == t'
altMatch (ConstCase c _) (ConstCase c' _) = c == c'
altMatch _ _ = False

-- Given a type and a list of case alternatives, return the
-- well-typed alternatives which were *not* in the list
getMissingAlts : FC -> Defs -> NF vars -> List (CaseAlt vars) ->
                 Core (List (CaseAlt vars))
-- If it's a primitive, there's too many to reasonably check, so require a
-- catch all
getMissingAlts fc defs (NPrimVal _ c) alts
    = if any isDefault alts
         then pure []
         else pure [DefaultCase (Unmatched "Coverage check")]
  where
    isDefault : CaseAlt vars -> Bool
    isDefault (DefaultCase _) = True
    isDefault _ = False
-- Similarly for types
getMissingAlts fc defs (NType _) alts
    = if any isDefault alts
         then pure []
         else pure [DefaultCase (Unmatched "Coverage check")]
  where
    isDefault : CaseAlt vars -> Bool
    isDefault (DefaultCase _) = True
    isDefault _ = False
getMissingAlts fc defs nfty alts
    = do allCons <- getCons defs nfty
         pure (filter (noneOf alts)
                 (map (mkAlt fc (Unmatched "Coverage check") . snd) allCons))
  where
    -- Return whether the alternative c matches none of the given cases in alts
    noneOf : List (CaseAlt vars) -> CaseAlt vars -> Bool
    noneOf alts c = not $ any (altMatch c) alts

-- Mapping of variable to constructor tag already matched for it
KnownVars : List Name -> Type -> Type
KnownVars vars a = List (Var vars, a)

getName : {idx : Nat} -> {vars : List Name} -> .(IsVar n idx vars) -> Name
getName {vars = v :: _} First = v
getName (Later p) = getName p

showK : Show a => KnownVars ns a -> String
showK {a} xs = show (map aString xs)
  where
    aString : (Var vars, a) -> (Name, a)
    aString (MkVar v, t) = (getName v, t)

weakenNs : (args : List Name) -> KnownVars vars a -> KnownVars (args ++ vars) a
weakenNs args [] = []
weakenNs {vars} args ((MkVar p, t) :: xs)
  = (insertVarNames _ {outer = []} {ns=args} {inner=vars} p, t)
         :: weakenNs args xs

findTag : IsVar n idx vars -> KnownVars vars a -> Maybe a
findTag v [] = Nothing
findTag v ((v', t) :: xs)
    = if sameVar (MkVar v) v'
         then Just t
         else findTag v xs

addNot : IsVar n idx vars -> Int -> KnownVars vars (List Int) ->
         KnownVars vars (List Int)
addNot v t [] = [(MkVar v, [t])]
addNot v t ((v', ts) :: xs)
    = if sameVar (MkVar v) v'
         then ((v', t :: ts) :: xs)
         else ((v', ts) :: addNot v t xs)

tagIs : Int -> CaseAlt vars -> Bool
tagIs t (ConCase _ t' _ _) = t == t'
tagIs t (ConstCase _ _) = False
tagIs t (DelayCase _ _ _) = False
tagIs t (DefaultCase _) = True

tagIsNot : List Int -> CaseAlt vars -> Bool
tagIsNot ts (ConCase _ t' _ _) = not (t' `elem` ts)
tagIsNot ts (ConstCase _ _) = True
tagIsNot ts (DelayCase _ _ _) = True
tagIsNot ts (DefaultCase _) = False

-- Replace a default case with explicit branches for the constructors.
-- This is easier than checking whether a default is needed when traversing
-- the tree (just one constructor lookup up front).
replaceDefaults : FC -> Defs -> NF vars -> List (CaseAlt vars) ->
                  Core (List (CaseAlt vars))
-- Leave it alone if it's a primitive type though, since we need the catch
-- all case there
replaceDefaults fc defs (NPrimVal _ _) cs = pure cs
replaceDefaults fc defs (NType _) cs = pure cs
replaceDefaults fc defs nfty cs
    = do cs' <- traverse rep cs
         pure (dropRep (concat cs'))
  where
    rep : CaseAlt vars -> Core (List (CaseAlt vars))
    rep (DefaultCase sc)
        = do allCons <- getCons defs nfty
             pure (map (mkAlt fc sc . snd) allCons)
    rep c = pure [c]

    dropRep : List (CaseAlt vars) -> List (CaseAlt vars)
    dropRep [] = []
    dropRep (c@(ConCase n t args sc) :: rest)
          -- assumption is that there's no defaultcase in 'rest' because
          -- we've just removed it
        = c :: dropRep (filter (not . tagIs t) rest)
    dropRep (c :: rest) = c :: dropRep rest

-- Traverse a case tree and refine the arguments while matching, so that
-- when we reach a leaf we know what patterns were used to get there,
-- and return those patterns.
-- The returned patterns are those arising from the *missing* cases
buildArgs : FC -> Defs ->
            KnownVars vars Int -> -- Things which have definitely match
            KnownVars vars (List Int) -> -- Things an argument *can't* be
                                    -- (because a previous case matches)
            List ClosedTerm -> -- ^ arguments, with explicit names
            CaseTree vars -> Core (List (List ClosedTerm))
buildArgs fc defs known not ps cs@(Case {name = var} idx el ty altsIn)
  -- If we've already matched on 'el' in this branch, restrict the alternatives
  -- to the tag we already know. Otherwise, add missing cases and filter out
  -- the ones it can't possibly be (the 'not') because a previous case
  -- has matched.
    = do let fenv = freeEnv fc _
         nfty <- nf defs fenv ty
         alts <- replaceDefaults fc defs nfty altsIn
         let alts' = alts ++ !(getMissingAlts fc defs nfty alts)
         let altsK = maybe alts' (\t => filter (tagIs t) alts')
                              (findTag el known)
         let altsN = maybe altsK (\ts => filter (tagIsNot ts) altsK)
                              (findTag el not)
         buildArgsAlt not altsN
  where
    buildArgAlt : KnownVars vars (List Int) ->
                  CaseAlt vars -> Core (List (List ClosedTerm))
    buildArgAlt not' (ConCase n t args sc)
        = do let con = Ref fc (DataCon t (length args)) n
             let ps' = map (substName var
                             (apply fc
                                    con (map (Ref fc Bound) args))) ps
             buildArgs fc defs (weakenNs args ((MkVar el, t) :: known))
                               (weakenNs args not') ps' sc
    buildArgAlt not' (DelayCase t a sc)
        = let ps' = map (substName var (TDelay fc LUnknown
                                             (Ref fc Bound t)
                                             (Ref fc Bound a))) ps in
              buildArgs fc defs (weakenNs [t,a] known) (weakenNs [t,a] not')
                                ps' sc
    buildArgAlt not' (ConstCase c sc)
        = do let ps' = map (substName var (PrimVal fc c)) ps
             buildArgs fc defs known not' ps' sc
    buildArgAlt not' (DefaultCase sc)
        = buildArgs fc defs known not' ps sc

    buildArgsAlt : KnownVars vars (List Int) -> List (CaseAlt vars) ->
                   Core (List (List ClosedTerm))
    buildArgsAlt not' [] = pure []
    buildArgsAlt not' (c@(ConCase _ t _ _) :: cs)
        = pure $ !(buildArgAlt not' c) ++
                 !(buildArgsAlt (addNot el t not') cs)
    buildArgsAlt not' (c :: cs)
        = pure $ !(buildArgAlt not' c) ++ !(buildArgsAlt not' cs)

buildArgs fc defs known not ps (STerm vs)
    = pure [] -- matched, so return nothing
buildArgs fc defs known not ps (Unmatched msg)
    = pure [ps] -- unmatched, so return it
buildArgs fc defs known not ps Impossible
    = pure [] -- not a possible match, so return nothing

-- Traverse a case tree and return pattern clauses which are not
-- matched. These might still be invalid patterns, or patterns which are covered
-- elsewhere (turning up due to overlapping clauses) so the results should be
-- checked
export
getMissing : {auto c : Ref Ctxt Defs} ->
             FC -> Name -> CaseTree vars ->
             Core (List ClosedTerm)
getMissing fc n ctree
   = do defs <- get Ctxt
        let psIn = map (Ref fc Bound) vars
        pats <- buildArgs fc defs [] [] psIn ctree
        pure (map (apply fc (Ref fc Func n)) pats)

-- For the given name, get the names it refers to which are not themselves
-- covering
export
getNonCoveringRefs : {auto c : Ref Ctxt Defs} ->
                     FC -> Name -> Core (List Name)
getNonCoveringRefs fc n
   = do defs <- get Ctxt
        Just d <- lookupCtxtExact n (gamma defs)
           | Nothing => throw (UndefinedName fc n)
        filterM (notCovering defs) (mapMaybe noAssert (toList (refersTo d)))
  where
    noAssert : (Name, Bool) -> Maybe Name
    noAssert (n, True) = Nothing
    noAssert (n, False) = Just n

    notCovering : Defs -> Name -> Core Bool
    notCovering defs n
        = case !(lookupCtxtExact n (gamma defs)) of
               Just def => case isCovering (totality def) of
                                IsCovering => pure False
                                _ => pure True
               _ => pure False
