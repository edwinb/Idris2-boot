module TTImp.Elab.Ambiguity

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.TTImp

%default covering

export
expandAmbigName : {auto c : Ref Ctxt Defs} ->
                  {auto e : Ref EST (EState vars)} ->
                  ElabMode -> Env Term vars -> RawImp -> 
                  List (FC, Maybe (Maybe Name), RawImp) -> 
                  RawImp -> Maybe (Glued vars) -> Core RawImp
expandAmbigName (InLHS _) env orig args (IBindVar fc n) exp
    = do est <- get EST
         if n `elem` lhsPatVars est
            then pure $ IMustUnify fc "Non linear pattern variable" orig
            else pure $ orig
expandAmbigName mode env orig args (IVar fc x) exp
    = do defs <- get Ctxt
         -- TODO: Look up 'x' in nested names, when we have them
         case defined x env of
              Just _ => 
                if isNil args || notLHS mode 
                   then pure $ orig
                   else pure $ IMustUnify fc "Name applied to arguments" orig
              Nothing => 
                 do est <- get EST
                    case !(lookupCtxtName x (gamma defs)) of
                         [] => pure orig
                         [nalt] => pure $ mkAlt defs est nalt
                         nalts => pure $ IAlternative fc Unique 
                                                (map (mkAlt defs est) nalts)
  where
    buildAlt : RawImp -> List (FC, Maybe (Maybe Name), RawImp) -> 
               RawImp
    buildAlt f [] = f
    buildAlt f ((fc', Nothing, a) :: as) 
        = buildAlt (IApp fc' f a) as
    buildAlt f ((fc', Just i, a) :: as) 
        = buildAlt (IImplicitApp fc' f i a) as
     
    isPrimAppF : Defs -> (Defs -> Maybe Name) -> Name -> RawImp -> Bool
    isPrimAppF defs pname n (IPrimVal _ _)
        = case pname defs of
               Nothing => False
               Just n' => dropNS n == n'
    isPrimAppF defs pname _ _ = False

    isPrimApp : Defs -> Name -> RawImp -> Bool
    isPrimApp defs fn arg
        = isPrimAppF defs fromIntegerName fn arg
        || isPrimAppF defs fromStringName fn arg
        || isPrimAppF defs fromCharName fn arg

    -- If it's not a constructor application, dot it
    wrapDot : Defs -> EState vars ->
              ElabMode -> Name -> List RawImp -> Def -> RawImp -> RawImp 
    wrapDot _ _ _ _ _ (DCon _ _) tm = tm
    wrapDot _ _ _ _ _ (TCon _ _ _ _ _ _) tm = tm
    -- Leave primitive applications alone, because they'll be inlined
    -- before compiling the case tree
    wrapDot defs est (InLHS _) n' [arg] _ tm 
       = if n' == Resolved (defining est) || isPrimApp defs n' arg
            then tm
            else IMustUnify fc "Not a constructor application or primitive" tm
    wrapDot defs est (InLHS _) n' _ _ tm 
       = if n' == Resolved (defining est)
            then tm
            else IMustUnify fc "Not a constructor application or primitive" tm
    wrapDot _ _ _ _ _ _ tm = tm


    mkTerm : Defs -> EState vars -> Name -> GlobalDef -> RawImp
    mkTerm defs est n def 
        = wrapDot defs est mode n (map (snd . snd) args)
                  (definition def) (buildAlt (IVar fc n) args)

    mkAlt : Defs -> EState vars -> (Name, Int, GlobalDef) -> RawImp
    mkAlt defs est (fullname, i, gdef) = mkTerm defs est (Resolved i) gdef

    notLHS : ElabMode -> Bool
    notLHS (InLHS _) = False
    notLHS _ = True

expandAmbigName mode env orig args (IApp fc f a) exp
    = expandAmbigName mode env orig 
                      ((fc, Nothing, a) :: args) f exp
expandAmbigName mode env orig args (IImplicitApp fc f n a) exp
    = expandAmbigName mode env orig 
                      ((fc, Just n, a) :: args) f exp
expandAmbigName elabmode env orig args tm exp = pure orig

stripDelay : Defs -> NF vars -> NF vars
stripDelay defs (NDelayed fc r t) = t
stripDelay defs tm = tm

data TypeMatch = Concrete | Poly | NoMatch

mutual
  mightMatchD : Defs -> NF vars -> NF [] -> Core TypeMatch
  mightMatchD defs l r 
      = mightMatch defs (stripDelay defs l) (stripDelay defs r)

  mightMatchArg : Defs -> 
                  Closure vars -> Closure [] -> 
                  Core Bool
  mightMatchArg defs l r
      = case !(mightMatchD defs !(evalClosure defs l) !(evalClosure defs r)) of
             NoMatch => pure False
             _ => pure True

  mightMatchArgs : Defs ->
                   List (Closure vars) -> List (Closure []) ->
                   Core Bool
  mightMatchArgs defs [] [] = pure True
  mightMatchArgs defs (x :: xs) (y :: ys)
      = do amatch <- mightMatchArg defs x y
           if amatch
              then mightMatchArgs defs xs ys
              else pure False
  mightMatchArgs _ _ _ = pure False

  mightMatch : Defs -> NF vars -> NF [] -> Core TypeMatch
  mightMatch defs target (NBind fc n (Pi _ _ _) sc)
      = mightMatchD defs target !(sc defs (toClosure defaultOpts [] (Erased fc)))
  mightMatch defs (NTCon _ n t a args) (NTCon _ n' t' a' args')
      = if n == n' 
           then do amatch <- mightMatchArgs defs args args'
                   if amatch then pure Concrete else pure NoMatch
           else pure NoMatch
  mightMatch defs (NDCon _ n t a args) (NDCon _ n' t' a' args')
      = if t == t' 
           then do amatch <- mightMatchArgs defs args args'
                   if amatch then pure Concrete else pure NoMatch
           else pure NoMatch
  mightMatch defs (NPrimVal _ x) (NPrimVal _ y) 
      = if x == y then pure Concrete else pure NoMatch
  mightMatch defs (NType _) (NType _) = pure Concrete
  mightMatch defs (NApp _ _ _) _ = pure Poly
  mightMatch defs (NErased _) _ = pure Poly
  mightMatch defs _ (NApp _ _ _) = pure Poly
  mightMatch defs _ (NErased _) = pure Poly
  mightMatch _ _ _ = pure NoMatch

-- Return true if the given name could return something of the given target type
couldBeName : Defs -> NF vars -> Name -> Core TypeMatch
couldBeName defs target n
    = case !(lookupTyExact n (gamma defs)) of
           Nothing => pure Poly -- could be a local name, don't rule it out
           Just ty => mightMatchD defs target !(nf defs [] ty)

couldBeFn : Defs -> NF vars -> RawImp -> Core TypeMatch
couldBeFn defs ty (IVar _ n) = couldBeName defs ty n
couldBeFn defs ty _ = pure Poly

-- Returns Nothing if there's no possibility the expression's type matches
-- the target type
-- Just (True, app) if it's a match on concrete return type
-- Just (False, app) if it might be a match due to being polymorphic
couldBe : Defs -> NF vars -> RawImp -> Core (Maybe (Bool, RawImp))
couldBe {vars} defs ty@(NTCon _ n _ _ _) app 
   = case !(couldBeFn {vars} defs ty (getFn app)) of
          Concrete => pure $ Just (True, app)
          Poly => pure $ Just (False, app)
          NoMatch => pure Nothing
couldBe {vars} defs ty@(NPrimVal _ _) app 
   = case !(couldBeFn {vars} defs ty (getFn app)) of
          Concrete => pure $ Just (True, app)
          Poly => pure $ Just (False, app)
          NoMatch => pure Nothing
couldBe defs ty app = pure $ Just (False, app)


notOverloadable : Defs -> RawImp -> Core Bool
notOverloadable defs fn = notOverloadableFn (getFn fn)
  where
    notOverloadableFn : RawImp -> Core Bool
    notOverloadableFn (IVar _ n)
        = do Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure True
             pure (not (Overloadable `elem` flags gdef))
    notOverloadableFn _ = pure True

filterCore : (a -> Core Bool) -> List a -> Core (List a)
filterCore f [] = pure []
filterCore f (x :: xs)
    = do p <- f x
         xs' <- filterCore f xs
         if p then pure (x :: xs')
              else pure xs'

pruneByType : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              NF vars -> List RawImp -> 
              Core (List RawImp)
pruneByType target alts
    = do defs <- get Ctxt
         matches_in <- traverse (couldBe defs target) alts
         let matches = mapMaybe id matches_in
         res <- if or (map Delay (map fst matches))
                -- if there's any concrete matches, drop the ones marked
                -- as '%allow_overloads' from the possible set
                   then filterCore (notOverloadable defs) (map snd matches)
                   else pure (map snd matches)
         if isNil res
            then pure alts -- if none of them work, better to show all the errors
            else pure res


export
ambiguous : Error -> Bool
ambiguous (AmbiguousElab _ _ _) = True
ambiguous (AmbiguousName _ _) = True
ambiguous (AllFailed _) = True
ambiguous (InType _ _ err) = ambiguous err
ambiguous (InCon _ _ err) = ambiguous err
ambiguous (InLHS _ _ err) = ambiguous err
ambiguous (InRHS _ _ err) = ambiguous err
ambiguous (WhenUnifying _ _ _ _ err) = ambiguous err
ambiguous _ = False

getName : RawImp -> Maybe Name
getName (IVar _ n) = Just n
getName (IApp _ f _) = getName f
getName (IImplicitApp _ f _ _) = getName f
getName _ = Nothing

export
checkAlternative : {vars : _} ->
                   {auto c : Ref Ctxt Defs} ->
                   {auto m : Ref MD Metadata} ->
                   {auto u : Ref UST UState} ->
                   {auto e : Ref EST (EState vars)} ->
                   RigCount -> ElabInfo -> 
                   NestedNames vars -> Env Term vars -> 
                   FC -> AltType -> List RawImp -> Maybe (Glued vars) ->
                   Core (Term vars, Glued vars)
checkAlternative rig elabinfo nest env fc (UniqueDefault def) alts mexpected
    = do expected <- maybe (do nm <- genName "altTy"
                               ty <- metaVar fc Rig0 env nm (TType fc)
                               pure (gnf env ty))
                           pure mexpected
         let solvemode = case elabMode elabinfo of
                              InLHS c => InLHS
                              _ => InTerm
         solveConstraints solvemode Normal
         delayOnFailure fc rig env expected ambiguous $ 
            (\delayed => 
               do defs <- get Ctxt
                  alts' <- pruneByType !(getNF expected) alts
                  if delayed -- use the default if there's still ambiguity
                     then try 
                            (exactlyOne fc env 
                                (map (\t => 
                                   (getName t, 
                                    checkImp rig elabinfo nest env t 
                                             (Just expected))) alts'))
                            (checkImp rig elabinfo nest env def (Just expected))
                     else exactlyOne fc env
                           (map (\t => 
                             (getName t, 
                              checkImp rig elabinfo nest env t (Just expected)))
                              alts'))
checkAlternative rig elabinfo nest env fc uniq alts mexpected
    = do expected <- maybe (do nm <- genName "altTy"
                               ty <- metaVar fc Rig0 env nm (TType fc)
                               pure (gnf env ty))
                           pure mexpected
         let solvemode = case elabMode elabinfo of
                              InLHS c => InLHS
                              _ => InTerm
         solveConstraints solvemode Normal
         delayOnFailure fc rig env expected ambiguous $ 
            (\delayed => 
               do defs <- get Ctxt
                  alts' <- pruneByType !(getNF expected) alts
                  exp <- getTerm expected
                  -- If we don't know the target type on the first attempt, 
                  -- delay
--                   when (not delayed && 
--                         !(holeIn (gamma defs) exp)) $
--                     throw (AllFailed [])
                  -- We can't just use the old NF on the second attempt, 
                  -- because we might know more now, so recalculate it
                  let exp' = if delayed 
                                then gnf env exp
                                else expected

                  logGlueNF 5 ("Ambiguous elaboration " ++ show alts' ++ 
                               " at " ++ show fc ++
                               "\nTarget type ") env exp'
                  let tryall = case uniq of
                                    FirstSuccess => anyOne fc
                                    _ => exactlyOne fc env
                  tryall (map (\t => 
                      (getName t, 
                       do res <- checkImp rig elabinfo nest env t (Just exp')
                          -- Do it twice for interface resolution;
                          -- first pass gets the determining argument
                          -- (maybe rethink this, there should be a better
                          -- way that allows one pass)
                          solveConstraints solvemode Normal
                          solveConstraints solvemode Normal
                          log 10 $ show (getName t) ++ " success"
                          pure res)) alts'))
  where
    holeIn : Context GlobalDef -> Term vs -> Core Bool
    holeIn gam tm
        = case getFn tm of
               Meta _ _ idx _ =>
                  do Just (Hole _ _) <- lookupDefExact (Resolved idx) gam
                          | _ => pure False
                     pure True
               _ => pure False

