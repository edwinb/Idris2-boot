module TTImp.Elab.Ambiguity

import Core.Context
import Core.Core
import Core.Env
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
                   {auto u : Ref UST UState} ->
                   {auto e : Ref EST (EState vars)} ->
                   RigCount -> ElabInfo -> Env Term vars -> 
                   FC -> AltType -> List RawImp -> Maybe (Glued vars) ->
                   Core (Term vars, Glued vars)
checkAlternative rig elabinfo env fc (UniqueDefault def) alts mexpected
    = throw (InternalError "default alternatives not implemented")
checkAlternative rig elabinfo env fc uniq alts mexpected
    = do expected <- maybe (do nm <- genName "altTy"
                               ty <- metaVar fc Rig0 env nm (TType fc)
                               pure (gnf env ty))
                           pure mexpected
         let solvemode = case elabMode elabinfo of
                              InLHS c => InLHS
                              _ => InTerm
         solveConstraints solvemode Normal
         defs <- get Ctxt
         delayOnFailure fc rig env expected ambiguous $ 
            (\delayed => 
               do defs <- get Ctxt
                  -- If we don't know the target type, try again later
                  when (not delayed && 
                        !(holeIn (gamma defs) !(getTerm expected))) $
                    throw (AllFailed [])
                  let alts' = alts -- pruneByType defs expected alts TODO
                  logGlue 5 ("Ambiguous elaboration " ++ show alts' ++ 
                             "\nTarget type ") env expected
                  let tryall = case uniq of
                                    FirstSuccess => anyOne fc
                                    _ => exactlyOne fc env
                  tryall (map (\t => 
                      (getName t, 
                       do res <- checkImp rig elabinfo env t (Just expected)
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
                  do Just (Hole _) <- lookupDefExact (Resolved idx) gam
                          | Nothing => pure False
                     pure True
               _ => pure False

