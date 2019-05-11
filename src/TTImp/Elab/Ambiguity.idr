module TTImp.Elab.Ambiguity

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
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
