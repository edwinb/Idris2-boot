module TTImp.Interactive.MakeLemma

import Core.Context
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.TT

import TTImp.Unelab
import TTImp.TTImp
import TTImp.Utils

%default covering

used : RigCount -> Bool
used Rig0 = False
used _ = True

hiddenName : Name -> Bool
hiddenName (MN "_" _) = True
hiddenName _ = False

-- True if the variable appears guarded by a constructor in the term
bindable : Nat -> Term vars -> Bool
bindable p tm
    = case getFnArgs tm of
           (Ref _ (TyCon _ _) n, args) => any (bindable p) args
           (Ref _ (DataCon _ _) _, args) => any (bindable p) args
           (TDelayed _ _ t, args) => any (bindable p) (t :: args)
           (TDelay _ _ _ t, args) => any (bindable p) (t :: args)
           (TForce _ _ t, args) => any (bindable p) (t :: args)
           (Local _ _ p' _, []) => p == p'
           _ => False

bindableArg : Nat -> Term vars -> Bool
bindableArg p (Bind _ _ (Pi _ _ ty) sc)
   = bindable p ty || bindableArg (1 + p) sc
bindableArg p _ = False

getArgs : {auto c : Ref Ctxt Defs} ->
          Env Term vars -> Nat -> Term vars ->
          Core (List (Name, Maybe Name, PiInfo RawImp, RigCount, RawImp), RawImp)
getArgs {vars} env (S k) (Bind _ x (Pi c p ty) sc)
    = do ty' <- unelab env ty
         defs <- get Ctxt
         let x' = UN !(uniqueName defs (map nameRoot vars) (nameRoot x))
         (sc', ty) <- getArgs (Pi c p ty :: env) k (renameTop x' sc)
         -- Don't need to use the name if it's not used in the scope type
         let mn = case c of
                       RigW => case shrinkTerm sc (DropCons SubRefl) of
                                    Nothing => Just x'
                                    _ => Nothing
                       _ => Just x'
         let p' = if used c && not (bindableArg 0 sc) && not (hiddenName x)
                     then Explicit
                     else Implicit
         pure ((x, mn, p', c, ty') :: sc', ty)
getArgs env k ty
      = do ty' <- unelab env ty
           pure ([], ty')

mkType : FC -> List (Name, Maybe Name, PiInfo RawImp, RigCount, RawImp) ->
         RawImp -> RawImp
mkType loc [] ret = ret
mkType loc ((_, n, p, c, ty) :: rest) ret
    = IPi loc c p n ty (mkType loc rest ret)

mkApp : FC -> Name ->
        List (Name, Maybe Name, PiInfo RawImp, RigCount, RawImp) -> RawImp
mkApp loc n args
    = apply (IVar loc n) (mapMaybe getArg args)
  where
    getArg : (Name, Maybe Name, PiInfo RawImp, RigCount, RawImp) ->
             Maybe RawImp
    getArg (x, _, Explicit, _, _) = Just (IVar loc x)
    getArg _ = Nothing

-- Return a top level type for the lemma, and an expression which applies
-- the lemma to solve a hole with 'locs' arguments
export
makeLemma : {auto m : Ref MD Metadata} ->
            {auto c : Ref Ctxt Defs} ->
            FC -> Name -> Nat -> ClosedTerm ->
            Core (RawImp, RawImp)
makeLemma loc n nlocs ty
    = do (args, ret) <- getArgs [] nlocs ty
         pure (mkType loc args ret, mkApp loc n args)


