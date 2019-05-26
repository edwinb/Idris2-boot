module TTImp.BindImplicits

import Core.Context
import Core.Core
import Core.TT
import TTImp.TTImp
import TTImp.Utils

import Control.Monad.State

%default covering

getUnique : List String -> String -> String
getUnique xs x = if x `elem` xs then getUnique xs (x ++ "'") else x

-- Rename the IBindVars in a term. Anything which appears in the list 'renames'
-- should be renamed, to something which is *not* in the list 'used'
export
renameIBinds : (renames : List String) -> 
               (used : List String) -> 
               RawImp -> State (List (String, String)) RawImp
renameIBinds rs us (IPi fc c p (Just (UN n)) ty sc)
    = if n `elem` rs 
         then let n' = getUnique (rs ++ us) n
                  sc' = substNames (map UN (filter (/= n) us)) 
                                   [(UN n, IVar fc (UN n'))] sc in
              do scr <- renameIBinds rs (n' :: us) sc'
                 ty' <- renameIBinds rs us ty
                 upds <- get
                 put (with List ((n, n') :: upds))
                 pure $ IPi fc c p (Just (UN n')) ty' scr
         else do scr <- renameIBinds rs us sc
                 ty' <- renameIBinds rs us ty
                 pure $ IPi fc c p (Just (UN n)) ty' scr
renameIBinds rs us (IPi fc c p n ty sc)
    = pure $ IPi fc c p n !(renameIBinds rs us ty) !(renameIBinds rs us sc)
renameIBinds rs us (ILam fc c p n ty sc)
    = pure $ ILam fc c p n !(renameIBinds rs us ty) !(renameIBinds rs us sc)
renameIBinds rs us (IApp fc fn arg)
    = pure $ IApp fc !(renameIBinds rs us fn) !(renameIBinds rs us arg)
renameIBinds rs us (IImplicitApp fc fn n arg)
    = pure $ IImplicitApp fc !(renameIBinds rs us fn) n !(renameIBinds rs us arg)
renameIBinds rs us (IAs fc s n pat)
    = pure $ IAs fc s n !(renameIBinds rs us pat)
renameIBinds rs us (IMustUnify fc r pat)
    = pure $ IMustUnify fc r !(renameIBinds rs us pat)
renameIBinds rs us (IDelayed fc r t)
    = pure $ IDelayed fc r !(renameIBinds rs us t)
renameIBinds rs us (IDelay fc t)
    = pure $ IDelay fc !(renameIBinds rs us t)
renameIBinds rs us (IForce fc t)
    = pure $ IForce fc !(renameIBinds rs us t)
renameIBinds rs us (IAlternative fc u alts)
    = pure $ IAlternative fc u !(traverse (renameIBinds rs us) alts)
renameIBinds rs us (IBindVar fc n)
    = if n `elem` rs
         then do let n' = getUnique (rs ++ us) n
                 upds <- get
                 put (with List ((n, n') :: upds))
                 pure $ IBindVar fc n'
         else pure $ IBindVar fc n
renameIBinds rs us tm = pure $ tm

export
doBind : List (String, String) -> RawImp -> RawImp
doBind [] tm = tm
doBind ns (IVar fc (UN n))
    = maybe (IVar fc (UN n))
            (\n' => IBindVar fc n')
            (lookup n ns)
doBind ns (IPi fc rig p mn aty retty)
    = let ns' = case mn of
                     Just (UN n) => filter (\x => fst x /= n) ns
                     _ => ns in
          IPi fc rig p mn (doBind ns' aty) (doBind ns' retty)
doBind ns (ILam fc rig p mn aty sc)
    = let ns' = case mn of
                     Just (UN n) => filter (\x => fst x /= n) ns
                     _ => ns in
          ILam fc rig p mn (doBind ns' aty) (doBind ns' sc)
doBind ns (IApp fc fn av)
    = IApp fc (doBind ns fn) (doBind ns av)
doBind ns (IImplicitApp fc fn n av)
    = IImplicitApp fc (doBind ns fn) n (doBind ns av)
doBind ns (IAs fc s n pat)
    = IAs fc s n (doBind ns pat)
doBind ns (IMustUnify fc r pat)
    = IMustUnify fc r (doBind ns pat)
doBind ns (IAlternative fc u alts)
    = IAlternative fc u (map (doBind ns) alts)
doBind ns tm = tm

export
bindNames : {auto c : Ref Ctxt Defs} ->
            (arg : Bool) -> RawImp -> Core (List Name, RawImp)
bindNames arg tm
    = if !isAutoImplicits
         then do let ns = nub (findBindableNames arg [] [] tm)
                 pure (map UN (map snd ns), doBind ns tm)
         else pure ([], tm)

export
bindTypeNames : {auto c : Ref Ctxt Defs} ->
                List Name -> RawImp-> Core RawImp
bindTypeNames env tm
    = if !isAutoImplicits
         then do let ns = nub (findBindableNames True env [] tm)
                 pure (doBind ns tm)
         else pure tm

export
bindTypeNamesUsed : {auto c : Ref Ctxt Defs} ->
                    List String -> List Name -> RawImp -> Core RawImp
bindTypeNamesUsed used env tm
    = if !isAutoImplicits
         then do let ns = nub (findBindableNames True env used tm)
                 pure (doBind ns tm)
         else pure tm

export
piBindNames : FC -> List Name -> RawImp -> RawImp
piBindNames loc env tm
    = let ns = nub (findBindableNames True env [] tm) in
          piBind (map fst ns) tm
  where
    piBind : List String -> RawImp -> RawImp
    piBind [] ty = ty
    piBind (n :: ns) ty 
       = IPi loc Rig0 Implicit (Just (UN n)) (Implicit loc False) (piBind ns ty)

