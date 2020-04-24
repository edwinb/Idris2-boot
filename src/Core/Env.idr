module Core.Env

import Core.TT

-- Environment containing types and values of local variables
public export
data Env : (tm : List Name -> Type) -> List Name -> Type where
     Nil : Env tm []
     (::) : Binder (tm vars) -> Env tm vars -> Env tm (x :: vars)

export
extend : (x : Name) -> Binder (tm vars) -> Env tm vars -> Env tm (x :: vars)
extend x = (::) {x}

export
length : Env tm xs -> Nat
length [] = 0
length (_ :: xs) = S (length xs)

export
lengthNoLet : Env tm xs -> Nat
lengthNoLet [] = 0
lengthNoLet (Let _ _ _ :: xs) = lengthNoLet xs
lengthNoLet (_ :: xs) = S (lengthNoLet xs)

export
namesNoLet : {xs : _} -> Env tm xs -> List Name
namesNoLet [] = []
namesNoLet (Let _ _ _ :: xs) = namesNoLet xs
namesNoLet {xs = x :: _} (_ :: env) = x :: namesNoLet env

public export
data IsDefined : Name -> List Name -> Type where
  MkIsDefined : {idx : Nat} -> RigCount -> .(IsVar n idx vars) ->
                IsDefined n vars

export
defined : {vars : _} ->
          (n : Name) -> Env Term vars ->
          Maybe (IsDefined n vars)
defined n [] = Nothing
defined {vars = x :: xs} n (b :: env)
    = case nameEq n x of
           Nothing => do MkIsDefined rig prf <- defined n env
                         pure (MkIsDefined rig (Later prf))
           Just Refl => Just (MkIsDefined (multiplicity b) First)

export
bindEnv : FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
bindEnv loc [] tm = tm
bindEnv loc (b :: env) tm
    = bindEnv loc env (Bind loc _ b tm)

revOnto : (xs, vs : _) -> reverseOnto xs vs = reverse vs ++ xs
revOnto xs [] = Refl
revOnto xs (v :: vs)
    = rewrite revOnto (v :: xs) vs in
        rewrite appendAssociative (reverse vs) [v] xs in
				  rewrite revOnto [v] vs in Refl

revNs : (vs, ns : List a) -> reverse ns ++ reverse vs = reverse (vs ++ ns)
revNs [] ns = rewrite appendNilRightNeutral (reverse ns) in Refl
revNs (v :: vs) ns
    = rewrite revOnto [v] vs in
        rewrite revOnto [v] (vs ++ ns) in
          rewrite sym (revNs vs ns) in
            rewrite appendAssociative (reverse ns) (reverse vs) [v] in
              Refl

-- Weaken by all the names at once at the end, to save multiple traversals
-- in big environments
-- Also reversing the names at the end saves significant time over concatenating
-- when environments get fairly big.
getBinderUnder : Weaken tm =>
                 {idx : Nat} ->
                 (ns : List Name) ->
                 .(IsVar x idx vars) -> Env tm vars ->
                 Binder (tm (reverseOnto vars ns))
getBinderUnder {idx = Z} {vars = v :: vs} ns First (b :: env)
    = rewrite revOnto vs (v :: ns) in map (weakenNs (reverse (v :: ns))) b
getBinderUnder {idx = S k} {vars = v :: vs} ns (Later lp) (b :: env)
    = getBinderUnder (v :: ns) lp env

export
getBinder : Weaken tm =>
            {idx : Nat} ->
            .(IsVar x idx vars) -> Env tm vars -> Binder (tm vars)
getBinder el env = getBinderUnder [] el env

-- Make a type which abstracts over an environment
-- Don't include 'let' bindings, since they have a concrete value and
-- shouldn't be generalised
export
abstractEnvType : FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
abstractEnvType fc [] tm = tm
abstractEnvType fc (Let c val ty :: env) tm
    = abstractEnvType fc env (Bind fc _ (Let c val ty) tm)
abstractEnvType fc (Pi c e ty :: env) tm
    = abstractEnvType fc env (Bind fc _ (Pi c e ty) tm)
abstractEnvType fc (b :: env) tm
    = abstractEnvType fc env (Bind fc _
						(Pi (multiplicity b) Explicit (binderType b)) tm)

-- As above, for the corresponding term
export
abstractEnv : FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
abstractEnv fc [] tm = tm
abstractEnv fc (Let c val ty :: env) tm
    = abstractEnv fc env (Bind fc _ (Let c val ty) tm)
abstractEnv fc (b :: env) tm
    = abstractEnv fc env (Bind fc _
						(Lam (multiplicity b) Explicit (binderType b)) tm)

-- As above, but abstract over all binders including lets
export
abstractFullEnvType : FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
abstractFullEnvType fc [] tm = tm
abstractFullEnvType fc (b :: env) tm
    = abstractFullEnvType fc env (Bind fc _
						(Pi (multiplicity b) Explicit (binderType b)) tm)

export
letToLam : Env Term vars -> Env Term vars
letToLam [] = []
letToLam (Let c val ty :: env) = Lam c Explicit ty :: letToLam env
letToLam (b :: env) = b :: letToLam env

mutual
	-- Quicker, if less safe, to store variables as a Nat, for quick comparison
  findUsed : Env Term vars -> List Nat -> Term vars -> List Nat
  findUsed env used (Local fc r idx p)
      = if elemBy eqNat idx used
           then used
           else assert_total (findUsedInBinder env (idx :: used)
                                               (getBinder p env))
    where
      eqNat : Nat -> Nat -> Bool
      eqNat i j = toIntegerNat i == toIntegerNat j
  findUsed env used (Meta _ _ _ args)
      = findUsedArgs env used args
    where
      findUsedArgs : Env Term vars -> List Nat -> List (Term vars) -> List Nat
      findUsedArgs env u [] = u
      findUsedArgs env u (a :: as)
          = findUsedArgs env (findUsed env u a) as
  findUsed env used (Bind fc x b tm)
      = assert_total $
          dropS (findUsed (b :: env)
                          (map S (findUsedInBinder env used b))
                          tm)
    where
      dropS : List Nat -> List Nat
      dropS [] = []
      dropS (Z :: xs) = dropS xs
      dropS (S p :: xs) = p :: dropS xs
  findUsed env used (App fc fn arg)
      = findUsed env (findUsed env used fn) arg
  findUsed env used (As fc s a p)
      = findUsed env (findUsed env used a) p
  findUsed env used (TDelayed fc r tm)
      = findUsed env used tm
  findUsed env used (TDelay fc r ty tm)
      = findUsed env (findUsed env used ty) tm
  findUsed env used (TForce fc r tm)
      = findUsed env used tm
  findUsed env used _ = used

  findUsedInBinder : Env Term vars -> List Nat ->
										 Binder (Term vars) -> List Nat
  findUsedInBinder env used (Let _ val ty)
    = findUsed env (findUsed env used val) ty
  findUsedInBinder env used (PLet _ val ty)
    = findUsed env (findUsed env used val) ty
  findUsedInBinder env used b = findUsed env used (binderType b)

toVar : (vars : List Name) -> Nat -> Maybe (Var vars)
toVar (v :: vs) Z = Just (MkVar First)
toVar (v :: vs) (S k)
   = do MkVar prf <- toVar vs k
        Just (MkVar (Later prf))
toVar _ _ = Nothing

export
findUsedLocs : Env Term vars -> Term vars -> List (Var vars)
findUsedLocs env tm
    = mapMaybe (toVar _) (findUsed env [] tm)

isUsed : Nat -> List (Var vars) -> Bool
isUsed n [] = False
isUsed n (v :: vs) = n == varIdx v || isUsed n vs

mkShrinkSub : (vars : _) -> List (Var (n :: vars)) ->
              (newvars ** SubVars newvars (n :: vars))
mkShrinkSub [] els
    = if isUsed 0 els
         then (_ ** KeepCons SubRefl)
         else (_ ** DropCons SubRefl)
mkShrinkSub (x :: xs) els
    = let (_ ** subRest) = mkShrinkSub xs (dropFirst els) in
					if isUsed 0 els
				     then (_ ** KeepCons subRest)
				     else (_ ** DropCons subRest)

mkShrink : List (Var vars) ->
           (newvars ** SubVars newvars vars)
mkShrink {vars = []} xs = (_ ** SubRefl)
mkShrink {vars = v :: vs} xs = mkShrinkSub _ xs

-- Find the smallest subset of the environment which is needed to type check
-- the given term
export
findSubEnv : Env Term vars -> Term vars ->
						 (vars' : List Name ** SubVars vars' vars)
findSubEnv env tm = mkShrink (findUsedLocs env tm)

export
shrinkEnv : Env Term vars -> SubVars newvars vars -> Maybe (Env Term newvars)
shrinkEnv env SubRefl = Just env
shrinkEnv (b :: env) (DropCons p) = shrinkEnv env p
shrinkEnv (b :: env) (KeepCons p)
    = do env' <- shrinkEnv env p
         b' <- shrinkBinder b p
         pure (b' :: env')


