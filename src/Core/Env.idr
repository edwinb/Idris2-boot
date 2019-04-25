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
length (x :: xs) = S (length xs)

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
                 Binder (tm (reverse ns ++ vars))
getBinderUnder {idx = Z} {vars = v :: vs} ns First (b :: env) 
    = rewrite appendAssociative (reverse ns) [v] vs in
			 rewrite revNs [v] ns in
         map (weakenNs (reverse (v :: ns))) b
getBinderUnder {idx = S k} {vars = v :: vs} ns (Later lp) (b :: env) 
    = rewrite appendAssociative (reverse ns) [v] vs in
			 rewrite revNs [v] ns in
         getBinderUnder (v :: ns) lp env

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

