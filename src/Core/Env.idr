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

export
defined : {vars : _} ->
          (n : Name) -> Env Term vars -> 
          Maybe (idx ** (RigCount, IsVar n idx vars))
defined n [] = Nothing
defined {vars = x :: xs} n (b :: env)
    = case nameEq n x of
           Nothing => do (idx ** (rig, prf)) <- defined n env
                         pure (_ ** (rig, Later prf))
           Just Refl => Just (_ ** (multiplicity b, First))

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
export
getBinderUnder : Weaken tm => 
                 (ns : List Name) -> 
                 IsVar x idx vars -> Env tm vars -> 
                 Binder (tm (reverse ns ++ vars))
getBinderUnder {vars = v :: vs} ns First (b :: env) 
    = rewrite appendAssociative (reverse ns) [v] vs in
			 rewrite revNs [v] ns in
         map (weakenNs (reverse (v :: ns))) b
getBinderUnder {vars = v :: vs} ns (Later lp) (b :: env) 
    = rewrite appendAssociative (reverse ns) [v] vs in
			 rewrite revNs [v] ns in
         getBinderUnder (v :: ns) lp env

export
getBinder : Weaken tm => IsVar x idx vars -> Env tm vars -> Binder (tm vars)
getBinder el env = getBinderUnder [] el env

export
getLetBinderUnder : Weaken tm => 
                    (ns : List Name) -> 
                    IsVar x idx vars -> Env tm vars -> 
                    Maybe (tm (reverse ns ++ vars))
getLetBinderUnder {vars = v :: vs} ns First (Let mrig val ty :: env) 
    = rewrite appendAssociative (reverse ns) [v] vs in
			 rewrite revNs [v] ns in 
         Just (weakenNs (reverse (v :: ns)) val)
getLetBinderUnder ns First _ = Nothing
getLetBinderUnder {vars = v :: vs} ns (Later lp) (b :: env) 
    = rewrite appendAssociative (reverse ns) [v] vs in
			 rewrite revNs [v] ns in
         getLetBinderUnder (v :: ns) lp env

export
getLetBinder : Weaken tm => IsVar x idx vars -> Env tm vars -> Maybe (tm vars)
getLetBinder el env = getLetBinderUnder [] el env

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

