-- Representation of expressions ready for compiling
-- Type erased, explicit case trees
module Core.CompileExpr

import Core.FC
import Core.Name
import Core.TT

import Data.Vect

%default total

mutual
  ||| CExp - an expression ready for compiling.
  public export
  data CExp : List Name -> Type where
       CLocal : {idx : Nat} -> FC -> .(IsVar x idx vars) -> CExp vars
       CRef : FC -> Name -> CExp vars
       -- Lambda expression
       CLam : FC -> (x : Name) -> CExp (x :: vars) -> CExp vars
       -- Let bindings
       CLet : FC -> (x : Name) -> CExp vars -> CExp (x :: vars) -> CExp vars
       -- Application of a defined function. The length of the argument list is
       -- exactly the same length as expected by its definition (so saturate with
       -- lambdas if necessary, or overapply with additional CApps)
       CApp : FC -> CExp vars -> List (CExp vars) -> CExp vars
       -- A saturated constructor application
       CCon : FC -> Name -> (tag : Int) -> List (CExp vars) -> CExp vars
       -- Internally defined primitive operations
       COp : FC -> PrimFn arity -> Vect arity (CExp vars) -> CExp vars
       -- Externally defined primitive operations
       CExtPrim : FC -> (p : Name) -> List (CExp vars) -> CExp vars
       -- A forced (evaluated) value (TODO: is this right?)
       CForce : FC -> CExp vars -> CExp vars
       -- A delayed value (lazy? TODO: check)
       CDelay : FC -> CExp vars -> CExp vars
       -- A case match statement
       CConCase : FC -> (sc : CExp vars) -> List (CConAlt vars) -> Maybe (CExp vars) -> CExp vars
       CConstCase : FC -> (sc : CExp vars) -> List (CConstAlt vars) -> Maybe (CExp vars) -> CExp vars
       -- A primitive value
       CPrimVal : FC -> Constant -> CExp vars
       -- An erased value
       CErased : FC -> CExp vars
       -- Some sort of crash?
       CCrash : FC -> String -> CExp vars

  public export
  data CConAlt : List Name -> Type where
       MkConAlt : Name -> (tag : Int) -> (args : List Name) ->
                  CExp (args ++ vars) -> CConAlt vars

  public export
  data CConstAlt : List Name -> Type where
       MkConstAlt : Constant -> CExp vars -> CConstAlt vars

public export
data CDef : Type where
     -- Normal function definition
     MkFun : (args : List Name) -> CExp args -> CDef
     -- Constructor
     MkCon : (tag : Int) -> (arity : Nat) -> CDef
     -- A function which will fail at runtime (usually due to being a hole) so needs
     -- to run, discarding arguments, no matter how many arguments are passed
     MkError : CExp [] -> CDef

mutual
  export
  Show (CExp vars) where
    show (CLocal {x} _ y) = "!" ++ show x
    show (CRef _ x) = show x
    show (CLam _ x y) = "(%lam " ++ show x ++ " " ++ show y ++ ")"
    show (CLet _ x y z) = "(%let " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (CApp _ x xs)
        = assert_total $ "(" ++ show x ++ " " ++ show xs ++ ")"
    show (CCon _ x tag xs)
        = assert_total $ "(%con " ++ show x ++ " " ++ show tag ++ " " ++ show xs ++ ")"
    show (COp _ op xs)
        = assert_total $ "(" ++ show op ++ " " ++ show xs ++ ")"
    show (CExtPrim _ p xs)
        = assert_total $ "(%extern " ++ show p ++ " " ++ show xs ++ ")"
    show (CForce _ x) = "(%force " ++ show x ++ ")"
    show (CDelay _ x) = "(%delay " ++ show x ++ ")"
    show (CConCase _ sc xs def)
        = assert_total $ "(%case " ++ show sc ++ " " ++ show xs ++ " " ++ show def ++ ")"
    show (CConstCase _ sc xs def)
        = assert_total $ "(%case " ++ show sc ++ " " ++ show xs ++ " " ++ show def ++ ")"
    show (CPrimVal _ x) = show x
    show (CErased _) = "___"
    show (CCrash _ x) = "(CRASH " ++ show x ++ ")"

  export
  Show (CConAlt vars) where
    show (MkConAlt x tag args exp)
         = "(%concase " ++ show x ++ " " ++ show tag ++ " " ++
             show args ++ " " ++ show exp ++ ")"

  export
  Show (CConstAlt vars) where
    show (MkConstAlt x exp)
         = "(%constcase " ++ show x ++ " " ++ show exp ++ ")"

export
Show CDef where
  show (MkFun args exp) = show args ++ ": " ++ show exp
  show (MkCon tag arity) = "Constructor tag " ++ show tag ++ " arity " ++ show arity
  show (MkError exp) = "Error: " ++ show exp

mutual
  export
  thin : (n : Name) -> CExp (outer ++ inner) -> CExp (outer ++ n :: inner)
  thin n (CLocal fc prf) 
      = let MkVar var' = insertVar {n} _ prf in
            CLocal fc var'
  thin n (CRef fc x) = CRef fc x
  thin {outer} {inner} n (CLam fc x sc)
      = let sc' = thin {outer = x :: outer} {inner} n sc in
            CLam fc x sc'
  thin {outer} {inner} n (CLet fc x val sc)
      = let sc' = thin {outer = x :: outer} {inner} n sc in
            CLet fc x (thin n val) sc'
  thin n (CApp fc x xs)
      = CApp fc (thin n x) (assert_total (map (thin n) xs))
  thin n (CCon fc x tag xs)
      = CCon fc x tag (assert_total (map (thin n) xs))
  thin n (COp fc x xs)
      = COp fc x (assert_total (map (thin n) xs))
  thin n (CExtPrim fc p xs)
      = CExtPrim fc p (assert_total (map (thin n) xs))
  thin n (CForce fc x) = CForce fc (thin n x)
  thin n (CDelay fc x) = CDelay fc (thin n x)
  thin n (CConCase fc sc xs def)
      = CConCase fc (thin n sc) (assert_total (map (thinConAlt n) xs))
                 (assert_total (map (thin n) def))
  thin n (CConstCase fc sc xs def)
      = CConstCase fc (thin n sc) (assert_total (map (thinConstAlt n) xs))
                   (assert_total (map (thin n) def))
  thin n (CPrimVal fc x) = CPrimVal fc x
  thin n (CErased fc) = CErased fc
  thin n (CCrash fc x) = CCrash fc x

  thinConAlt : (n : Name) -> CConAlt (outer ++ inner) -> CConAlt (outer ++ n :: inner)
  thinConAlt {outer} {inner} n (MkConAlt x tag args sc)
        = let sc' : CExp ((args ++ outer) ++ inner)
                  = rewrite sym (appendAssociative args outer inner) in sc in
              MkConAlt x tag args
               (rewrite appendAssociative args outer (n :: inner) in
                        thin n sc')

  thinConstAlt : (n : Name) -> CConstAlt (outer ++ inner) -> CConstAlt (outer ++ n :: inner)
  thinConstAlt n (MkConstAlt x sc) = MkConstAlt x (thin n sc)

mutual
  export
  embed : CExp args -> CExp (args ++ vars)
  embed (CLocal fc prf) = CLocal fc (varExtend prf)
  embed (CRef fc n) = CRef fc n
  embed (CLam fc x sc) = CLam fc x (embed sc)
  embed (CLet fc x val sc) = CLet fc x (embed val) (embed sc)
  embed (CApp fc f args) = CApp fc (embed f) (assert_total (map embed args))
  embed (CCon fc n t args) = CCon fc n t (assert_total (map embed args))
  embed (COp fc p args) = COp fc p (assert_total (map embed args))
  embed (CExtPrim fc p args) = CExtPrim fc p (assert_total (map embed args))
  embed (CForce fc e) = CForce fc (embed e)
  embed (CDelay fc e) = CDelay fc (embed e)
  embed (CConCase fc sc alts def)
      = CConCase fc (embed sc) (assert_total (map embedAlt alts))
                 (assert_total (map embed def))
  embed (CConstCase fc sc alts def)
      = CConstCase fc (embed sc) (assert_total (map embedConstAlt alts))
                   (assert_total (map embed def))
  embed (CPrimVal fc c) = CPrimVal fc c
  embed (CErased fc) = CErased fc
  embed (CCrash fc msg) = CCrash fc msg

  embedAlt : CConAlt args -> CConAlt (args ++ vars)
  embedAlt {args} {vars} (MkConAlt n t as sc)
     = MkConAlt n t as (rewrite appendAssociative as args vars in embed sc)

  embedConstAlt : CConstAlt args -> CConstAlt (args ++ vars)
  embedConstAlt (MkConstAlt c sc) = MkConstAlt c (embed sc)

mutual
  export
  Weaken CExp where
    weaken = thin {outer = []} _

export
getFC : CExp args -> FC
getFC (CLocal fc y) = fc
getFC (CRef fc x) = fc
getFC (CLam fc x y) = fc
getFC (CLet fc x y z) = fc
getFC (CApp fc x xs) = fc
getFC (CCon fc x tag xs) = fc
getFC (COp fc x xs) = fc
getFC (CExtPrim fc p xs) = fc
getFC (CForce fc x) = fc
getFC (CDelay fc x) = fc
getFC (CConCase fc sc xs x) = fc
getFC (CConstCase fc sc xs x) = fc
getFC (CPrimVal fc x) = fc
getFC (CErased fc) = fc
getFC (CCrash fc x) = fc
