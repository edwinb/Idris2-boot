-- Representation of expressions ready for compiling
-- Type erased, explicit case trees
module Core.CompileExpr

import Core.Name
import Core.TT

import Data.Vect

%default total

mutual
  ||| CExp - an expression ready for compiling.
  public export
  data CExp : List Name -> Type where
       CLocal : {idx : Nat} -> .(IsVar x idx vars) -> CExp vars
       CRef : Name -> CExp vars
       -- Lambda expression
       CLam : (x : Name) -> CExp (x :: vars) -> CExp vars
       -- Let bindings
       CLet : (x : Name) -> CExp vars -> CExp (x :: vars) -> CExp vars
       -- Application of a defined function. The length of the argument list is
       -- exactly the same length as expected by its definition (so saturate with
       -- lambdas if necessary, or overapply with additional CApps)
       CApp : CExp vars -> List (CExp vars) -> CExp vars
       -- A saturated constructor application
       CCon : Name -> (tag : Int) -> List (CExp vars) -> CExp vars
       -- Internally defined primitive operations
       COp : PrimFn arity -> Vect arity (CExp vars) -> CExp vars
       -- Externally defined primitive operations
       CExtPrim : (p : Name) -> List (CExp vars) -> CExp vars
       -- A forced (evaluated) value (TODO: is this right?)
       CForce : CExp vars -> CExp vars
       -- A delayed value (lazy? TODO: check)
       CDelay : CExp vars -> CExp vars
       -- A case match statement
       CConCase : (sc : CExp vars) -> List (CConAlt vars) -> Maybe (CExp vars) -> CExp vars
       CConstCase : (sc : CExp vars) -> List (CConstAlt vars) -> Maybe (CExp vars) -> CExp vars
       -- A primitive value
       CPrimVal : Constant -> CExp vars
       -- An erased value
       CErased : CExp vars
       -- Some sort of crash?
       CCrash : String -> CExp vars

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
    show (CLocal {x} y) = "!" ++ show x
    show (CRef x) = show x
    show (CLam x y) = "(%lam " ++ show x ++ " " ++ show y ++ ")"
    show (CLet x y z) = "(%let " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (CApp x xs)
        = assert_total $ "(" ++ show x ++ " " ++ show xs ++ ")"
    show (CCon x tag xs)
        = assert_total $ "(%con " ++ show x ++ " " ++ show tag ++ " " ++ show xs ++ ")"
    show (COp op xs)
        = assert_total $ "(" ++ show op ++ " " ++ show xs ++ ")"
    show (CExtPrim p xs)
        = assert_total $ "(%extern " ++ show p ++ " " ++ show xs ++ ")"
    show (CForce x) = "(%force " ++ show x ++ ")"
    show (CDelay x) = "(%delay " ++ show x ++ ")"
    show (CConCase sc xs def)
        = assert_total $ "(%case " ++ show sc ++ " " ++ show xs ++ " " ++ show def ++ ")"
    show (CConstCase sc xs def)
        = assert_total $ "(%case " ++ show sc ++ " " ++ show xs ++ " " ++ show def ++ ")"
    show (CPrimVal x) = show x
    show CErased = "___"
    show (CCrash x) = "(CRASH " ++ show x ++ ")"

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
  thin n (CLocal prf) 
      = let MkVar var' = insertVar {n} _ prf in
            CLocal var'
  thin n (CRef x) = CRef x
  thin {outer} {inner} n (CLam x sc)
      = let sc' = thin {outer = x :: outer} {inner} n sc in
            CLam x sc'
  thin {outer} {inner} n (CLet x val sc)
      = let sc' = thin {outer = x :: outer} {inner} n sc in
            CLet x (thin n val) sc'
  thin n (CApp x xs)
      = CApp (thin n x) (assert_total (map (thin n) xs))
  thin n (CCon x tag xs)
      = CCon x tag (assert_total (map (thin n) xs))
  thin n (COp x xs)
      = COp x (assert_total (map (thin n) xs))
  thin n (CExtPrim p xs)
      = CExtPrim p (assert_total (map (thin n) xs))
  thin n (CForce x) = CForce (thin n x)
  thin n (CDelay x) = CDelay (thin n x)
  thin n (CConCase sc xs def)
      = CConCase (thin n sc) (assert_total (map (thinConAlt n) xs))
                 (assert_total (map (thin n) def))
  thin n (CConstCase sc xs def)
      = CConstCase (thin n sc) (assert_total (map (thinConstAlt n) xs))
                   (assert_total (map (thin n) def))
  thin n (CPrimVal x) = CPrimVal x
  thin n CErased = CErased
  thin n (CCrash x) = CCrash x

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
  embed (CLocal prf) = CLocal (varExtend prf)
  embed (CRef n) = CRef n
  embed (CLam x sc) = CLam x (embed sc)
  embed (CLet x val sc) = CLet x (embed val) (embed sc)
  embed (CApp f args) = CApp (embed f) (assert_total (map embed args))
  embed (CCon n t args) = CCon n t (assert_total (map embed args))
  embed (COp p args) = COp p (assert_total (map embed args))
  embed (CExtPrim p args) = CExtPrim p (assert_total (map embed args))
  embed (CForce e) = CForce (embed e)
  embed (CDelay e) = CDelay (embed e)
  embed (CConCase sc alts def)
      = CConCase (embed sc) (assert_total (map embedAlt alts))
                 (assert_total (map embed def))
  embed (CConstCase sc alts def)
      = CConstCase (embed sc) (assert_total (map embedConstAlt alts))
                   (assert_total (map embed def))
  embed (CPrimVal c) = CPrimVal c
  embed CErased = CErased
  embed (CCrash msg) = CCrash msg

  embedAlt : CConAlt args -> CConAlt (args ++ vars)
  embedAlt {args} {vars} (MkConAlt n t as sc)
     = MkConAlt n t as (rewrite appendAssociative as args vars in embed sc)

  embedConstAlt : CConstAlt args -> CConstAlt (args ++ vars)
  embedConstAlt (MkConstAlt c sc) = MkConstAlt c (embed sc)

mutual
  export
  Weaken CExp where
    weaken = thin {outer = []} _

