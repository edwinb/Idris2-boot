-- Representation of expressions ready for compiling
-- Type erased, explicit case trees
module Core.CompileExpr

import Core.FC
import Core.Name
import Core.TT

import Data.Vect

%default covering

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
       -- A forced (evaluated) value
       CForce : FC -> CExp vars -> CExp vars
       -- A delayed value
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

-- Argument type descriptors for foreign function calls
public export
data CFType : Type where
     CFUnit : CFType
     CFInt : CFType
     CFString : CFType
     CFDouble : CFType
     CFChar : CFType
     CFPtr : CFType
     CFWorld : CFType
     CFFun : CFType -> CFType -> CFType
     CFIORes : CFType -> CFType
     CFUser : Name -> List CFType -> CFType

public export
data CDef : Type where
     -- Normal function definition
     MkFun : (args : List Name) -> CExp args -> CDef
     -- Constructor
     MkCon : (tag : Int) -> (arity : Nat) -> CDef
     -- Foreign definition
     MkForeign : (ccs : List String) ->
                 (fargs : List CFType) ->
                 CFType ->
                 CDef
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
Show CFType where
  show CFUnit = "Unit"
  show CFInt = "Int"
  show CFString = "String"
  show CFDouble = "Double"
  show CFChar = "Char"
  show CFPtr = "Ptr"
  show CFWorld = "%World"
  show (CFFun s t) = show s ++ " -> " ++ show t
  show (CFIORes t) = "IORes " ++ show t
  show (CFUser n args) = show n ++ " " ++ showSep " " (map show args)

export
Show CDef where
  show (MkFun args exp) = show args ++ ": " ++ show exp
  show (MkCon tag arity) = "Constructor tag " ++ show tag ++ " arity " ++ show arity
  show (MkForeign ccs args ret)
      = "Foreign call " ++ show ccs ++ " " ++
        show args ++ " -> " ++ show ret
  show (MkError exp) = "Error: " ++ show exp

mutual
  export
  thin : (n : Name) -> CExp (outer ++ inner) -> CExp (outer ++ n :: inner)
  thin n (CLocal fc prf)
      = let MkVar var' = insertVar {n} _ prf in
            CLocal fc var'
  thin _ (CRef fc x) = CRef fc x
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
  thin _ (CPrimVal fc x) = CPrimVal fc x
  thin _ (CErased fc) = CErased fc
  thin _ (CCrash fc x) = CCrash fc x

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
  -- Shrink the scope of a compiled expression, replacing any variables not
  -- in the remaining set with Erased
  export
  shrinkCExp : SubVars newvars vars -> CExp vars -> CExp newvars
  shrinkCExp sub (CLocal fc prf)
      = case subElem prf sub of
             Nothing => CErased fc
             Just (MkVar prf') => CLocal fc prf'
  shrinkCExp _ (CRef fc x) = CRef fc x
  shrinkCExp sub (CLam fc x sc)
      = let sc' = shrinkCExp (KeepCons sub) sc in
            CLam fc x sc'
  shrinkCExp sub (CLet fc x val sc)
      = let sc' = shrinkCExp (KeepCons sub) sc in
            CLet fc x (shrinkCExp sub val) sc'
  shrinkCExp sub (CApp fc x xs)
      = CApp fc (shrinkCExp sub x) (assert_total (map (shrinkCExp sub) xs))
  shrinkCExp sub (CCon fc x tag xs)
      = CCon fc x tag (assert_total (map (shrinkCExp sub) xs))
  shrinkCExp sub (COp fc x xs)
      = COp fc x (assert_total (map (shrinkCExp sub) xs))
  shrinkCExp sub (CExtPrim fc p xs)
      = CExtPrim fc p (assert_total (map (shrinkCExp sub) xs))
  shrinkCExp sub (CForce fc x) = CForce fc (shrinkCExp sub x)
  shrinkCExp sub (CDelay fc x) = CDelay fc (shrinkCExp sub x)
  shrinkCExp sub (CConCase fc sc xs def)
      = CConCase fc (shrinkCExp sub sc)
                 (assert_total (map (shrinkConAlt sub) xs))
                 (assert_total (map (shrinkCExp sub) def))
  shrinkCExp sub (CConstCase fc sc xs def)
      = CConstCase fc (shrinkCExp sub sc)
                   (assert_total (map (shrinkConstAlt sub) xs))
                   (assert_total (map (shrinkCExp sub) def))
  shrinkCExp _ (CPrimVal fc x) = CPrimVal fc x
  shrinkCExp _ (CErased fc) = CErased fc
  shrinkCExp _ (CCrash fc x) = CCrash fc x

  shrinkConAlt : SubVars newvars vars -> CConAlt vars -> CConAlt newvars
  shrinkConAlt sub (MkConAlt x tag args sc)
        = MkConAlt x tag args (shrinkCExp (subExtend args sub) sc)

  shrinkConstAlt : SubVars newvars vars -> CConstAlt vars -> CConstAlt newvars
  shrinkConstAlt sub (MkConstAlt x sc) = MkConstAlt x (shrinkCExp sub sc)

mutual
  export
  Weaken CExp where
    weaken = thin {outer = []} _

export
getFC : CExp args -> FC
getFC (CLocal fc _) = fc
getFC (CRef fc _) = fc
getFC (CLam fc _ _) = fc
getFC (CLet fc _ _ _) = fc
getFC (CApp fc _ _) = fc
getFC (CCon fc _ _ _) = fc
getFC (COp fc _ _) = fc
getFC (CExtPrim fc _ _) = fc
getFC (CForce fc _) = fc
getFC (CDelay fc _) = fc
getFC (CConCase fc _ _ _) = fc
getFC (CConstCase fc _ _ _) = fc
getFC (CPrimVal fc _) = fc
getFC (CErased fc) = fc
getFC (CCrash fc _) = fc
