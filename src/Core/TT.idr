module Core.TT

import public Core.FC
import public Core.Name

import Data.Vect

%default covering

%hide Raw -- from Reflection in the Prelude
%hide Binder
%hide NameType
%hide Case

public export
data NameType : Type where
     Bound   : NameType
     Func    : NameType
     DataCon : (tag : Int) -> (arity : Nat) -> NameType
     TyCon   : (tag : Int) -> (arity : Nat) -> NameType

public export
data Constant 
	  = I Int
    | BI Integer
    | Str String
    | Ch Char
    | Db Double
    | WorldVal

    | IntType
		| IntegerType
    | StringType
    | CharType
    | DoubleType
    | WorldType

export
constantEq : (x, y : Constant) -> Maybe (x = y)
constantEq (I x) (I y) = case decEq x y of
                              Yes Refl => Just Refl
                              No contra => Nothing
constantEq (BI x) (BI y) = case decEq x y of
                                Yes Refl => Just Refl
                                No contra => Nothing
constantEq (Str x) (Str y) = case decEq x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (Ch x) (Ch y) = case decEq x y of
                                Yes Refl => Just Refl
                                No contra => Nothing
constantEq (Db x) (Db y) = Nothing -- no DecEq for Doubles!
constantEq WorldVal WorldVal = Just Refl
constantEq IntType IntType = Just Refl
constantEq IntegerType IntegerType = Just Refl
constantEq StringType StringType = Just Refl
constantEq CharType CharType = Just Refl
constantEq DoubleType DoubleType = Just Refl
constantEq WorldType WorldType = Just Refl
constantEq _ _ = Nothing

export
Show Constant where
  show (I x) = show x
  show (BI x) = show x
  show (Str x) = show x
  show (Ch x) = show x
  show (Db x) = show x
  show WorldVal = "%MkWorld"
  show IntType = "Int"
  show IntegerType = "Integer"
  show StringType = "String"
  show CharType = "Char"
  show DoubleType = "Double"
  show WorldType = "%World"

export
Eq Constant where
  (I x) == (I y) = x == y
  (BI x) == (BI y) = x == y
  (Str x) == (Str y) = x == y
  (Ch x) == (Ch y) = x == y
  (Db x) == (Db y) = x == y
  WorldVal == WorldVal = True
  IntType == IntType = True
  IntegerType == IntegerType = True
  StringType == StringType = True
  CharType == CharType = True
  DoubleType == DoubleType = True
  WorldType == WorldType = True
  _ == _ = False

public export
data PiInfo = Implicit | Explicit | AutoImplicit

export
Show PiInfo where
  show Implicit = "Implicit"
  show Explicit = "Explicit"
  show AutoImplicit = "AutoImplicit"

public export
data RigCount = Rig0 | Rig1 | RigW

export
isLinear : RigCount -> Bool
isLinear Rig1 = True
isLinear _ = False

export
Eq RigCount where
  (==) Rig0 Rig0 = True
  (==) Rig1 Rig1 = True
  (==) RigW RigW = True
  (==) _ _ = False

export
Ord RigCount where
  compare Rig0 Rig0 = EQ
  compare Rig0 Rig1 = LT
  compare Rig0 RigW = LT

  compare Rig1 Rig0 = GT
  compare Rig1 Rig1 = EQ
  compare Rig1 RigW = LT

  compare RigW Rig0 = GT
  compare RigW Rig1 = GT
  compare RigW RigW = EQ

export
Show RigCount where
  show Rig0 = "Rig0"
  show Rig1 = "Rig1"
  show RigW = "RigW"

export
rigPlus : RigCount -> RigCount -> RigCount
rigPlus Rig0 Rig0 = Rig0
rigPlus Rig0 Rig1 = Rig1
rigPlus Rig0 RigW = RigW
rigPlus Rig1 Rig0 = Rig1
rigPlus Rig1 Rig1 = RigW
rigPlus Rig1 RigW = RigW
rigPlus RigW Rig0 = RigW
rigPlus RigW Rig1 = RigW
rigPlus RigW RigW = RigW

export
rigMult : RigCount -> RigCount -> RigCount
rigMult Rig0 Rig0 = Rig0
rigMult Rig0 Rig1 = Rig0
rigMult Rig0 RigW = Rig0
rigMult Rig1 Rig0 = Rig0
rigMult Rig1 Rig1 = Rig1
rigMult Rig1 RigW = RigW
rigMult RigW Rig0 = Rig0
rigMult RigW Rig1 = RigW
rigMult RigW RigW = RigW

public export
data Binder : Type -> Type where
	   -- Lambda bound variables with their implicitness
     Lam : RigCount -> PiInfo -> (ty : type) -> Binder type
		 -- Let bound variables with their value
     Let : RigCount -> (val : type) -> (ty : type) -> Binder type
		 -- Forall/pi bound variables with their implicitness
     Pi : RigCount -> PiInfo -> (ty : type) -> Binder type
		 -- pattern bound variables
     PVar : RigCount -> (ty : type) -> Binder type 
		 -- the type of pattern bound variables
     PVTy : RigCount -> (ty : type) -> Binder type

export
binderType : Binder tm -> tm
binderType (Lam _ x ty) = ty
binderType (Let _ val ty) = ty
binderType (Pi _ x ty) = ty
binderType (PVar _ ty) = ty
binderType (PVTy _ ty) = ty

export
multiplicity : Binder tm -> RigCount
multiplicity (Lam c x ty) = c
multiplicity (Let c val ty) = c
multiplicity (Pi c x ty) = c
multiplicity (PVar c ty) = c
multiplicity (PVTy c ty) = c
  
export
setMultiplicity : Binder tm -> RigCount -> Binder tm
setMultiplicity (Lam c x ty) c' = Lam c' x ty
setMultiplicity (Let c val ty) c' = Let c' val ty
setMultiplicity (Pi c x ty) c' = Pi c' x ty
setMultiplicity (PVar c ty) c' = PVar c' ty
setMultiplicity (PVTy c ty) c' = PVTy c' ty

showCount : RigCount -> String
showCount Rig0 = "0 "
showCount Rig1 = "1 "
showCount RigW = ""
  
Show ty => Show (Binder ty) where
	show (Lam c _ t) = "\\" ++ showCount c ++ show t
	show (Pi c _ t) = "Pi " ++ showCount c ++ show t
	show (Let c v t) = "let " ++ showCount c ++ show v ++ " : " ++ show t
	show (PVar c t) = "pat " ++ showCount c ++ show t
	show (PVTy c t) = "pty " ++ showCount c ++ show t

export
setType : Binder tm -> tm -> Binder tm
setType (Lam c x _) ty = Lam c x ty
setType (Let c val _) ty = Let c val ty
setType (Pi c x _) ty = Pi c x ty
setType (PVar c _) ty = PVar c ty
setType (PVTy c _) ty = PVTy c ty

export
Functor Binder where
  map func (Lam c x ty) = Lam c x (func ty)
  map func (Let c val ty) = Let c (func val) (func ty)
  map func (Pi c x ty) = Pi c x (func ty)
  map func (PVar c ty) = PVar c (func ty)
  map func (PVTy c ty) = PVTy c (func ty)

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

public export
data Var : List Name -> Type where
     MkVar : {i : Nat} -> IsVar n i vars -> Var vars

export
sameVar : {i, j : _} -> IsVar n i xs -> IsVar m j xs -> Bool
sameVar {i} {j} _ _ = i == j

public export
record AppInfo where
  constructor MkAppInfo
  plicit : PiInfo

export
appInf : PiInfo -> AppInfo
appInf p = MkAppInfo p

export
implApp : AppInfo
implApp = appInf Implicit

export
explApp : AppInfo
explApp = appInf Explicit

namespace CList
  -- A list correspoding to another list
  public export
  data CList : List a -> Type -> Type where
       Nil : CList [] ty
       (::) : (x : ty) -> CList cs ty -> CList (c :: cs) ty

-- Typechecked terms
-- These are guaranteed to be well-scoped wrt local variables, because they are
-- indexed by the names of local variables in scope
mutual
  public export
  data Term : List Name -> Type where
       Local : FC -> Maybe RigCount -> 
               (idx : Nat) -> IsVar name idx vars -> Term vars
       Ref : FC -> NameType -> (name : Name) -> Term vars
       -- Metavariable solution binding
       ULet : Int -> Term vars -> Term vars -> Term vars
       Bind : FC -> (x : Name) -> 
              (b : Binder (Term vars)) -> 
              (scope : Term (x :: vars)) -> Term vars
       App : FC -> (fn : Term vars) -> (p : AppInfo) -> (arg : Term vars) -> Term vars
       Case : FC -> (cs : List (Var vars)) -> 
              (ty : Term vars) ->
              Maybe (CaseTree vars) ->
              (alts : List (PatAlt vars)) -> 
              Term vars
       PrimVal : FC -> (c : Constant) -> Term vars
       Erased : FC -> Term vars
       TType : FC -> Term vars

  public export
  data Pat : List Name -> Type where
       PAs : FC -> (idx : Nat) -> IsVar name idx vars -> Pat vars -> Pat vars
       PCon : FC -> Name -> (tag : Int) -> (arity : Nat) ->
              List (Pat vars) -> Pat vars
       PLoc : FC -> (idx : Nat) -> IsVar name idx vars -> Pat vars
       PUnmatchable : FC -> Term vars -> Pat vars

  public export
  data PatAlt : List Name -> Type where
       CBind : RigCount -> (x : Name) -> (ty : Term vars) ->
               PatAlt (x :: vars) -> PatAlt vars
       CPats : List (Pat vars) -> Term vars -> PatAlt vars

  public export
  data CaseTree : List Name -> Type where
       Switch : (idx : Nat) -> IsVar name idx vars ->
                (scTy : Term vars) -> List (CaseAlt vars) ->
                CaseTree vars
       STerm : Term vars -> CaseTree vars
       Unmatched : (msg : String) -> CaseTree vars
       Impossible : CaseTree vars

  public export
  data CaseAlt : List Name -> Type where
       ConCase : Name -> (tag : Int) -> (args : List Name) ->
                 CaseTree (args ++ vars) -> CaseAlt vars
       ConstCase : Constant -> CaseTree vars -> CaseAlt vars
       DefaultCase : CaseTree vars -> CaseAlt vars

export Show (Term vars) where
  show tm = "[not done yet]"

public export
ClosedTerm : Type
ClosedTerm = Term []

export
apply : FC -> AppInfo -> Term vars -> List (Term vars) -> Term vars
apply loc p fn [] = fn
apply loc p fn (a :: args) = apply loc p (App loc fn p a) args

public export
data Visibility = Private | Export | Public

export
Show Visibility where
  show Private = "private"
  show Export = "export"
  show Public = "public export"

export
Eq Visibility where
  Private == Private = True
  Export == Export = True
  Public == Public = True
  _ == _ = False

export
Ord Visibility where
  compare Private Export = LT
  compare Private Public = LT
  compare Export Public = LT

  compare Private Private = EQ
  compare Export Export = EQ
  compare Public Public = EQ

  compare Export Private = GT
  compare Public Private = GT
  compare Public Export = GT

public export
interface Weaken (tm : List Name -> Type) where
  weaken : tm vars -> tm (n :: vars)
  weakenNs : (ns : List Name) -> tm vars -> tm (ns ++ vars)

  weakenNs [] t = t
  weakenNs (n :: ns) t = weaken (weakenNs ns t)

  weaken = weakenNs [_]

insertVar : {outer : _} ->
            (idx : _) -> 
            IsVar name idx (outer ++ inner) ->
            (idx' ** IsVar name idx' (outer ++ n :: inner))
insertVar {outer = []} idx x = (_ ** Later x)
insertVar {outer = (name :: xs)} Z First = (_ ** First)
insertVar {n} {outer = (x :: xs)} (S i) (Later y) 
    = let (_ ** prf) = insertVar {n} i y in
          (_ ** Later prf)

weakenVar : (ns : List Name) -> IsVar name idx inner ->
            (idx' ** IsVar name idx' (ns ++ inner))
weakenVar [] x = (_ ** x)
weakenVar (y :: xs) x 
   = let (_ ** x') = weakenVar xs x in
         (_ ** Later x')

insertVarNames : {outer, ns : _} ->
                 (idx : _) -> 
                 IsVar name idx (outer ++ inner) ->
                 (idx' ** IsVar name idx' (outer ++ (ns ++ inner)))
insertVarNames {ns} {outer = []} idx prf = weakenVar ns prf
insertVarNames {outer = (y :: xs)} Z First = (_ ** First)
insertVarNames {ns} {outer = (y :: xs)} (S i) (Later x) 
    = let (_ ** prf) = insertVarNames {ns} i x in
          (_ ** Later prf)

mutual
  export
  thin : {outer, inner : _} ->
         (n : Name) -> Term (outer ++ inner) -> Term (outer ++ n :: inner)
  thin n (Local fc r idx prf) 
      = let (idx' ** var') = insertVar {n} idx prf in
            Local fc r idx' var'
  thin n (Ref fc nt name) = Ref fc nt name
  thin n (ULet i val sc) 
      = ULet i (thin n val) (thin n sc)
  thin {outer} {inner} n (Bind fc x b scope) 
      = let sc' = thin {outer = x :: outer} {inner} n scope in
            Bind fc x (assert_total (map (thin n) b)) sc'
  thin n (App fc fn p arg) = App fc (thin n fn) p (thin n arg)
  thin {outer} {inner} n (Case fc cs ty tree alts) 
      = Case fc (map (thinVar {outer} {inner} n) cs)
                     (thin {outer} {inner} n ty) 
                     (map (thinTree n) tree)
                     (map (thinPatAlt n) alts)
  thin n (PrimVal fc c) = PrimVal fc c
  thin n (Erased fc) = Erased fc
  thin n (TType fc) = TType fc
  
  export
  insertNames : {outer, inner : _} ->
                (ns : List Name) -> Term (outer ++ inner) ->
                Term (outer ++ (ns ++ inner))
  insertNames ns (Local fc r idx prf) 
      = let (_ ** prf') = insertVarNames {ns} idx prf in
            Local fc r _ prf'
  insertNames ns (Ref fc nt name) = Ref fc nt name
  insertNames ns (ULet i val sc) 
      = ULet i (insertNames ns val) (insertNames ns sc)
  insertNames {outer} {inner} ns (Bind fc x b scope) 
      = Bind fc x (assert_total (map (insertNames ns) b)) 
             (insertNames {outer = x :: outer} {inner} ns scope)
  insertNames ns (App fc fn p arg) 
      = App fc (insertNames ns fn) p (insertNames ns arg)
  insertNames {outer} {inner} ns (Case fc cs ty tree alts) 
      = Case fc (map (insertNamesVar {outer} {inner} ns) cs)
                (insertNames ns ty)
                (map (insertCaseNames ns) tree)
                (map (insertPatAltNames ns) alts)
  insertNames ns (PrimVal fc c) = PrimVal fc c
  insertNames ns (Erased fc) = Erased fc
  insertNames ns (TType fc) = TType fc

  insertCaseNames : (ns : List Name) -> CaseTree (outer ++ inner) ->
                    CaseTree (outer ++ (ns ++ inner))
  insertCaseNames {inner} {outer} ns (Switch idx prf scTy alts) 
      = let (_ ** prf') = insertVarNames {outer} {inner} {ns} _ prf in
            Switch _ prf' (insertNames {outer} ns scTy)
                (map (insertCaseAltNames {outer} {inner} ns) alts)
  insertCaseNames {outer} ns (STerm x) = STerm (insertNames {outer} ns x)
  insertCaseNames ns (Unmatched msg) = Unmatched msg
  insertCaseNames ns Impossible = Impossible
  
  insertCaseAltNames : (ns : List Name) -> 
                       CaseAlt (outer ++ inner) -> 
                       CaseAlt (outer ++ (ns ++ inner))
  insertCaseAltNames {outer} {inner} ns (ConCase x tag args ct) 
      = ConCase x tag args 
           (rewrite appendAssociative args outer (ns ++ inner) in
                    insertCaseNames {outer = args ++ outer} {inner} ns
                        (rewrite sym (appendAssociative args outer inner) in
                                 ct))
  insertCaseAltNames ns (ConstCase x ct) 
      = ConstCase x (insertCaseNames ns ct)
  insertCaseAltNames ns (DefaultCase ct) 
      = DefaultCase (insertCaseNames ns ct)

  thinVar : (n : Name) -> Var (outer ++ inner) -> Var (outer ++ n :: inner)
  thinVar n (MkVar prf) 
      = let (_ ** prf') = insertVar {n} _ prf in
            MkVar prf'

  insertNamesVar : (ns : List Name) -> Var (outer ++ inner) -> Var (outer ++ (ns ++ inner))
  insertNamesVar ns (MkVar prf) 
      = let (_ ** prf') = insertVarNames {ns} _ prf in
            MkVar prf'

  thinTree : (n : Name) -> CaseTree (outer ++ inner) -> CaseTree (outer ++ n :: inner)
  thinTree n (Switch idx prf scTy alts) 
      = let (_ ** prf') = insertVar {n} _ prf in
            Switch _ prf' (thin n scTy) (map (insertCaseAltNames [n]) alts)
  thinTree n (STerm tm) = STerm (thin n tm)
  thinTree n (Unmatched msg) = Unmatched msg
  thinTree n Impossible = Impossible

  thinPat : (n : Name) -> Pat (outer ++ inner) -> Pat (outer ++ n :: inner)
  thinPat n (PAs fc idx prf p) 
      = let (_ ** prf') = insertVar {n} _ prf in
            PAs fc _ prf' (thinPat n p)
  thinPat n (PCon fc x tag arity args) 
      = PCon fc x tag arity (map (thinPat n) args)
  thinPat n (PLoc fc idx prf) 
      = let (_ ** prf') = insertVar {n} _ prf in
            PLoc fc _ prf'
  thinPat n (PUnmatchable fc tm) = PUnmatchable fc (thin n tm)
  
  insertPatNames : (ns : List Name) -> 
                   Pat (outer ++ inner) -> Pat (outer ++ (ns ++ inner))
  insertPatNames ns (PAs fc idx prf p) 
      = let (_ ** prf') = insertVarNames {ns} _ prf in
            PAs fc _ prf' (insertPatNames ns p)
  insertPatNames ns (PCon fc x tag arity args) 
      = PCon fc x tag arity (map (insertPatNames ns) args)
  insertPatNames ns (PLoc fc idx prf) 
      = let (_ ** prf') = insertVarNames {ns} _ prf in
            PLoc fc _ prf'
  insertPatNames ns (PUnmatchable fc tm) 
      = PUnmatchable fc (insertNames ns tm)

  thinPatAlt : (n : Name) -> PatAlt (outer ++ inner) -> PatAlt (outer ++ n :: inner)
  thinPatAlt {outer} n (CBind r x ty alt) 
      = CBind r x (thin n ty) (thinPatAlt {outer = x :: outer} n alt)
  thinPatAlt n (CPats pats tm) 
      = CPats (map (thinPat n) pats) (thin n tm)

  insertPatAltNames : (ns : List Name) -> 
                      PatAlt (outer ++ inner) -> PatAlt (outer ++ (ns ++ inner))
  insertPatAltNames {outer} ns (CBind r x ty alt) 
      = CBind r x (insertNames ns ty) (insertPatAltNames {outer = x :: outer} ns alt)
  insertPatAltNames ns (CPats pats tm) 
      = CPats (map (insertPatNames ns) pats) (insertNames ns tm)

export 
Weaken Term where
  weaken tm = thin {outer = []} _ tm
  weakenNs ns tm = insertNames {outer = []} ns tm

--- Some test stuff
loc : (n : Name) -> {auto prf : IsVar n idx vars} -> Term vars
loc n {prf} = Local emptyFC Nothing _ prf

cvar : (n : Name) -> {auto prf : IsVar n idx vars} -> Var vars
cvar n {prf} = MkVar prf

ploc : (n : Name) -> {auto prf : IsVar n idx vars} -> Pat vars
ploc n {prf} = PLoc emptyFC _ prf

lam : (n : Name) -> Term vars -> Term (n :: vars) -> Term vars
lam n ty sc = Bind emptyFC n (Lam RigW Explicit ty) sc

NatTy : Term vs
NatTy = Ref emptyFC (TyCon 0 2) (UN "Nat")

testPlus : Term []
testPlus 
    = lam (UN "x") NatTy $
        lam (UN "y") NatTy $
          Case emptyFC [cvar (UN "x")] NatTy Nothing
            [CPats [PCon emptyFC (UN "Z") 0 0 []] (loc (UN "y")),
             CBind RigW (UN "k") NatTy
                (CPats [PCon emptyFC (UN "S") 1 1 [ploc (UN "k")]] 
                   (apply emptyFC explApp (Ref emptyFC (DataCon 1 1) (UN "S")) 
                       [apply emptyFC explApp (Ref emptyFC Func (UN "plus"))
                               [loc (UN "k"), loc (UN "y")]]))]




