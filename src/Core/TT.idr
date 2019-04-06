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

export
Eq PiInfo where
  (==) Implicit Implicit = True
  (==) Explicit Explicit = True
  (==) AutoImplicit AutoImplicit = True
  (==) _ _ = False

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
  argname : Maybe Name
  plicit : PiInfo

export
appInf : Maybe Name -> PiInfo -> AppInfo
appInf n p = MkAppInfo n p

export
implApp : Maybe Name -> AppInfo
implApp n = appInf n Implicit

export
explApp : Maybe Name -> AppInfo
explApp n = appInf n Explicit

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
  data LazyReason = LInf | LLazy 

  public export
  data Term : List Name -> Type where
       Local : {name : _} ->
               FC -> Maybe RigCount -> 
               (idx : Nat) -> IsVar name idx vars -> Term vars
       Ref : FC -> NameType -> (name : Name) -> Term vars
       Meta : FC -> Name -> Int -> List (Term vars) -> Term vars
       Bind : FC -> (x : Name) -> 
              (b : Binder (Term vars)) -> 
              (scope : Term (x :: vars)) -> Term vars
       App : FC -> (fn : Term vars) -> (p : AppInfo) -> (arg : Term vars) -> Term vars
       Case : FC -> (cs : List (Var vars)) -> 
              (ty : Term vars) ->
              Maybe (CaseTree vars) ->
              (alts : List (PatAlt vars)) -> 
              Term vars
       TDelayed : FC -> LazyReason -> Term vars -> Term vars
       TDelay : FC -> LazyReason -> Term vars -> Term vars
       TForce : FC -> Term vars -> Term vars
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

export
Eq LazyReason where
  (==) LInf LInf = True
  (==) LLazy LLazy = True
  (==) _ _ = False

export
varExtend : IsVar x idx xs -> IsVar x idx (xs ++ ys)
-- What Could Possibly Go Wrong?
-- This relies on the runtime representation of the term being the same
-- after embedding! It is just an identity function at run time, though, and
-- we don't need its definition at compile time, so let's do it...
varExtend p = believe_me p

export
embed : Term vars -> Term (vars ++ more)
embed tm = believe_me tm

public export
ClosedTerm : Type
ClosedTerm = Term []

export
apply : FC -> AppInfo -> Term vars -> List (Term vars) -> Term vars
apply loc p fn [] = fn
apply loc p fn (a :: args) = apply loc p (App loc fn p a) args

export
applyInfo : FC -> Term vars -> List (AppInfo, Term vars) -> Term vars
applyInfo loc fn [] = fn
applyInfo loc fn ((p, a) :: args) = applyInfo loc (App loc fn p a) args

export
getFnArgs : Term vars -> (Term vars, List (AppInfo, Term vars))
getFnArgs tm = getFA [] tm
  where
    getFA : List (AppInfo, Term vars) -> Term vars -> 
            (Term vars, List (AppInfo, Term vars))
    getFA args (App _ f i a) = getFA ((i, a) :: args) f
    getFA args tm = (tm, args)

export
getFn : Term vars -> Term vars
getFn (App _ f _ a) = getFn f
getFn tm = tm

export
getArgs : Term vars -> (List (AppInfo, Term vars))
getArgs = snd . getFnArgs

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

export
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
  thin n (Meta fc name idx args) = Meta fc name idx (map (thin n) args)
  thin {outer} {inner} n (Bind fc x b scope) 
      = let sc' = thin {outer = x :: outer} {inner} n scope in
            Bind fc x (assert_total (map (thin n) b)) sc'
  thin n (App fc fn p arg) = App fc (thin n fn) p (thin n arg)
  thin {outer} {inner} n (Case fc cs ty tree alts) 
      = Case fc (map (thinVar {outer} {inner} n) cs)
                     (thin {outer} {inner} n ty) 
                     (map (thinTree n) tree)
                     (map (thinPatAlt n) alts)
  thin n (TDelayed fc r ty) = TDelayed fc r (thin n ty)
  thin n (TDelay fc r tm) = TDelay fc r (thin n tm)
  thin n (TForce fc tm) = TForce fc (thin n tm)
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
  insertNames ns (Meta fc name idx args)
      = Meta fc name idx (map (insertNames ns) args)
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
  insertNames ns (TDelayed fc r ty) = TDelayed fc r (insertNames ns ty)
  insertNames ns (TDelay fc r tm) = TDelay fc r (insertNames ns tm)
  insertNames ns (TForce fc tm) = TForce fc (insertNames ns tm)
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

public export
data CompatibleVars : List Name -> List Name -> Type where
     CompatPre : CompatibleVars xs xs
     CompatExt : CompatibleVars xs ys -> CompatibleVars (n :: xs) (m :: ys)

export
areVarsCompatible : (xs : List Name) -> (ys : List Name) -> 
                    Maybe (CompatibleVars xs ys)
areVarsCompatible [] [] = pure CompatPre
areVarsCompatible (x :: xs) (y :: ys)
    = do compat <- areVarsCompatible xs ys
         pure (CompatExt compat)
areVarsCompatible _ _ = Nothing

extendCompats : (args : List Name) ->
                CompatibleVars xs ys ->
                CompatibleVars (args ++ xs) (args ++ ys)
extendCompats [] prf = prf
extendCompats (x :: xs) prf = CompatExt (extendCompats xs prf)

renameLocalRef : CompatibleVars xs ys -> IsVar name idx xs -> (name' ** IsVar name' idx ys)
renameLocalRef CompatPre First = (_ ** First)
renameLocalRef (CompatExt x) First = (_ ** First)
renameLocalRef CompatPre (Later p) = (_ ** Later p)
renameLocalRef (CompatExt y) (Later p) 
    = let (_ ** p') = renameLocalRef y p in (_ ** Later p')

renameVarList : CompatibleVars xs ys -> Var xs -> Var ys
renameVarList prf (MkVar p) = MkVar (snd (renameLocalRef prf p))

mutual
  -- TODO: Surely identity at run time, can we replace with 'believe_me'?
  export
  renameVars : CompatibleVars xs ys -> Term xs -> Term ys 
  renameVars CompatPre tm = tm
  renameVars prf (Local fc r idx vprf) 
      = Local fc r idx (snd (renameLocalRef prf vprf))
  renameVars prf (Ref fc x name) = Ref fc x name
  renameVars prf (Meta fc n i args) 
      = Meta fc n i (map (renameVars prf) args)
  renameVars prf (Bind fc x b scope) 
      = Bind fc x (map (renameVars prf) b) (renameVars (CompatExt prf) scope)
  renameVars prf (App fc fn p arg) 
      = App fc (renameVars prf fn) p (renameVars prf arg)
  renameVars prf (Case fc cs ty tree alts) 
      = Case fc (map (renameVarList prf) cs) (renameVars prf ty) 
                (map (renameTree prf) tree) 
                (map (renamePatAlt prf) alts)
  renameVars prf (TDelayed fc r ty) = TDelayed fc r (renameVars prf ty)
  renameVars prf (TDelay fc r tm) = TDelay fc r (renameVars prf tm)
  renameVars prf (TForce fc x) = TForce fc (renameVars prf x)
  renameVars prf (PrimVal fc c) = PrimVal fc c
  renameVars prf (Erased fc) = Erased fc
  renameVars prf (TType fc) = TType fc

  renameCaseAlt : CompatibleVars xs ys -> CaseAlt xs -> CaseAlt ys
  renameCaseAlt prf (ConCase x tag args tree) 
      = ConCase x tag args (renameTree (extendCompats args prf) tree)
  renameCaseAlt prf (ConstCase c tree) 
      = ConstCase c (renameTree prf tree)
  renameCaseAlt prf (DefaultCase tree) 
      = DefaultCase (renameTree prf tree)

  renameTree : CompatibleVars xs ys -> CaseTree xs -> CaseTree ys
  renameTree prf (Switch idx x scTy xs) 
     = Switch idx (snd (renameLocalRef prf x)) (renameVars prf scTy)
                  (map (renameCaseAlt prf) xs)
  renameTree prf (STerm tm) = STerm (renameVars prf tm)
  renameTree prf (Unmatched msg) = Unmatched msg
  renameTree prf Impossible = Impossible

  renamePat : CompatibleVars xs ys -> Pat xs -> Pat ys
  renamePat prf (PAs fc idx p pat) 
      = PAs fc idx (snd (renameLocalRef prf p)) (renamePat prf pat)
  renamePat prf (PCon fc x tag arity xs) 
      = PCon fc x tag arity (map (renamePat prf) xs)
  renamePat prf (PLoc fc idx p) 
      = PLoc fc idx (snd (renameLocalRef prf p))
  renamePat prf (PUnmatchable fc tm) 
      = PUnmatchable fc (renameVars prf tm)

  renamePatAlt : CompatibleVars xs ys -> PatAlt xs -> PatAlt ys
  renamePatAlt prf (CBind r x ty alt) 
      = CBind r x (renameVars prf ty) (renamePatAlt (CompatExt prf) alt)
  renamePatAlt prf (CPats xs tm)
      = CPats (map (renamePat prf) xs) (renameVars prf tm)


export
renameTop : (m : Name) -> Term (n :: vars) -> Term (m :: vars)
renameTop m tm = renameVars (CompatExt CompatPre) tm

public export
data SubVars : List Name -> List Name -> Type where
     SubRefl  : SubVars xs xs
     DropCons : SubVars xs ys -> SubVars xs (y :: ys)
     KeepCons : SubVars xs ys -> SubVars (x :: xs) (x :: ys)

export
subElem : IsVar name x xs -> SubVars ys xs -> Maybe (x' ** IsVar name x' ys)
subElem prf SubRefl = Just (_ ** prf)
subElem First (DropCons p) = Nothing
subElem (Later x) (DropCons p) 
    = do (_ ** prf') <- subElem x p
         Just (_ ** prf')
subElem First (KeepCons p) = Just (_ ** First)
subElem (Later x) (KeepCons p) 
    = do (_ ** prf') <- subElem x p
         Just (_ ** Later prf')

mutual
  shrinkBinder : Binder (Term vars) -> SubVars newvars vars -> 
                 Maybe (Binder (Term newvars))
  shrinkBinder (Lam c p ty) prf 
      = Just (Lam c p !(shrinkTerm ty prf))
  shrinkBinder (Let c val ty) prf
      = Just (Let c !(shrinkTerm val prf) !(shrinkTerm ty prf))
  shrinkBinder (Pi c p ty) prf
      = Just (Pi c p !(shrinkTerm ty prf))
  shrinkBinder (PVar c ty) prf
      = Just (PVar c !(shrinkTerm ty prf))
  shrinkBinder (PVTy c ty) prf
      = Just (PVTy c !(shrinkTerm ty prf))

  export
  shrinkVar : Var vars -> SubVars newvars vars -> Maybe (Var newvars)
  shrinkVar (MkVar x) prf 
      = case subElem x prf of
             Nothing => Nothing
             Just (_ ** x') => Just (MkVar x')

  export
  shrinkTree : CaseTree vars -> SubVars newvars vars -> Maybe (CaseTree newvars)
  shrinkTree (Switch idx x scTy xs) prf 
     = case subElem x prf of
            Nothing => Nothing
            Just (_ ** x') => 
                Just (Switch _ x' !(shrinkTerm scTy prf) 
                           !(traverse (\x => shrinkCaseAlt x prf) xs))
  shrinkTree (STerm x) prf = Just (STerm !(shrinkTerm x prf))
  shrinkTree (Unmatched msg) prf = Just (Unmatched msg)
  shrinkTree Impossible prf = Just Impossible

  export
  shrinkCaseAlt : CaseAlt vars -> SubVars newvars vars -> Maybe (CaseAlt newvars)
  shrinkCaseAlt (ConCase x tag args tree) prf 
      = Just (ConCase x tag args !(shrinkTree tree (keepArgs args prf)))
    where
      keepArgs : (args : List Name) ->
                 SubVars newvars vars -> SubVars (args ++ newvars) (args ++ vars)
      keepArgs [] prf = prf
      keepArgs (x :: xs) prf = KeepCons (keepArgs xs prf)
  shrinkCaseAlt (ConstCase x tree) prf 
      = Just (ConstCase x !(shrinkTree tree prf))
  shrinkCaseAlt (DefaultCase tree) prf 
      = Just (DefaultCase !(shrinkTree tree prf))

  export
  shrinkPatAlt : PatAlt vars -> SubVars newvars vars -> Maybe (PatAlt newvars)
  shrinkPatAlt (CBind r x ty alt) prf 
      = Just (CBind r x !(shrinkTerm ty prf) !(shrinkPatAlt alt (KeepCons prf)))
  shrinkPatAlt (CPats xs tm) prf 
      = Just (CPats !(traverse (\x => shrinkPat x prf) xs)
                    !(shrinkTerm tm prf))

  shrinkPat : Pat vars -> SubVars newvars vars -> Maybe (Pat newvars)
  shrinkPat (PAs fc idx x pat) prf 
      = case subElem x prf of
             Nothing => Nothing
             Just (_ ** x') =>
                 Just (PAs fc _ x' !(shrinkPat pat prf))
  shrinkPat (PCon fc x tag arity xs) prf 
      = Just (PCon fc x tag arity !(traverse (\x => shrinkPat x prf) xs))
  shrinkPat (PLoc fc idx x) prf
      = case subElem x prf of
             Nothing => Nothing
             Just (_ ** x') =>
                 Just (PLoc fc _ x')
  shrinkPat (PUnmatchable fc x) prf 
      = Just (PUnmatchable fc !(shrinkTerm x prf))

  export
  shrinkTerm : Term vars -> SubVars newvars vars -> Maybe (Term newvars)
  shrinkTerm (Local fc r idx loc) prf 
     = case subElem loc prf of
            Nothing => Nothing
            Just (_ ** loc') => Just (Local fc r _ loc')
  shrinkTerm (Ref fc x name) prf = Just (Ref fc x name)
  shrinkTerm (Meta fc x y xs) prf 
     = do xs' <- traverse (\x => shrinkTerm x prf) xs
          Just (Meta fc x y xs')
  shrinkTerm (Bind fc x b scope) prf 
     = Just (Bind fc x !(shrinkBinder b prf) !(shrinkTerm scope (KeepCons prf)))
  shrinkTerm (App fc fn p arg) prf 
     = Just (App fc !(shrinkTerm fn prf) p !(shrinkTerm arg prf))
  shrinkTerm (Case fc cs ty tree alts) prf 
     = Just (Case fc !(traverse (\x => shrinkVar x prf) cs)
                     !(shrinkTerm ty prf)
                     !(traverse (\x => shrinkTree x prf) tree)
                     !(traverse (\x => shrinkPatAlt x prf) alts))
  shrinkTerm (TDelayed fc x y) prf 
     = Just (TDelayed fc x !(shrinkTerm y prf))
  shrinkTerm (TDelay fc x y) prf
     = Just (TDelay fc x !(shrinkTerm y prf))
  shrinkTerm (TForce fc x) prf
     = Just (TForce fc !(shrinkTerm x prf))
  shrinkTerm (PrimVal fc c) prf = Just (PrimVal fc c)
  shrinkTerm (Erased fc) prf = Just (Erased fc)
  shrinkTerm (TType fc) prf = Just (TType fc)

public export
data Bounds : List Name -> Type where
     None : Bounds []
     Add : (x : Name) -> Name -> Bounds xs -> Bounds (x :: xs)

-- export
-- refsToLocals : Bounds bound -> Term vars -> Term (bound ++ vars)

export Show (Term vars) where
  show tm = let (fn, args) = getFnArgs tm in showApp fn args
    where
      showApp : Term vars -> List (AppInfo, Term vars) -> String
      showApp (Local {name} _ _ idx _) [] = show name ++ "[" ++ show idx ++ "]"
      showApp (Ref _ _ n) [] = show n
      showApp (Meta _ n _ args) [] = "?" ++ show n ++ "_" ++ show (length args)
      showApp (Bind _ x (Lam c p ty) sc) [] 
          = "\\" ++ showCount c ++ show x ++ " : " ++ show ty ++ 
            " => " ++ show sc
      showApp (Bind _ x (Let c val ty) sc) [] 
          = "let " ++ showCount c ++ show x ++ " : " ++ show ty ++ 
            " = " ++ show val ++ " in " ++ show sc
      showApp (Bind _ x (Pi c Explicit ty) sc) [] 
          = "(" ++ showCount c ++ show x ++ " : " ++ show ty ++ 
            ") -> " ++ show sc
      showApp (Bind _ x (Pi c Implicit ty) sc) [] 
          = "{" ++ showCount c ++ show x ++ " : " ++ show ty ++ 
            "} -> " ++ show sc
      showApp (Bind _ x (Pi c AutoImplicit ty) sc) [] 
          = "{auto" ++ showCount c ++ show x ++ " : " ++ show ty ++ 
            "} -> " ++ show sc
      showApp (Bind _ x (PVar c ty) sc) [] 
          = "pat " ++ showCount c ++ show x ++ " : " ++ show ty ++ 
            " => " ++ show sc
      showApp (Bind _ x (PVTy c ty) sc) [] 
          = "pty " ++ showCount c ++ show x ++ " : " ++ show ty ++ 
            " => " ++ show sc
      showApp (App _ _ _ _) [] = "[can't happen]"
      showApp (Case _ _ _ _ _) [] = "[case tree]"
      showApp (TDelayed _ _ tm) [] = "Delayed " ++ show tm
      showApp (TDelay _ _ tm) [] = "Delay " ++ show tm
      showApp (TForce _ tm) [] = "Force " ++ show tm
      showApp (PrimVal _ c) [] = show c
      showApp (Erased _) [] = "[__]"
      showApp (TType _) [] = "Type"
      showApp _ [] = "???"
      showApp f args = "(" ++ assert_total (show f) ++ " " ++
                        assert_total (showSep " " (map (show . snd) args))
                     ++ ")"

