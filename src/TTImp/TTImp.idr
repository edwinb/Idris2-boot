module TTImp.TTImp

import Core.Binary
import Core.Context
import Core.Env
import Core.TT
import Core.TTC

%default covering

-- Information about names in nested blocks
public export
record NestedNames (vars : List Name) where
  constructor MkNested
  -- A map from names to the decorated version of the name, and the new name
  -- applied to its enclosing environment
  -- Takes the location and name type, because we don't know them until we
  -- elaborate the name at the point of use
  names : List (Name, (Maybe Name, FC -> NameType -> Term vars))

export
Weaken NestedNames where
  weaken (MkNested ns) = MkNested (map wknName ns)
    where
      wknName : (Name, (Maybe Name, FC -> NameType -> Term vars)) ->
                (Name, (Maybe Name, FC -> NameType -> Term (n :: vars)))
      wknName (n, (mn, rep)) = (n, (mn, \fc, nt => weaken (rep fc nt)))

-- Unchecked terms, with implicit arguments
-- This is the raw, elaboratable form.
-- Higher level expressions (e.g. case, pattern matching let, where blocks,
-- do notation, etc, should elaborate via this, perhaps in some local 
-- context).
mutual
  public export
  data BindMode = PI RigCount | PATTERN | NONE

  -- For as patterns matching linear arguments, select which side is
  -- consumed
  public export
  data UseSide = UseLeft | UseRight

  public export
  data RawImp : Type where
       IVar : FC -> Name -> RawImp
       IPi : FC -> RigCount -> PiInfo -> Maybe Name ->
             (argTy : RawImp) -> (retTy : RawImp) -> RawImp
       ILam : FC -> RigCount -> PiInfo -> Maybe Name ->
              (argTy : RawImp) -> (lamTy : RawImp) -> RawImp
       ILet : FC -> RigCount -> Name -> 
              (nTy : RawImp) -> (nVal : RawImp) -> 
              (scope : RawImp) -> RawImp 
       ICase : FC -> RawImp -> (ty : RawImp) ->
               List ImpClause -> RawImp
       ILocal : FC -> List ImpDecl -> RawImp -> RawImp
       IUpdate : FC -> List IFieldUpdate -> RawImp -> RawImp

       IApp : FC -> RawImp -> RawImp -> RawImp
       IImplicitApp : FC -> RawImp -> Maybe Name -> RawImp -> RawImp
       ISearch : FC -> (depth : Nat) -> RawImp
       IAlternative : FC -> AltType -> List RawImp -> RawImp
       IRewrite : FC -> RawImp -> RawImp -> RawImp
       ICoerced : FC -> RawImp -> RawImp 

       -- Any implicit bindings in the scope should be bound here, using
       -- the given binder
       IBindHere : FC -> BindMode -> RawImp -> RawImp
       -- A name which should be implicitly bound
       IBindVar : FC -> String -> RawImp
       -- An 'as' pattern, valid on the LHS of a clause only
       IAs : FC -> UseSide -> Name -> RawImp -> RawImp
       -- A 'dot' pattern, i.e. one which must also have the given value
       -- by unification
       IMustUnify : FC -> (reason : String) -> RawImp -> RawImp

       -- Laziness annotations
       IDelayed : FC -> LazyReason -> RawImp -> RawImp -- the type
       IDelay : FC -> RawImp -> RawImp -- delay constructor
       IForce : FC -> RawImp -> RawImp
       
       IPrimVal : FC -> (c : Constant) -> RawImp
       IType : FC -> RawImp
       IHole : FC -> String -> RawImp

       -- An implicit value, solved by unification, but which will also be
       -- bound (either as a pattern variable or a type variable) if unsolved
       -- at the end of elaborator                                                                     
       Implicit : FC -> (bindIfUnsolved : Bool) -> RawImp

  public export
  data IFieldUpdate : Type where
       ISetField : (path : List String) -> RawImp -> IFieldUpdate
       ISetFieldApp : (path : List String) -> RawImp -> IFieldUpdate

  public export
  data AltType : Type where
       FirstSuccess : AltType
       Unique : AltType
       UniqueDefault : RawImp -> AltType

  export
    Show RawImp where
      show (IVar fc n) = show n
      show (IPi fc c p n arg ret)
         = "(%pi " ++ show c ++ " " ++ show p ++
           " " ++ show n ++ " " ++ show arg ++ " " ++ show ret ++ ")"
      show (ILam fc c p n arg sc)
         = "(%lam " ++ show c ++ " " ++ show p ++
           " " ++ show n ++ " " ++ show arg ++ " " ++ show sc ++ ")"
      show (ILet fc c n ty val sc)
         = "(%let " ++ show c ++ " " ++ " " ++ show n ++ " " ++ show ty ++ 
           " " ++ show val ++ " " ++ show sc ++ ")"
      show (ICase _ scr scrty alts)
         = "(%case (" ++ show scr ++ ") " ++ show alts ++ ")"
      show (ILocal _ def scope)
         = "(%local (" ++ show def ++ ") " ++ show scope ++ ")"
      show (IUpdate _ flds rec)
         = "(%record " ++ showSep ", " (map show flds) ++ " " ++ show rec ++ ")"

      show (IApp fc f a)
         = "(" ++ show f ++ " " ++ show a ++ ")"
      show (IImplicitApp fc f n a)
         = "(" ++ show f ++ " [" ++ show n ++ " = " ++ show a ++ "])"
      show (ISearch fc d)
         = "%search"
      show (IAlternative fc ty alts)
         = "(|" ++ showSep "," (map show alts) ++ "|)"
      show (IRewrite _ rule tm)
         = "(%rewrite (" ++ show rule ++ ") (" ++ show tm ++ "))"
      show (ICoerced _ tm) = show tm

      show (IBindHere fc b sc)
         = "(%bindhere " ++ show sc ++ ")"
      show (IBindVar fc n) = "$" ++ n
      show (IAs fc _ n tm) = show n ++ "@(" ++ show tm ++ ")"
      show (IMustUnify fc r tm) = ".(" ++ show tm ++ ")"
      show (IDelayed fc r tm) = "(%delayed " ++ show tm ++ ")"
      show (IDelay fc tm) = "(%delay " ++ show tm ++ ")"
      show (IForce fc tm) = "(%force " ++ show tm ++ ")"
      show (IPrimVal fc c) = show c
      show (IHole _ x) = "?" ++ x
      show (IType fc) = "%type"
      show (Implicit fc True) = "_"
      show (Implicit fc False) = "?"

  export
  Show IFieldUpdate where
    show (ISetField p val) = showSep "->" p ++ " = " ++ show val
    show (ISetFieldApp p val) = showSep "->" p ++ " $= " ++ show val

  public export
  data FnOpt : Type where
       Inline : FnOpt
       -- Flag means the hint is a direct hint, not a function which might
       -- find the result (e.g. chasing parent interface dictionaries)
       Hint : Bool -> FnOpt
       -- flag means always use this in search. If not set, it is only
       -- used as a hint if all else fails (i.e. a default)
       GlobalHint : Bool -> FnOpt
       ExternFn : FnOpt
       -- assume safe to cancel arguments in unification
       Invertible : FnOpt
       Total : FnOpt
       Covering : FnOpt
       PartialOK : FnOpt

  export
  Show FnOpt where
    show Inline = "%inline"
    show (Hint t) = "%hint " ++ show t
    show (GlobalHint t) = "%globalhint " ++ show t
    show ExternFn = "%extern"
    show Invertible = "%invertible"
    show Total = "total"
    show Covering = "covering"
    show PartialOK = "partial"

  export
  Eq FnOpt where
    Inline == Inline = True
    (Hint x) == (Hint y) = x == y
    (GlobalHint x) == (GlobalHint y) = x == y
    ExternFn == ExternFn = True
    Invertible == Invertible = True
    Total == Total = True
    Covering == Covering = True
    PartialOK == PartialOK = True
    _ == _ = False

  public export
  data ImpTy : Type where
       MkImpTy : FC -> (n : Name) -> (ty : RawImp) -> ImpTy

  export
  Show ImpTy where
    show (MkImpTy fc n ty) = "(%claim " ++ show n ++ " " ++ show ty ++ ")"

  public export
  data DataOpt : Type where
       SearchBy : List Name -> DataOpt -- determining arguments
       NoHints : DataOpt -- Don't generate search hints for constructors

  export
  Eq DataOpt where
    (==) (SearchBy xs) (SearchBy ys) = xs == ys
    (==) NoHints NoHints = True
    (==) _ _ = False

  public export
  data ImpData : Type where
       MkImpData : FC -> (n : Name) -> (tycon : RawImp) ->
                   (opts : List DataOpt) -> 
                   (datacons : List ImpTy) -> ImpData
       MkImpLater : FC -> (n : Name) -> (tycon : RawImp) -> ImpData

  export
  Show ImpData where
    show (MkImpData fc n tycon _ cons)
        = "(%data " ++ show n ++ " " ++ show tycon ++ " " ++
           show cons ++ ")"
    show (MkImpLater fc n tycon)
        = "(%datadecl " ++ show n ++ " " ++ show tycon ++ ")"

  public export
  data IField : Type where
       MkIField : FC -> RigCount -> PiInfo -> Name -> RawImp ->
                  IField

  public export
  data ImpRecord : Type where
       MkImpRecord : FC -> (n : Name) ->
                     (params : List (Name, RawImp)) ->
                     (conName : Maybe Name) ->
                     (fields : List IField) ->
                     ImpRecord

  export
  Show IField where
    show (MkIField _ c Explicit n ty) = show n ++ " : " ++ show ty
    show (MkIField _ c _ n ty) = "{" ++ show n ++ " : " ++ show ty ++ "}"

  export
  Show ImpRecord where
    show (MkImpRecord _ n params con fields)
        = "record " ++ show n ++ " " ++ show params ++ 
          " " ++ show con ++ "\n\t" ++ 
          showSep "\n\t" (map show fields) ++ "\n"

  public export
  data ImpClause : Type where
       PatClause : FC -> (lhs : RawImp) -> (rhs : RawImp) -> ImpClause 
       WithClause : FC -> (lhs : RawImp) -> (wval : RawImp) ->
                    List ImpClause -> ImpClause
       ImpossibleClause : FC -> (lhs : RawImp) -> ImpClause
  
  export
  Show ImpClause where
    show (PatClause fc lhs rhs)
       = show lhs ++ " = " ++ show rhs
    show (WithClause fc lhs wval block)
       = show lhs ++ " with " ++ show wval ++ "\n\t" ++ show block
    show (ImpossibleClause fc lhs)
       = show lhs ++ " impossible"

  public export
  data ImpDecl : Type where
       IClaim : FC -> RigCount -> Visibility -> List FnOpt ->
                ImpTy -> ImpDecl
       IData : FC -> Visibility -> ImpData -> ImpDecl
       IDef : FC -> Name -> List ImpClause -> ImpDecl
       IParameters : FC -> List (Name, RawImp) ->
                     List ImpDecl -> ImpDecl 
       IRecord : FC -> Visibility -> ImpRecord -> ImpDecl
       INamespace : FC -> List String -> List ImpDecl -> ImpDecl 
       IPragma : ({vars : _} -> Ref Ctxt Defs -> 
                  NestedNames vars -> Env Term vars -> Core ()) -> 
                 ImpDecl
       ILog : Nat -> ImpDecl

  export
  Show ImpDecl where
    show (IClaim _ _ _ _ ty) = show ty
    show (IData _ _ d) = show d
    show (IDef _ n cs) = "(%def " ++ show n ++ " " ++ show cs ++ ")"
    show (IParameters _ ps ds) 
        = "parameters " ++ show ps ++ "\n\t" ++
          showSep "\n\t" (assert_total $ map show ds)
    show (IRecord _ _ d) = show d
    show (INamespace _ ns decls) 
        = "namespace " ++ show ns ++ 
          showSep "\n" (assert_total $ map show decls)
    show (IPragma _) = "[externally defined pragma]"
    show (ILog lvl) = "%logging " ++ show lvl

-- REPL commands for TTImp interaction
public export
data ImpREPL : Type where
     Eval : RawImp -> ImpREPL
     Check : RawImp -> ImpREPL
     ProofSearch : Name -> ImpREPL
     DebugInfo : Name -> ImpREPL
     Quit : ImpREPL

export
lhsInCurrentNS : {auto c : Ref Ctxt Defs} ->
                 NestedNames vars -> RawImp -> Core RawImp
lhsInCurrentNS nest (IApp loc f a)
    = do f' <- lhsInCurrentNS nest f
         pure (IApp loc f' a)
lhsInCurrentNS nest (IImplicitApp loc f n a)
    = do f' <- lhsInCurrentNS nest f
         pure (IImplicitApp loc f' n a)
lhsInCurrentNS nest tm@(IVar loc (NS _ _)) = pure tm -- leave explicit NS alone
lhsInCurrentNS nest (IVar loc n)
    = case lookup n (names nest) of
           Nothing =>
              do n' <- inCurrentNS n
                 pure (IVar loc n')
           -- If it's one of the names in the current nested block, we'll
           -- be rewriting it during elaboration to be in the scope of the
           -- parent name.
           Just _ => pure (IVar loc n)
lhsInCurrentNS nest tm = pure tm

export
findIBinds : RawImp -> List String
findIBinds (IPi fc rig p mn aty retty)
    = findIBinds aty ++ findIBinds retty
findIBinds (ILam fc rig p n aty sc)
    = findIBinds aty ++ findIBinds sc
findIBinds (IApp fc fn av)
    = findIBinds fn ++ findIBinds av
findIBinds (IImplicitApp fc fn n av)
    = findIBinds fn ++ findIBinds av
findIBinds (IAs fc _ n pat)
    = findIBinds pat
findIBinds (IMustUnify fc r pat)
    = findIBinds pat
findIBinds (IAlternative fc u alts)
    = concatMap findIBinds alts
findIBinds (IDelayed fc _ ty) = findIBinds ty
findIBinds (IDelay fc tm) = findIBinds tm
findIBinds (IForce fc tm) = findIBinds tm
findIBinds (IBindVar _ n) = [n]
-- We've skipped lambda, case, let and local - rather than guess where the
-- name should be bound, leave it to the programmer
findIBinds tm = []

export
findImplicits : RawImp -> List String
findImplicits (IPi fc rig p (Just (UN mn)) aty retty)
    = mn :: findImplicits aty ++ findImplicits retty
findImplicits (IPi fc rig p mn aty retty)
    = findImplicits aty ++ findImplicits retty
findImplicits (ILam fc rig p n aty sc)
    = findImplicits aty ++ findImplicits sc
findImplicits (IApp fc fn av)
    = findImplicits fn ++ findImplicits av
findImplicits (IImplicitApp fc fn n av)
    = findImplicits fn ++ findImplicits av
findImplicits (IAs fc _ n pat)
    = findImplicits pat
findImplicits (IMustUnify fc r pat)
    = findImplicits pat
findImplicits (IAlternative fc u alts)
    = concatMap findImplicits alts
findImplicits (IBindVar _ n) = [n]
findImplicits tm = []
         
export
definedInBlock : List ImpDecl -> List Name
definedInBlock = concatMap defName
  where
    getName : ImpTy -> Name
    getName (MkImpTy _ n _) = n

    defName : ImpDecl -> List Name
    defName (IClaim _ _ _ _ ty) = [getName ty]
    defName (IData _ _ (MkImpData _ n _ _ cons)) = n :: map getName cons
    defName (IData _ _ (MkImpLater _ n _)) = [n]
    defName (IParameters _ _ pds) = concatMap defName pds
    defName (IRecord _ _ (MkImpRecord _ n _ _ _)) = [n]
    defName _ = []

export
getFC : RawImp -> FC
getFC (IVar x _) = x
getFC (IPi x _ _ _ _ _) = x
getFC (ILam x _ _ _ _ _) = x
getFC (ILet x _ _ _ _ _) = x
getFC (ICase x _ _ _) = x
getFC (ILocal x _ _) = x
getFC (IUpdate x _ _) = x
getFC (IApp x _ _) = x
getFC (IImplicitApp x _ _ _) = x
getFC (ISearch x _) = x
getFC (IAlternative x _ _) = x
getFC (IRewrite x _ _) = x
getFC (ICoerced x _) = x
getFC (IPrimVal x _) = x
getFC (IHole x _) = x
getFC (IType x) = x
getFC (IBindVar x _) = x
getFC (IBindHere x _ _) = x
getFC (IMustUnify x _ _) = x
getFC (IDelayed x _ _) = x
getFC (IDelay x _) = x
getFC (IForce x _) = x
getFC (IAs x _ _ _) = x
getFC (Implicit x _) = x

export
apply : RawImp -> List RawImp -> RawImp
apply f [] = f
apply f (x :: xs) = apply (IApp (getFC f) f x) xs

export
getFn : RawImp -> RawImp
getFn (IApp _ f arg) = getFn f
getFn (IImplicitApp _ f _ _) = getFn f
getFn f = f

-- Everything below is TTC instances

mutual
  export
  TTC RawImp where
    toBuf b (IVar fc n) = do tag 0; toBuf b fc; toBuf b n
    toBuf b (IPi fc r p n argTy retTy) 
        = do tag 1; toBuf b fc; toBuf b r; toBuf b p; toBuf b n
             toBuf b argTy; toBuf b retTy
    toBuf b (ILam fc r p n argTy scope) 
        = do tag 2; toBuf b fc; toBuf b r; toBuf b p; toBuf b n;
             toBuf b argTy; toBuf b scope
    toBuf b (ILet fc r n nTy nVal scope) 
        = do tag 3; toBuf b fc; toBuf b r; toBuf b n; 
             toBuf b nTy; toBuf b nVal; toBuf b scope
    toBuf b (ICase fc y ty xs) 
        = do tag 4; toBuf b fc; toBuf b y; toBuf b ty; toBuf b xs
    toBuf b (ILocal fc xs sc) 
        = do tag 5; toBuf b fc; toBuf b xs; toBuf b sc
    toBuf b (IUpdate fc fs rec) 
        = do tag 6; toBuf b fc; toBuf b fs; toBuf b rec
    toBuf b (IApp fc fn arg) 
        = do tag 7; toBuf b fc; toBuf b fn; toBuf b arg
    toBuf b (IImplicitApp fc fn y arg) 
        = do tag 8; toBuf b fc; toBuf b fn; toBuf b y; toBuf b arg
    toBuf b (ISearch fc depth) 
        = do tag 9; toBuf b fc; toBuf b depth
    toBuf b (IAlternative fc y xs) 
        = do tag 10; toBuf b fc; toBuf b y; toBuf b xs
    toBuf b (IRewrite fc x y) 
        = do tag 11; toBuf b fc; toBuf b x; toBuf b y
    toBuf b (ICoerced fc y) 
        = do tag 12; toBuf b fc; toBuf b y

    toBuf b (IBindHere fc m y)
        = do tag 13; toBuf b fc; toBuf b m; toBuf b y
    toBuf b (IBindVar fc y)
        = do tag 14; toBuf b fc; toBuf b y
    toBuf b (IAs fc s y pattern)
        = do tag 15; toBuf b fc; toBuf b s; toBuf b y; toBuf b pattern
    toBuf b (IMustUnify fc r pattern)
        -- No need to record 'r', it's for type errors only
        = do tag 16; toBuf b fc; toBuf b pattern

    toBuf b (IDelayed fc r y)
        = do tag 17; toBuf b fc; toBuf b r; toBuf b y
    toBuf b (IDelay fc t)
        = do tag 18; toBuf b fc; toBuf b t
    toBuf b (IForce fc t)
        = do tag 19; toBuf b fc; toBuf b t

    toBuf b (IPrimVal fc y)
        = do tag 20; toBuf b fc; toBuf b y
    toBuf b (IType fc)
        = do tag 21; toBuf b fc
    toBuf b (IHole fc y)
        = do tag 22; toBuf b fc; toBuf b y

    toBuf b (Implicit fc i)
        = do tag 23; toBuf b fc; toBuf b i

    fromBuf s b
        = case !getTag of
               0 => do fc <- fromBuf s b; n <- fromBuf s b;
                       pure (IVar fc n)
               1 => do fc <- fromBuf s b;
                       r <- fromBuf s b; p <- fromBuf s b; 
                       n <- fromBuf s b
                       argTy <- fromBuf s b; retTy <- fromBuf s b
                       pure (IPi fc r p n argTy retTy)
               2 => do fc <- fromBuf s b;
                       r <- fromBuf s b; p <- fromBuf s b; n <- fromBuf s b
                       argTy <- fromBuf s b; scope <- fromBuf s b
                       pure (ILam fc r p n argTy scope)
               3 => do fc <- fromBuf s b;
                       r <- fromBuf s b; n <- fromBuf s b
                       nTy <- fromBuf s b; nVal <- fromBuf s b
                       scope <- fromBuf s b
                       pure (ILet fc r n nTy nVal scope)
               4 => do fc <- fromBuf s b; y <- fromBuf s b;
                       ty <- fromBuf s b; xs <- fromBuf s b
                       pure (ICase fc y ty xs)
               5 => do fc <- fromBuf s b;
                       xs <- fromBuf s b; sc <- fromBuf s b
                       pure (ILocal fc xs sc)
               6 => do fc <- fromBuf s b; fs <- fromBuf s b
                       rec <- fromBuf s b
                       pure (IUpdate fc fs rec)
               7 => do fc <- fromBuf s b; fn <- fromBuf s b
                       arg <- fromBuf s b
                       pure (IApp fc fn arg)
               8 => do fc <- fromBuf s b; fn <- fromBuf s b
                       y <- fromBuf s b; arg <- fromBuf s b
                       pure (IImplicitApp fc fn y arg)
               9 => do fc <- fromBuf s b; depth <- fromBuf s b
                       pure (ISearch fc depth)
               10 => do fc <- fromBuf s b; y <- fromBuf s b
                        xs <- fromBuf s b
                        pure (IAlternative fc y xs)
               11 => do fc <- fromBuf s b; x <- fromBuf s b; y <- fromBuf s b
                        pure (IRewrite fc x y)
               12 => do fc <- fromBuf s b; y <- fromBuf s b
                        pure (ICoerced fc y)
               13 => do fc <- fromBuf s b; m <- fromBuf s b; y <- fromBuf s b
                        pure (IBindHere fc m y)
               14 => do fc <- fromBuf s b; y <- fromBuf s b
                        pure (IBindVar fc y)
               15 => do fc <- fromBuf s b; side <- fromBuf s b
                        y <- fromBuf s b
                        pattern <- fromBuf s b
                        pure (IAs fc side y pattern)
               16 => do fc <- fromBuf s b
                        pattern <- fromBuf s b
                        pure (IMustUnify fc "" pattern)

               17 => do fc <- fromBuf s b; r <- fromBuf s b
                        y <- fromBuf s b
                        pure (IDelayed fc r y)
               18 => do fc <- fromBuf s b; y <- fromBuf s b
                        pure (IDelay fc y)
               19 => do fc <- fromBuf s b; y <- fromBuf s b
                        pure (IForce fc y)

               20 => do fc <- fromBuf s b; y <- fromBuf s b
                        pure (IPrimVal fc y)
               21 => do fc <- fromBuf s b
                        pure (IType fc)
               22 => do fc <- fromBuf s b; y <- fromBuf s b
                        pure (IHole fc y)
               23 => do fc <- fromBuf s b
                        i <- fromBuf s b
                        pure (Implicit fc i)
               _ => corrupt "RawImp"
  
  export
  TTC IFieldUpdate where
    toBuf b (ISetField p val)
        = do tag 0; toBuf b p; toBuf b val
    toBuf b (ISetFieldApp p val)
        = do tag 1; toBuf b p; toBuf b val

    fromBuf s b
        = case !getTag of
               0 => do p <- fromBuf s b; val <- fromBuf s b
                       pure (ISetField p val)
               1 => do p <- fromBuf s b; val <- fromBuf s b
                       pure (ISetFieldApp p val)
               _ => corrupt "IFieldUpdate"

  export
  TTC BindMode where
    toBuf b (PI r) = do tag 0; toBuf b r
    toBuf b PATTERN = tag 1
    toBuf b NONE = tag 2

    fromBuf s b
        = case !getTag of
               0 => do x <- fromBuf s b
                       pure (PI x)
               1 => pure PATTERN
               2 => pure NONE
               _ => corrupt "BindMode"

  export
  TTC UseSide where
    toBuf b UseLeft = tag 0
    toBuf b UseRight = tag 1

    fromBuf s b
        = case !getTag of
               0 => pure UseLeft
               1 => pure UseRight
               _ => corrupt "UseSide"

  export
  TTC AltType where
    toBuf b FirstSuccess = tag 0
    toBuf b Unique = tag 1
    toBuf b (UniqueDefault x) = do tag 2; toBuf b x

    fromBuf s b
        = case !getTag of
               0 => pure FirstSuccess
               1 => pure Unique
               2 => do x <- fromBuf s b
                       pure (UniqueDefault x)
               _ => corrupt "AltType"
  
  export
  TTC ImpTy where
    toBuf b (MkImpTy fc n ty) 
        = do toBuf b fc; toBuf b n; toBuf b ty
    fromBuf s b
        = do fc <- fromBuf s b; n <- fromBuf s b; ty <- fromBuf s b
             pure (MkImpTy fc n ty)

  export
  TTC ImpClause where
    toBuf b (PatClause fc lhs rhs) 
        = do tag 0; toBuf b fc; toBuf b lhs; toBuf b rhs
    toBuf b (ImpossibleClause fc lhs) 
        = do tag 1; toBuf b fc; toBuf b lhs
    toBuf b (WithClause fc lhs wval cs) 
        = do tag 2; toBuf b fc; toBuf b lhs; toBuf b wval; toBuf b cs

    fromBuf s b
        = case !getTag of
               0 => do fc <- fromBuf s b; lhs <- fromBuf s b; 
                       rhs <- fromBuf s b
                       pure (PatClause fc lhs rhs)
               1 => do fc <- fromBuf s b; lhs <- fromBuf s b; 
                       pure (ImpossibleClause fc lhs)
               2 => do fc <- fromBuf s b; lhs <- fromBuf s b; 
                       wval <- fromBuf s b; cs <- fromBuf s b
                       pure (WithClause fc lhs wval cs)
               _ => corrupt "ImpClause"

  export
  TTC DataOpt where
    toBuf b (SearchBy ns) 
        = do tag 0; toBuf b ns
    toBuf b NoHints = tag 1

    fromBuf s b
        = case !getTag of
               0 => do ns <- fromBuf s b
                       pure (SearchBy ns)
               1 => pure NoHints
               _ => corrupt "DataOpt"

  export
  TTC ImpData where
    toBuf b (MkImpData fc n tycon opts cons) 
        = do tag 0; toBuf b fc; toBuf b n; toBuf b tycon; toBuf b opts
             toBuf b cons
    toBuf b (MkImpLater fc n tycon) 
        = do tag 1; toBuf b fc; toBuf b n; toBuf b tycon

    fromBuf s b
        = case !getTag of
               0 => do fc <- fromBuf s b; n <- fromBuf s b;
                       tycon <- fromBuf s b; opts <- fromBuf s b
                       cons <- fromBuf s b
                       pure (MkImpData fc n tycon opts cons)
               1 => do fc <- fromBuf s b; n <- fromBuf s b;
                       tycon <- fromBuf s b
                       pure (MkImpLater fc n tycon)
               _ => corrupt "ImpData"

  export
  TTC IField where
    toBuf b (MkIField fc c p n ty)
        = do toBuf b fc; toBuf b c; toBuf b p; toBuf b n; toBuf b ty

    fromBuf s b
        = do fc <- fromBuf s b; c <- fromBuf s b; p <- fromBuf s b
             n <- fromBuf s b; ty <- fromBuf s b
             pure (MkIField fc c p n ty)

  export
  TTC ImpRecord where
    toBuf b (MkImpRecord fc n ps con fs)
        = do toBuf b fc; toBuf b n; toBuf b ps; toBuf b con; toBuf b fs

    fromBuf s b
        = do fc <- fromBuf s b; n <- fromBuf s b; ps <- fromBuf s b
             con <- fromBuf s b; fs <- fromBuf s b
             pure (MkImpRecord fc n ps con fs)

  export
  TTC FnOpt where
    toBuf b Inline = tag 0
    toBuf b (Hint t) = do tag 1; toBuf b t
    toBuf b (GlobalHint t) = do tag 2; toBuf b t
    toBuf b ExternFn = tag 3
    toBuf b Invertible = tag 4
    toBuf b Total = tag 5
    toBuf b Covering = tag 6
    toBuf b PartialOK = tag 7

    fromBuf s b
        = case !getTag of
               0 => pure Inline
               1 => do t <- fromBuf s b; pure (Hint t)
               2 => do t <- fromBuf s b; pure (GlobalHint t)
               3 => pure ExternFn
               4 => pure Invertible
               5 => pure Total
               6 => pure Covering
               7 => pure PartialOK
               _ => corrupt "FnOpt"

  export
  TTC ImpDecl where
    toBuf b (IClaim fc c vis xs d) 
        = do tag 0; toBuf b c; toBuf b fc; toBuf b vis; toBuf b xs; toBuf b d
    toBuf b (IData fc vis d) 
        = do tag 1; toBuf b fc; toBuf b vis; toBuf b d
    toBuf b (IDef fc n xs) 
        = do tag 2; toBuf b fc; toBuf b n; toBuf b xs
    toBuf b (IParameters fc vis d) 
        = do tag 3; toBuf b fc; toBuf b vis; toBuf b d
    toBuf b (IRecord fc vis r) 
        = do tag 4; toBuf b fc; toBuf b vis; toBuf b r
    toBuf b (INamespace fc xs ds) 
        = do tag 5; toBuf b fc; toBuf b xs; toBuf b ds
    toBuf b (IPragma f) = throw (InternalError "Can't write Pragma")
    toBuf b (ILog n) 
        = do tag 6; toBuf b n

    fromBuf s b
        = case !getTag of
               0 => do fc <- fromBuf s b; c <- fromBuf s b
                       vis <- fromBuf s b;
                       xs <- fromBuf s b; d <- fromBuf s b
                       pure (IClaim fc c vis xs d)
               1 => do fc <- fromBuf s b; vis <- fromBuf s b
                       d <- fromBuf s b
                       pure (IData fc vis d)
               2 => do fc <- fromBuf s b; n <- fromBuf s b
                       xs <- fromBuf s b
                       pure (IDef fc n xs)
               3 => do fc <- fromBuf s b; vis <- fromBuf s b
                       d <- fromBuf s b
                       pure (IParameters fc vis d)
               4 => do fc <- fromBuf s b; vis <- fromBuf s b
                       r <- fromBuf s b
                       pure (IRecord fc vis r)
               5 => do fc <- fromBuf s b; xs <- fromBuf s b
                       ds <- fromBuf s b
                       pure (INamespace fc xs ds)
               6 => do n <- fromBuf s b
                       pure (ILog n)
               _ => corrupt "ImpDecl"

