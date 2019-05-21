module TTImp.TTImp

import Core.Context
import Core.Env
import Core.TT

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

  export
  Eq FnOpt where
    (==) Inline Inline = True
    (==) _ _ = False

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
  data ImpClause : Type where
       PatClause : FC -> (lhs : RawImp) -> (rhs : RawImp) -> ImpClause 
--        WithClause : FC -> (lhs : RawImp) -> (wval : RawImp) ->
--                     List ImpClause -> ImpClause
       ImpossibleClause : FC -> (lhs : RawImp) -> ImpClause
  
  export
  Show ImpClause where
    show (PatClause fc lhs rhs)
       = show lhs ++ " = " ++ show rhs
    show (ImpossibleClause fc lhs)
       = show lhs ++ " impossible"

  public export
  data ImpDecl : Type where
       IClaim : FC -> RigCount -> Visibility -> List FnOpt ->
                ImpTy -> ImpDecl
       IData : FC -> Visibility -> ImpData -> ImpDecl
       IDef : FC -> Name -> List ImpClause -> ImpDecl
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

