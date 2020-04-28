module TTImp.TTImp

import Core.Binary
import Core.Context
import Core.Env
import Core.Normalise
import Core.TT
import Core.TTC
import Core.Value

%default covering

-- Information about names in nested blocks
public export
record NestedNames (vars : List Name) where
  constructor MkNested
  -- A map from names to the decorated version of the name, and the new name
  -- applied to its enclosing environment
  -- Takes the location and name type, because we don't know them until we
  -- elaborate the name at the point of use
  names : List (Name, (Maybe Name,  -- new name if there is one
                       List Name, -- names used from the environment
                       FC -> NameType -> Term vars))

export
Weaken NestedNames where
  weaken (MkNested ns) = MkNested (map wknName ns)
    where
      wknName : (Name, (Maybe Name, List Name, FC -> NameType -> Term vars)) ->
                (Name, (Maybe Name, List Name, FC -> NameType -> Term (n :: vars)))
      wknName (n, (mn, len, rep)) = (n, (mn, len, \fc, nt => weaken (rep fc nt)))

-- Unchecked terms, with implicit arguments
-- This is the raw, elaboratable form.
-- Higher level expressions (e.g. case, pattern matching let, where blocks,
-- do notation, etc, should elaborate via this, perhaps in some local
-- context).
public export
data BindMode = PI RigCount | PATTERN | NONE

mutual
  public export
  data RawImp : Type where
       IVar : FC -> Name -> RawImp
       IPi : FC -> RigCount -> PiInfo RawImp -> Maybe Name ->
             (argTy : RawImp) -> (retTy : RawImp) -> RawImp
       ILam : FC -> RigCount -> PiInfo RawImp -> Maybe Name ->
              (argTy : RawImp) -> (lamTy : RawImp) -> RawImp
       ILet : FC -> RigCount -> Name ->
              (nTy : RawImp) -> (nVal : RawImp) ->
              (scope : RawImp) -> RawImp
       ICase : FC -> RawImp -> (ty : RawImp) ->
               List ImpClause -> RawImp
       ILocal : FC -> List ImpDecl -> RawImp -> RawImp
       -- Local definitions made elsewhere, but that we're pushing
       -- into a case branch as nested names.
       -- An appearance of 'uname' maps to an application of
       -- 'internalName' to 'args'.
       ICaseLocal : FC -> (uname : Name) ->
                    (internalName : Name) ->
                    (args : List Name) -> RawImp -> RawImp

       IUpdate : FC -> List IFieldUpdate -> RawImp -> RawImp

       IApp : FC -> RawImp -> RawImp -> RawImp
       IImplicitApp : FC -> RawImp -> Maybe Name -> RawImp -> RawImp
       IWithApp : FC -> RawImp -> RawImp -> RawImp

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
       IMustUnify : FC -> DotReason -> RawImp -> RawImp

       -- Laziness annotations
       IDelayed : FC -> LazyReason -> RawImp -> RawImp -- the type
       IDelay : FC -> RawImp -> RawImp -- delay constructor
       IForce : FC -> RawImp -> RawImp

       -- Quasiquoting
       IQuote : FC -> RawImp -> RawImp
       IQuoteDecl : FC -> ImpDecl -> RawImp
       IUnquote : FC -> RawImp -> RawImp
       IRunElab : FC -> RawImp -> RawImp

       IPrimVal : FC -> (c : Constant) -> RawImp
       IType : FC -> RawImp
       IHole : FC -> String -> RawImp

       IUnifyLog : FC -> Nat -> RawImp -> RawImp
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
         = "(%case (" ++ show scr ++ " : " ++ show scrty ++ ") " ++ show alts ++ ")"
      show (ILocal _ def scope)
         = "(%local (" ++ show def ++ ") " ++ show scope ++ ")"
      show (ICaseLocal _ uname iname args sc)
         = "(%caselocal (" ++ show uname ++ " " ++ show iname
               ++ " " ++ show args ++ ") " ++ show sc ++ ")"
      show (IUpdate _ flds rec)
         = "(%record " ++ showSep ", " (map show flds) ++ " " ++ show rec ++ ")"

      show (IApp fc f a)
         = "(" ++ show f ++ " " ++ show a ++ ")"
      show (IImplicitApp fc f n a)
         = "(" ++ show f ++ " [" ++ show n ++ " = " ++ show a ++ "])"
      show (IWithApp fc f a)
         = "(" ++ show f ++ " | " ++ show a ++ ")"
      show (ISearch fc d)
         = "%search"
      show (IAlternative fc ty alts)
         = "(|" ++ showSep "," (map show alts) ++ "|)"
      show (IRewrite _ rule tm)
         = "(%rewrite (" ++ show rule ++ ") (" ++ show tm ++ "))"
      show (ICoerced _ tm) = "(%coerced " ++ show tm ++ ")"

      show (IBindHere fc b sc)
         = "(%bindhere " ++ show sc ++ ")"
      show (IBindVar fc n) = "$" ++ n
      show (IAs fc _ n tm) = show n ++ "@(" ++ show tm ++ ")"
      show (IMustUnify fc r tm) = ".(" ++ show tm ++ ")"
      show (IDelayed fc r tm) = "(%delayed " ++ show tm ++ ")"
      show (IDelay fc tm) = "(%delay " ++ show tm ++ ")"
      show (IForce fc tm) = "(%force " ++ show tm ++ ")"
      show (IQuote fc tm) = "(%quote " ++ show tm ++ ")"
      show (IQuoteDecl fc tm) = "(%quotedecl " ++ show tm ++ ")"
      show (IUnquote fc tm) = "(%unquote " ++ show tm ++ ")"
      show (IRunElab fc tm) = "(%runelab " ++ show tm ++ ")"
      show (IPrimVal fc c) = show c
      show (IHole _ x) = "?" ++ x
      show (IUnifyLog _ lvl x) = "(%logging " ++ show lvl ++ " " ++ show x ++ ")"
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
       -- Flag means to use as a default if all else fails
       GlobalHint : Bool -> FnOpt
       ExternFn : FnOpt
       -- Defined externally, list calling conventions
       ForeignFn : List RawImp -> FnOpt
       -- assume safe to cancel arguments in unification
       Invertible : FnOpt
       Totality : TotalReq -> FnOpt
       Macro : FnOpt
       SpecArgs : List Name -> FnOpt

  export
  Show FnOpt where
    show Inline = "%inline"
    show (Hint t) = "%hint " ++ show t
    show (GlobalHint t) = "%globalhint " ++ show t
    show ExternFn = "%extern"
    show (ForeignFn cs) = "%foreign " ++ showSep " " (map show cs)
    show Invertible = "%invertible"
    show (Totality Total) = "total"
    show (Totality CoveringOnly) = "covering"
    show (Totality PartialOK) = "partial"
    show Macro = "%macro"
    show (SpecArgs ns) = "%spec " ++ showSep " " (map show ns)

  export
  Eq FnOpt where
    Inline == Inline = True
    (Hint x) == (Hint y) = x == y
    (GlobalHint x) == (GlobalHint y) = x == y
    ExternFn == ExternFn = True
    (ForeignFn xs) == (ForeignFn ys) = True -- xs == ys
    Invertible == Invertible = True
    (Totality tot_lhs) == (Totality tot_rhs) = tot_lhs == tot_rhs
    Macro == Macro = True
    (SpecArgs ns) == (SpecArgs ns') = ns == ns'
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
       UniqueSearch : DataOpt -- auto implicit search must check result is unique
       External : DataOpt -- implemented externally

  export
  Eq DataOpt where
    (==) (SearchBy xs) (SearchBy ys) = xs == ys
    (==) NoHints NoHints = True
    (==) UniqueSearch UniqueSearch = True
    (==) External External = True
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
       MkIField : FC -> RigCount -> PiInfo RawImp -> Name -> RawImp ->
                  IField

  public export
  data ImpRecord : Type where
       MkImpRecord : FC -> (n : Name) ->
                     (params : List (Name, RigCount, PiInfo RawImp, RawImp)) ->
                     (conName : Name) ->
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
       IRecord : FC ->
                 Maybe String -> -- nested namespace
                 Visibility -> ImpRecord -> ImpDecl
       INamespace : FC -> List String -> List ImpDecl -> ImpDecl
       ITransform : FC -> RawImp -> RawImp -> ImpDecl
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
    show (IRecord _ _ _ d) = show d
    show (INamespace _ ns decls)
        = "namespace " ++ show ns ++
          showSep "\n" (assert_total $ map show decls)
    show (ITransform _ lhs rhs)
        = "%transform " ++ show lhs ++ " ==> " ++ show rhs
    show (IPragma _) = "[externally defined pragma]"
    show (ILog lvl) = "%logging " ++ show lvl

-- REPL commands for TTImp interaction
public export
data ImpREPL : Type where
     Eval : RawImp -> ImpREPL
     Check : RawImp -> ImpREPL
     ProofSearch : Name -> ImpREPL
     ExprSearch : Name -> ImpREPL
     GenerateDef : Int -> Name -> ImpREPL
     Missing : Name -> ImpREPL
     CheckTotal : Name -> ImpREPL
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
lhsInCurrentNS nest (IWithApp loc f a)
    = do f' <- lhsInCurrentNS nest f
         pure (IWithApp loc f' a)
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
findIBinds (IWithApp fc fn av)
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
findIBinds (IQuote fc tm) = findIBinds tm
findIBinds (IUnquote fc tm) = findIBinds tm
findIBinds (IRunElab fc tm) = findIBinds tm
findIBinds (IBindHere _ _ tm) = findIBinds tm
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
findImplicits (IWithApp fc fn av)
    = findImplicits fn ++ findImplicits av
findImplicits (IAs fc _ n pat)
    = findImplicits pat
findImplicits (IMustUnify fc r pat)
    = findImplicits pat
findImplicits (IAlternative fc u alts)
    = concatMap findImplicits alts
findImplicits (IDelayed fc _ ty) = findImplicits ty
findImplicits (IDelay fc tm) = findImplicits tm
findImplicits (IForce fc tm) = findImplicits tm
findImplicits (IQuote fc tm) = findImplicits tm
findImplicits (IUnquote fc tm) = findImplicits tm
findImplicits (IRunElab fc tm) = findImplicits tm
findImplicits (IBindVar _ n) = [n]
findImplicits tm = []

-- Update the lhs of a clause so that any implicits named in the type are
-- bound as @-patterns (unless they're already explicitly bound or appear as
-- IBindVar anywhere else in the pattern) so that they will be available on the
-- rhs
export
implicitsAs : Defs -> List Name -> RawImp -> Core RawImp
implicitsAs defs ns tm = setAs (map Just (ns ++ map UN (findIBinds tm))) tm
  where
    setAs : List (Maybe Name) -> RawImp -> Core RawImp
    setAs is (IApp loc f a)
        = do f' <- setAs is f
             pure $ IApp loc f' a
    setAs is (IImplicitApp loc f n a)
        = do f' <- setAs (n :: is) f
             pure $ IImplicitApp loc f' n a
    setAs is (IWithApp loc f a)
        = do f' <- setAs is f
             pure $ IWithApp loc f' a
    setAs is (IVar loc n)
        = case !(lookupTyExact n (gamma defs)) of
               Nothing => pure $ IVar loc n
               Just ty => pure $ impAs loc
                                    !(findImps is !(nf defs [] ty)) (IVar loc n)
      where
        -- If there's an @{c} in the list of given implicits, that's the next
        -- autoimplicit, so don't rewrite the LHS and update the list of given
        -- implicits
        updateNs : Name -> List (Maybe Name) -> Maybe (List (Maybe Name))
        updateNs n (Nothing :: ns) = Just ns
        updateNs n (x :: ns)
            = if Just n == x
                 then Just ns -- found it
                 else do ns' <- updateNs n ns
                         pure (x :: ns')
        updateNs n [] = Nothing

        findImps : List (Maybe Name) -> NF [] -> Core (List (Name, PiInfo RawImp))
        findImps ns (NBind fc x (Pi _ Explicit _) sc)
            = findImps ns !(sc defs (toClosure defaultOpts [] (Erased fc False)))
        -- if the implicit was given, skip it
        findImps ns (NBind fc x (Pi _ AutoImplicit _) sc)
            = case updateNs x ns of
                   Nothing => -- didn't find explicit call
                      pure $ (x, AutoImplicit) :: !(findImps ns !(sc defs (toClosure defaultOpts [] (Erased fc False))))
                   Just ns' => findImps ns' !(sc defs (toClosure defaultOpts [] (Erased fc False)))
        findImps ns (NBind fc x (Pi _ p _) sc)
            = if Just x `elem` ns
                 then findImps ns !(sc defs (toClosure defaultOpts [] (Erased fc False)))
                 else pure $ (x, forgetDef p) :: !(findImps ns !(sc defs (toClosure defaultOpts [] (Erased fc False))))
        findImps _ _ = pure []

        impAs : FC -> List (Name, PiInfo RawImp) -> RawImp -> RawImp
        impAs loc' [] tm = tm
        impAs loc' ((UN n, AutoImplicit) :: ns) tm
            = impAs loc' ns $
                 IImplicitApp loc' tm (Just (UN n)) (IBindVar loc' n)
        impAs loc' ((n, Implicit) :: ns) tm
            = impAs loc' ns $
                 IImplicitApp loc' tm (Just n)
                     (IAs loc' UseLeft n (Implicit loc' True))
        impAs loc' ((n, DefImplicit t) :: ns) tm
            = impAs loc' ns $
                 IImplicitApp loc' tm (Just n)
                     (IAs loc' UseLeft n (Implicit loc' True))
        impAs loc' (_ :: ns) tm = impAs loc' ns tm
    setAs is tm = pure tm

export
definedInBlock : List String -> -- namespace to resolve names
                 List ImpDecl -> List Name
definedInBlock ns decls =
    concatMap (defName ns) decls
  where
    getName : ImpTy -> Name
    getName (MkImpTy _ n _) = n

    getFieldName : IField -> Name
    getFieldName (MkIField _ _ _ n _) = n

    expandNS : List String -> Name -> Name
    expandNS [] n = n
    expandNS ns (UN n) = NS ns (UN n)
    expandNS ns (RF n) = NS ns (RF n)
    expandNS ns n@(MN _ _) = NS ns n
    expandNS ns n@(DN _ _) = NS ns n
    expandNS ns n = n

    defName : List String -> ImpDecl -> List Name
    defName ns (IClaim _ _ _ _ ty) = [expandNS ns (getName ty)]
    defName ns (IData _ _ (MkImpData _ n _ _ cons))
        = expandNS ns n :: map (expandNS ns) (map getName cons)
    defName ns (IData _ _ (MkImpLater _ n _)) = [expandNS ns n]
    defName ns (IParameters _ _ pds) = concatMap (defName ns) pds
    defName ns (INamespace _ n nds) = concatMap (defName (n ++ ns)) nds
    defName ns (IRecord _ fldns _ (MkImpRecord _ n _ con flds))
        = expandNS ns con :: all
      where
        fldns' : List String
        fldns' = maybe ns (\f => f :: ns) fldns

        toRF : Name -> Name
        toRF (UN n) = RF n
        toRF n = n

        fnsUN : List Name
        fnsUN = map getFieldName flds

        fnsRF : List Name
        fnsRF = map toRF fnsUN

        -- Depending on %undotted_record_projections,
        -- the record may or may not produce undotted projections (fnsUN).
        --
        -- However, since definedInBlock is pure, we can't check that flag
        -- (and it would also be wrong if %undotted_record_projections appears
        -- inside the parameter block)
        -- so let's just declare all of them and some may go unused.
        all : List Name
        all = expandNS ns n :: map (expandNS fldns') (fnsRF ++ fnsUN)

    defName _ _ = []

export
getFC : RawImp -> FC
getFC (IVar x _) = x
getFC (IPi x _ _ _ _ _) = x
getFC (ILam x _ _ _ _ _) = x
getFC (ILet x _ _ _ _ _) = x
getFC (ICase x _ _ _) = x
getFC (ILocal x _ _) = x
getFC (ICaseLocal x _ _ _ _) = x
getFC (IUpdate x _ _) = x
getFC (IApp x _ _) = x
getFC (IImplicitApp x _ _ _) = x
getFC (IWithApp x _ _) = x
getFC (ISearch x _) = x
getFC (IAlternative x _ _) = x
getFC (IRewrite x _ _) = x
getFC (ICoerced x _) = x
getFC (IPrimVal x _) = x
getFC (IHole x _) = x
getFC (IUnifyLog x _ _) = x
getFC (IType x) = x
getFC (IBindVar x _) = x
getFC (IBindHere x _ _) = x
getFC (IMustUnify x _ _) = x
getFC (IDelayed x _ _) = x
getFC (IDelay x _) = x
getFC (IForce x _) = x
getFC (IQuote x _) = x
getFC (IQuoteDecl x _) = x
getFC (IUnquote x _) = x
getFC (IRunElab x _) = x
getFC (IAs x _ _ _) = x
getFC (Implicit x _) = x

export
apply : RawImp -> List RawImp -> RawImp
apply f [] = f
apply f (x :: xs) = apply (IApp (getFC f) f x) xs

export
getFn : RawImp -> RawImp
getFn (IApp _ f arg) = getFn f
getFn (IWithApp _ f arg) = getFn f
getFn (IImplicitApp _ f _ _) = getFn f
getFn (IAs _ _ _ f) = getFn f
getFn (IMustUnify _ _ f) = getFn f
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
    toBuf b (ICaseLocal fc _ _ _ sc)
        = toBuf b sc
    toBuf b (IUpdate fc fs rec)
        = do tag 6; toBuf b fc; toBuf b fs; toBuf b rec
    toBuf b (IApp fc fn arg)
        = do tag 7; toBuf b fc; toBuf b fn; toBuf b arg
    toBuf b (IImplicitApp fc fn y arg)
        = do tag 8; toBuf b fc; toBuf b fn; toBuf b y; toBuf b arg
    toBuf b (IWithApp fc fn arg)
        = do tag 9; toBuf b fc; toBuf b fn; toBuf b arg
    toBuf b (ISearch fc depth)
        = do tag 10; toBuf b fc; toBuf b depth
    toBuf b (IAlternative fc y xs)
        = do tag 11; toBuf b fc; toBuf b y; toBuf b xs
    toBuf b (IRewrite fc x y)
        = do tag 12; toBuf b fc; toBuf b x; toBuf b y
    toBuf b (ICoerced fc y)
        = do tag 13; toBuf b fc; toBuf b y

    toBuf b (IBindHere fc m y)
        = do tag 14; toBuf b fc; toBuf b m; toBuf b y
    toBuf b (IBindVar fc y)
        = do tag 15; toBuf b fc; toBuf b y
    toBuf b (IAs fc s y pattern)
        = do tag 16; toBuf b fc; toBuf b s; toBuf b y; toBuf b pattern
    toBuf b (IMustUnify fc r pattern)
        -- No need to record 'r', it's for type errors only
        = do tag 17; toBuf b fc; toBuf b pattern

    toBuf b (IDelayed fc r y)
        = do tag 18; toBuf b fc; toBuf b r; toBuf b y
    toBuf b (IDelay fc t)
        = do tag 19; toBuf b fc; toBuf b t
    toBuf b (IForce fc t)
        = do tag 20; toBuf b fc; toBuf b t

    toBuf b (IQuote fc t)
        = do tag 21; toBuf b fc; toBuf b t
    toBuf b (IQuoteDecl fc t)
        = do tag 22; toBuf b fc; toBuf b t
    toBuf b (IUnquote fc t)
        = do tag 23; toBuf b fc; toBuf b t
    toBuf b (IRunElab fc t)
        = do tag 24; toBuf b fc; toBuf b t

    toBuf b (IPrimVal fc y)
        = do tag 25; toBuf b fc; toBuf b y
    toBuf b (IType fc)
        = do tag 26; toBuf b fc
    toBuf b (IHole fc y)
        = do tag 27; toBuf b fc; toBuf b y
    toBuf b (IUnifyLog fc lvl x) = toBuf b x

    toBuf b (Implicit fc i)
        = do tag 28; toBuf b fc; toBuf b i

    fromBuf b
        = case !getTag of
               0 => do fc <- fromBuf b; n <- fromBuf b;
                       pure (IVar fc n)
               1 => do fc <- fromBuf b;
                       r <- fromBuf b; p <- fromBuf b;
                       n <- fromBuf b
                       argTy <- fromBuf b; retTy <- fromBuf b
                       pure (IPi fc r p n argTy retTy)
               2 => do fc <- fromBuf b;
                       r <- fromBuf b; p <- fromBuf b; n <- fromBuf b
                       argTy <- fromBuf b; scope <- fromBuf b
                       pure (ILam fc r p n argTy scope)
               3 => do fc <- fromBuf b;
                       r <- fromBuf b; n <- fromBuf b
                       nTy <- fromBuf b; nVal <- fromBuf b
                       scope <- fromBuf b
                       pure (ILet fc r n nTy nVal scope)
               4 => do fc <- fromBuf b; y <- fromBuf b;
                       ty <- fromBuf b; xs <- fromBuf b
                       pure (ICase fc y ty xs)
               5 => do fc <- fromBuf b;
                       xs <- fromBuf b; sc <- fromBuf b
                       pure (ILocal fc xs sc)
               6 => do fc <- fromBuf b; fs <- fromBuf b
                       rec <- fromBuf b
                       pure (IUpdate fc fs rec)
               7 => do fc <- fromBuf b; fn <- fromBuf b
                       arg <- fromBuf b
                       pure (IApp fc fn arg)
               8 => do fc <- fromBuf b; fn <- fromBuf b
                       y <- fromBuf b; arg <- fromBuf b
                       pure (IImplicitApp fc fn y arg)
               9 => do fc <- fromBuf b; fn <- fromBuf b
                       arg <- fromBuf b
                       pure (IWithApp fc fn arg)
               10 => do fc <- fromBuf b; depth <- fromBuf b
                        pure (ISearch fc depth)
               11 => do fc <- fromBuf b; y <- fromBuf b
                        xs <- fromBuf b
                        pure (IAlternative fc y xs)
               12 => do fc <- fromBuf b; x <- fromBuf b; y <- fromBuf b
                        pure (IRewrite fc x y)
               13 => do fc <- fromBuf b; y <- fromBuf b
                        pure (ICoerced fc y)
               14 => do fc <- fromBuf b; m <- fromBuf b; y <- fromBuf b
                        pure (IBindHere fc m y)
               15 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IBindVar fc y)
               16 => do fc <- fromBuf b; side <- fromBuf b
                        y <- fromBuf b
                        pattern <- fromBuf b
                        pure (IAs fc side y pattern)
               17 => do fc <- fromBuf b
                        pattern <- fromBuf b
                        pure (IMustUnify fc UnknownDot pattern)

               18 => do fc <- fromBuf b; r <- fromBuf b
                        y <- fromBuf b
                        pure (IDelayed fc r y)
               19 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IDelay fc y)
               20 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IForce fc y)

               21 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IQuote fc y)
               22 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IQuoteDecl fc y)
               23 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IUnquote fc y)
               24 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IRunElab fc y)

               25 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IPrimVal fc y)
               26 => do fc <- fromBuf b
                        pure (IType fc)
               27 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IHole fc y)
               28 => do fc <- fromBuf b
                        i <- fromBuf b
                        pure (Implicit fc i)
               _ => corrupt "RawImp"

  export
  TTC IFieldUpdate where
    toBuf b (ISetField p val)
        = do tag 0; toBuf b p; toBuf b val
    toBuf b (ISetFieldApp p val)
        = do tag 1; toBuf b p; toBuf b val

    fromBuf b
        = case !getTag of
               0 => do p <- fromBuf b; val <- fromBuf b
                       pure (ISetField p val)
               1 => do p <- fromBuf b; val <- fromBuf b
                       pure (ISetFieldApp p val)
               _ => corrupt "IFieldUpdate"

  export
  TTC BindMode where
    toBuf b (PI r) = do tag 0; toBuf b r
    toBuf b PATTERN = tag 1
    toBuf b NONE = tag 2

    fromBuf b
        = case !getTag of
               0 => do x <- fromBuf b
                       pure (PI x)
               1 => pure PATTERN
               2 => pure NONE
               _ => corrupt "BindMode"

  export
  TTC AltType where
    toBuf b FirstSuccess = tag 0
    toBuf b Unique = tag 1
    toBuf b (UniqueDefault x) = do tag 2; toBuf b x

    fromBuf b
        = case !getTag of
               0 => pure FirstSuccess
               1 => pure Unique
               2 => do x <- fromBuf b
                       pure (UniqueDefault x)
               _ => corrupt "AltType"

  export
  TTC ImpTy where
    toBuf b (MkImpTy fc n ty)
        = do toBuf b fc; toBuf b n; toBuf b ty
    fromBuf b
        = do fc <- fromBuf b; n <- fromBuf b; ty <- fromBuf b
             pure (MkImpTy fc n ty)

  export
  TTC ImpClause where
    toBuf b (PatClause fc lhs rhs)
        = do tag 0; toBuf b fc; toBuf b lhs; toBuf b rhs
    toBuf b (ImpossibleClause fc lhs)
        = do tag 1; toBuf b fc; toBuf b lhs
    toBuf b (WithClause fc lhs wval cs)
        = do tag 2; toBuf b fc; toBuf b lhs; toBuf b wval; toBuf b cs

    fromBuf b
        = case !getTag of
               0 => do fc <- fromBuf b; lhs <- fromBuf b;
                       rhs <- fromBuf b
                       pure (PatClause fc lhs rhs)
               1 => do fc <- fromBuf b; lhs <- fromBuf b;
                       pure (ImpossibleClause fc lhs)
               2 => do fc <- fromBuf b; lhs <- fromBuf b;
                       wval <- fromBuf b; cs <- fromBuf b
                       pure (WithClause fc lhs wval cs)
               _ => corrupt "ImpClause"

  export
  TTC DataOpt where
    toBuf b (SearchBy ns)
        = do tag 0; toBuf b ns
    toBuf b NoHints = tag 1
    toBuf b UniqueSearch = tag 2
    toBuf b External = tag 3

    fromBuf b
        = case !getTag of
               0 => do ns <- fromBuf b
                       pure (SearchBy ns)
               1 => pure NoHints
               2 => pure UniqueSearch
               3 => pure External
               _ => corrupt "DataOpt"

  export
  TTC ImpData where
    toBuf b (MkImpData fc n tycon opts cons)
        = do tag 0; toBuf b fc; toBuf b n; toBuf b tycon; toBuf b opts
             toBuf b cons
    toBuf b (MkImpLater fc n tycon)
        = do tag 1; toBuf b fc; toBuf b n; toBuf b tycon

    fromBuf b
        = case !getTag of
               0 => do fc <- fromBuf b; n <- fromBuf b;
                       tycon <- fromBuf b; opts <- fromBuf b
                       cons <- fromBuf b
                       pure (MkImpData fc n tycon opts cons)
               1 => do fc <- fromBuf b; n <- fromBuf b;
                       tycon <- fromBuf b
                       pure (MkImpLater fc n tycon)
               _ => corrupt "ImpData"

  export
  TTC IField where
    toBuf b (MkIField fc c p n ty)
        = do toBuf b fc; toBuf b c; toBuf b p; toBuf b n; toBuf b ty

    fromBuf b
        = do fc <- fromBuf b; c <- fromBuf b; p <- fromBuf b
             n <- fromBuf b; ty <- fromBuf b
             pure (MkIField fc c p n ty)

  export
  TTC ImpRecord where
    toBuf b (MkImpRecord fc n ps con fs)
        = do toBuf b fc; toBuf b n; toBuf b ps; toBuf b con; toBuf b fs

    fromBuf b
        = do fc <- fromBuf b; n <- fromBuf b; ps <- fromBuf b
             con <- fromBuf b; fs <- fromBuf b
             pure (MkImpRecord fc n ps con fs)

  export
  TTC FnOpt where
    toBuf b Inline = tag 0
    toBuf b (Hint t) = do tag 1; toBuf b t
    toBuf b (GlobalHint t) = do tag 2; toBuf b t
    toBuf b ExternFn = tag 3
    toBuf b (ForeignFn cs) = do tag 4; toBuf b cs
    toBuf b Invertible = tag 5
    toBuf b (Totality Total) = tag 6
    toBuf b (Totality CoveringOnly) = tag 7
    toBuf b (Totality PartialOK) = tag 8
    toBuf b Macro = tag 9
    toBuf b (SpecArgs ns) = do tag 10; toBuf b ns

    fromBuf b
        = case !getTag of
               0 => pure Inline
               1 => do t <- fromBuf b; pure (Hint t)
               2 => do t <- fromBuf b; pure (GlobalHint t)
               3 => pure ExternFn
               4 => do cs <- fromBuf b; pure (ForeignFn cs)
               5 => pure Invertible
               6 => pure (Totality Total)
               7 => pure (Totality CoveringOnly)
               8 => pure (Totality PartialOK)
               9 => pure Macro
               10 => do ns <- fromBuf b; pure (SpecArgs ns)
               _ => corrupt "FnOpt"

  export
  TTC ImpDecl where
    toBuf b (IClaim fc c vis xs d)
        = do tag 0; toBuf b fc; toBuf b c; toBuf b vis; toBuf b xs; toBuf b d
    toBuf b (IData fc vis d)
        = do tag 1; toBuf b fc; toBuf b vis; toBuf b d
    toBuf b (IDef fc n xs)
        = do tag 2; toBuf b fc; toBuf b n; toBuf b xs
    toBuf b (IParameters fc vis d)
        = do tag 3; toBuf b fc; toBuf b vis; toBuf b d
    toBuf b (IRecord fc ns vis r)
        = do tag 4; toBuf b fc; toBuf b ns; toBuf b vis; toBuf b r
    toBuf b (INamespace fc xs ds)
        = do tag 5; toBuf b fc; toBuf b xs; toBuf b ds
    toBuf b (ITransform fc lhs rhs)
        = do tag 6; toBuf b fc; toBuf b lhs; toBuf b rhs
    toBuf b (IPragma f) = throw (InternalError "Can't write Pragma")
    toBuf b (ILog n)
        = do tag 7; toBuf b n

    fromBuf b
        = case !getTag of
               0 => do fc <- fromBuf b; c <- fromBuf b
                       vis <- fromBuf b;
                       xs <- fromBuf b; d <- fromBuf b
                       pure (IClaim fc c vis xs d)
               1 => do fc <- fromBuf b; vis <- fromBuf b
                       d <- fromBuf b
                       pure (IData fc vis d)
               2 => do fc <- fromBuf b; n <- fromBuf b
                       xs <- fromBuf b
                       pure (IDef fc n xs)
               3 => do fc <- fromBuf b; vis <- fromBuf b
                       d <- fromBuf b
                       pure (IParameters fc vis d)
               4 => do fc <- fromBuf b; ns <- fromBuf b;
                       vis <- fromBuf b; r <- fromBuf b
                       pure (IRecord fc ns vis r)
               5 => do fc <- fromBuf b; xs <- fromBuf b
                       ds <- fromBuf b
                       pure (INamespace fc xs ds)
               6 => do fc <- fromBuf b; lhs <- fromBuf b; rhs <- fromBuf b
                       pure (ITransform fc lhs rhs)
               7 => do n <- fromBuf b
                       pure (ILog n)
               _ => corrupt "ImpDecl"

