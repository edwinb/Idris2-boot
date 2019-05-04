module TTImp.TTImp

import Core.Context
import Core.Env
import Core.TT

mutual
  public export
  data BindMode = PI RigCount | PATTERN | NONE

  public export
  data RawImp : Type where
       IVar : FC -> Name -> RawImp
       IPi : FC -> RigCount -> PiInfo -> Maybe Name ->
             (argTy : RawImp) -> (retTy : RawImp) -> RawImp
       ILam : FC -> RigCount -> PiInfo -> Maybe Name ->
              (argTy : RawImp) -> (lamTy : RawImp) -> RawImp
       IApp : FC -> RawImp -> RawImp -> RawImp
       IImplicitApp : FC -> RawImp -> Maybe Name -> RawImp -> RawImp

       -- Any implicit bindings in the scope should be bound here, using
       -- the given binder
       IBindHere : FC -> BindMode -> RawImp -> RawImp
       -- A name which should be implicitly bound
       IBindVar : FC -> String -> RawImp
       -- An 'as' pattern, valid on the LHS of a clause only
       IAs : FC -> Name -> RawImp -> RawImp
       -- A 'dot' pattern, i.e. one which must also have the given value
       -- by unification
       IMustUnify : FC -> (reason : String) -> RawImp -> RawImp

       IPrimVal : FC -> (c : Constant) -> RawImp
       IType : FC -> RawImp

       -- An implicit value, solved by unification, but which will also be
       -- bound (either as a pattern variable or a type variable) if unsolved
       -- at the end of elaborator                                                                     
       Implicit : FC -> (bindIfUnsolved : Bool) -> RawImp

  export
    Show RawImp where
      show (IVar fc n) = show n
      show (IPi fc c p n arg ret)
         = "(%pi " ++ show c ++ " " ++ show p ++
           " " ++ show n ++ " " ++ show arg ++ " " ++ show ret ++ ")"
      show (ILam fc c p n arg sc)
         = "(%lam " ++ show c ++ " " ++ show p ++
           " " ++ show n ++ " " ++ show arg ++ " " ++ show sc ++ ")"
      show (IApp fc f a)
         = "(" ++ show f ++ " " ++ show a ++ ")"
      show (IImplicitApp fc f n a)
         = "(" ++ show f ++ " [" ++ show n ++ " = " ++ show a ++ "])"
      show (IBindHere fc b sc)
         = "(%bindhere " ++ show sc ++ ")"
      show (IBindVar fc n) = "$" ++ n
      show (IAs fc n tm) = show n ++ "@(" ++ show tm ++ ")"
      show (IMustUnify fc r tm) = ".(" ++ show tm ++ ")"
      show (IPrimVal fc c) = show c
      show (IType fc) = "%type"
      show (Implicit fc True) = "_"
      show (Implicit fc False) = "?"

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
       IPragma : ({vars : _} -> Ref Ctxt Defs -> Env Term vars -> Core ()) -> 
                 ImpDecl
       ILog : Nat -> ImpDecl

  export
  Show ImpDecl where
    show (IClaim _ _ _ _ ty) = show ty
    show (IData _ _ d) = show d
    show (IDef _ n cs) = "(%def " ++ show n ++ " " ++ show cs ++ ")"

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
                 RawImp -> Core RawImp
lhsInCurrentNS (IApp loc f a)
    = do f' <- lhsInCurrentNS f
         pure (IApp loc f' a)
lhsInCurrentNS (IImplicitApp loc f n a)
    = do f' <- lhsInCurrentNS f
         pure (IImplicitApp loc f' n a)
lhsInCurrentNS tm@(IVar loc (NS _ _)) = pure tm -- leave explicit NS alone
lhsInCurrentNS (IVar loc n)
       = do n' <- inCurrentNS n
            pure (IVar loc n')
--     = case lookup n (names nest) of
--            Nothing =>
--               do n' <- inCurrentNS n
--                  pure (IVar loc n')
--            -- If it's one of the names in the current nested block, we'll
--            -- be rewriting it during elaboration to be in the scope of the
--            -- parent name.
--            Just _ => pure (IVar loc n)
lhsInCurrentNS tm = pure tm
