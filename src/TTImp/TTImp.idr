module TTImp.TTImp

import Core.TT

mutual
  public export
  data RawImp : Type where
       IVar : FC -> Name -> RawImp
       IPi : FC -> RigCount -> PiInfo -> Maybe Name ->
             (argTy : RawImp) -> (retTy : RawImp) -> RawImp
       ILam : FC -> RigCount -> PiInfo -> Maybe Name ->
              (argTy : RawImp) -> (lamTy : RawImp) -> RawImp
       IApp : FC -> RawImp -> RawImp -> RawImp
       IImplicitApp : FC -> RawImp -> Maybe Name -> RawImp -> RawImp

       IPrimVal : FC -> (c : Constant) -> RawImp
       IType : FC -> RawImp
       Implicit : FC -> RawImp

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
      show (IPrimVal fc c) = show c
      show (IType fc) = "%type"
      show (Implicit fc) = "_"

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

  public export
  data ImpDecl : Type where
       IClaim : FC -> RigCount -> Visibility -> List FnOpt ->
                ImpTy -> ImpDecl
       IData : FC -> Visibility -> ImpData -> ImpDecl
       IDef : FC -> Name -> RawImp -> ImpDecl
