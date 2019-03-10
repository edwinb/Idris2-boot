module TTImp.Parser

import Core.TT
import Parser.Support
import TTImp.TTImp

topDecl : FileName -> IndentInfo -> Rule ImpDecl

atom : FileName -> Rule RawImp
atom fname
    = do start <- location
         x <- constant
         end <- location
         pure (IPrimVal (MkFC fname start end) x)
  <|> do start <- location
         keyword "Type"
         end <- location
         pure (IType (MkFC fname start end))
  <|> do start <- location
         symbol "_"
         end <- location
         pure (Implicit (MkFC fname start end))
  <|> do start <- location
         x <- name
         end <- location
         pure (IVar (MkFC fname start end) x)

visibility : EmptyRule Visibility
visibility
    = do keyword "public"
         keyword "export"
         pure Public
  <|> do keyword "export"
         pure Export
  <|> do keyword "private"
         pure Private
  <|> pure Private

bindSymbol : Rule PiInfo
bindSymbol
    = do symbol "->"
         pure Explicit
  <|> do symbol "=>"
         pure AutoImplicit

mutual
  appExpr : FileName -> IndentInfo -> Rule RawImp
  appExpr fname indents
      = do start <- location
           f <- simpleExpr fname indents
           args <- many (argExpr fname indents)
           end <- location
           pure (applyExpImp start end f args)
    where
      applyExpImp : FilePos -> FilePos ->
                    RawImp -> List (Either RawImp (Maybe Name, RawImp)) ->
                    RawImp
      applyExpImp start end f [] = f
      applyExpImp start end f (Left exp :: args)
          = applyExpImp start end (IApp (MkFC fname start end) f exp) args
      applyExpImp start end f (Right (n, imp) :: args) 
          = applyExpImp start end (IImplicitApp (MkFC fname start end) f n imp) args

  argExpr : FileName -> IndentInfo -> 
            Rule (Either RawImp (Maybe Name, RawImp))
  argExpr fname indents
      = do continue indents
           arg <- simpleExpr fname indents
           pure (Left arg)
    <|> do continue indents
           arg <- implicitArg fname indents
           pure (Right arg)

  implicitArg : FileName -> IndentInfo -> Rule (Maybe Name, RawImp)
  implicitArg fname indents
      = do start <- location
           symbol "{"
           x <- unqualifiedName
           (do symbol "="
               commit
               tm <- expr fname indents
               symbol "}"
               pure (Just (UN x), tm))
             <|> (do symbol "}"
                     end <- location
                     pure (Just (UN x), IVar (MkFC fname start end) (UN x)))
    <|> do symbol "@{"
           commit
           tm <- expr fname indents
           symbol "}"
           pure (Nothing, tm)

  simpleExpr : FileName -> IndentInfo -> Rule RawImp
  simpleExpr fname indents
       = atom fname
     <|> binder fname indents
     <|> do symbol "("
            e <- expr fname indents
            symbol ")"
            pure e

  multiplicity : EmptyRule (Maybe Integer)
  multiplicity
      = do c <- intLit
           pure (Just c)
    <|> pure Nothing

  getMult : Maybe Integer -> EmptyRule RigCount
  getMult (Just 0) = pure Rig0
  getMult (Just 1) = pure Rig1
  getMult Nothing = pure RigW
  getMult _ = fatalError "Invalid multiplicity (must be 0 or 1)"

  pibindAll : FC -> PiInfo -> List (RigCount, Maybe Name, RawImp) -> 
              RawImp -> RawImp
  pibindAll fc p [] scope = scope
  pibindAll fc p ((rig, n, ty) :: rest) scope
           = IPi fc rig p n ty (pibindAll fc p rest scope)

  bindList : FileName -> FilePos -> IndentInfo -> 
             Rule (List (RigCount, Name, RawImp))
  bindList fname start indents
      = sepBy1 (symbol ",")
               (do rigc <- multiplicity
                   n <- unqualifiedName
                   ty <- option 
                            (Implicit (MkFC fname start start))
                            (do symbol ":"
                                appExpr fname indents)
                   rig <- getMult rigc
                   pure (rig, UN n, ty))


  pibindList : FileName -> FilePos -> IndentInfo -> 
               Rule (List (RigCount, Maybe Name, RawImp))
  pibindList fname start indents
       = do rigc <- multiplicity
            ns <- sepBy1 (symbol ",") unqualifiedName
            symbol ":"
            ty <- expr fname indents
            atEnd indents
            rig <- getMult rigc
            pure (map (\n => (rig, Just (UN n), ty)) ns)
     <|> sepBy1 (symbol ",")
                (do rigc <- multiplicity
                    n <- name
                    symbol ":"
                    ty <- expr fname indents
                    rig <- getMult rigc
                    pure (rig, Just n, ty))
      
  autoImplicitPi : FileName -> IndentInfo -> Rule RawImp
  autoImplicitPi fname indents
      = do start <- location
           symbol "{"
           keyword "auto"
           commit
           binders <- pibindList fname start indents
           symbol "}"
           symbol "->"
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) AutoImplicit binders scope)

  forall_ : FileName -> IndentInfo -> Rule RawImp
  forall_ fname indents
      = do start <- location
           keyword "forall"
           commit
           nstart <- location
           ns <- sepBy1 (symbol ",") unqualifiedName
           nend <- location
           let nfc = MkFC fname nstart nend
           let binders = map (\n => (Rig0, Just (UN n), Implicit nfc)) ns
           symbol "."
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) Implicit binders scope)

  implicitPi : FileName -> IndentInfo -> Rule RawImp
  implicitPi fname indents
      = do start <- location
           symbol "{"
           binders <- pibindList fname start indents
           symbol "}"
           symbol "->"
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) Implicit binders scope)

  explicitPi : FileName -> IndentInfo -> Rule RawImp
  explicitPi fname indents
      = do start <- location
           symbol "("
           binders <- pibindList fname start indents
           symbol ")"
           exp <- bindSymbol
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) exp binders scope)

  lam : FileName -> IndentInfo -> Rule RawImp
  lam fname indents
      = do start <- location
           symbol "\\"
           binders <- bindList fname start indents
           symbol "=>"
           mustContinue indents Nothing
           scope <- expr fname indents
           end <- location
           pure (bindAll (MkFC fname start end) binders scope)
     where
       bindAll : FC -> List (RigCount, Name, RawImp) -> RawImp -> RawImp
       bindAll fc [] scope = scope
       bindAll fc ((rig, n, ty) :: rest) scope
           = ILam fc rig Explicit (Just n) ty (bindAll fc rest scope)

  binder : FileName -> IndentInfo -> Rule RawImp
  binder fname indents
      = autoImplicitPi fname indents
    <|> forall_ fname indents
    <|> implicitPi fname indents
    <|> explicitPi fname indents
    <|> lam fname indents

  typeExpr : FileName -> IndentInfo -> Rule RawImp
  typeExpr fname indents
      = do start <- location
           arg <- appExpr fname indents
           (do continue indents
               rest <- some (do exp <- bindSymbol
                                op <- appExpr fname indents
                                pure (exp, op))
               end <- location
               pure (mkPi start end arg rest))
             <|> pure arg
    where
      mkPi : FilePos -> FilePos -> RawImp -> List (PiInfo, RawImp) -> RawImp
      mkPi start end arg [] = arg
      mkPi start end arg ((exp, a) :: as) 
            = IPi (MkFC fname start end) RigW exp Nothing arg 
                  (mkPi start end a as)

  export
  expr : FileName -> IndentInfo -> Rule RawImp
  expr = typeExpr

tyDecl : FileName -> IndentInfo -> Rule ImpTy
tyDecl fname indents
    = do start <- location
         n <- name
         symbol ":"
         ty <- expr fname indents
         end <- location
         atEnd indents
         pure (MkImpTy (MkFC fname start end) n ty)

fnDef : FileName -> IndentInfo -> Rule ImpDecl
fnDef fname indents
    = do start <- location
         n <- name
         symbol "="
         ty <- expr fname indents
         end <- location
         atEnd indents
         pure (IDef (MkFC fname start end) n ty)

dataDecl : FileName -> IndentInfo -> Rule ImpData
dataDecl fname indents
    = do start <- location
         keyword "data"
         n <- name
         symbol ":"
         ty <- expr fname indents
         keyword "where"
         cs <- block (tyDecl fname)
         end <- location
         pure (MkImpData (MkFC fname start end) n ty [] cs)

-- Declared at the top
-- topDecl : FileName -> IndentInfo -> Rule ImpDecl
topDecl fname indents
    = do start <- location
         vis <- visibility
         dat <- dataDecl fname indents
         end <- location
         pure (IData (MkFC fname start end) vis dat)
  <|> do start <- location
         vis <- visibility
         claim <- tyDecl fname indents
         end <- location
         pure (IClaim (MkFC fname start end) RigW vis [] claim)
  <|> fnDef fname indents

export
prog : FileName -> Rule (List ImpDecl)
prog fname
    = nonEmptyBlock (topDecl fname)
