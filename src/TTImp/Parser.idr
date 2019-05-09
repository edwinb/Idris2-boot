module TTImp.Parser

import Core.Context
import Core.Core
import Core.Env
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
         pure (Implicit (MkFC fname start end) True)
  <|> do start <- location
         symbol "?"
         end <- location
         pure (Implicit (MkFC fname start end) False)
  <|> do start <- location
         symbol "%"
         exactIdent "search"
         end <- location
         pure (ISearch (MkFC fname start end) 1000)
  <|> do start <- location
         x <- name
         end <- location
         pure (IVar (MkFC fname start end) x)
  <|> do start <- location
         symbol "$"
         x <- unqualifiedName
         end <- location
         pure (IBindVar (MkFC fname start end) x)

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

  as : FileName -> IndentInfo -> Rule RawImp
  as fname indents
      = do start <- location
           x <- unqualifiedName
           symbol "@"
           pat <- simpleExpr fname indents
           end <- location
           pure (IAs (MkFC fname start end) (UN x) pat)

  simpleExpr : FileName -> IndentInfo -> Rule RawImp
  simpleExpr fname indents
      = as fname indents
    <|> atom fname
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
                            (Implicit (MkFC fname start start) False)
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
           let binders = map (\n => (Rig0, Just (UN n), Implicit nfc False)) ns
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

parseRHS : FileName -> IndentInfo -> (Int, Int) -> RawImp -> Rule ImpDecl
parseRHS fname indents start lhs
    = do symbol "="
         commit
         rhs <- expr fname indents
         atEnd indents
         fn <- getFn lhs
         end <- location
         let fc = MkFC fname start end
         pure (IDef fc fn [PatClause fc lhs rhs])
  <|> do keyword "impossible"
         atEnd indents
         fn <- getFn lhs
         end <- location
         let fc = MkFC fname start end
         pure (IDef fc fn [ImpossibleClause fc lhs])
  where
    getFn : RawImp -> EmptyRule Name
    getFn (IVar _ n) = pure n
    getFn (IApp _ f a) = getFn f
    getFn (IImplicitApp _ f _ a) = getFn f
    getFn _ = fail "Not a function application" 


clause : FileName -> IndentInfo -> Rule ImpDecl
clause fname indents
    = do start <- location
         lhs <- expr fname indents
         parseRHS fname indents start lhs

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

namespaceDecl : Rule (List String)
namespaceDecl
    = do keyword "namespace"
         commit
         ns <- namespace_
         pure ns

directive : FileName -> IndentInfo -> Rule ImpDecl
directive fname indents
    = do exactIdent "logging"
         lvl <- intLit
         atEnd indents
         pure (ILog (cast lvl))
  <|> do exactIdent "pair"
         start <- location
         p <- name
         f <- name
         s <- name
         end <- location
         let fc = MkFC fname start end
         pure (IPragma (\c, env => setPair {c} fc p f s))

-- Declared at the top
-- topDecl : FileName -> IndentInfo -> Rule ImpDecl
topDecl fname indents
    = do start <- location
         vis <- visibility
         dat <- dataDecl fname indents
         end <- location
         pure (IData (MkFC fname start end) vis dat)
  <|> do start <- location
         ns <- namespaceDecl
         ds <- assert_total (nonEmptyBlock (topDecl fname))
         end <- location
         pure (INamespace (MkFC fname start end) ns ds)
  <|> do start <- location
         vis <- visibility
         claim <- tyDecl fname indents
         end <- location
         pure (IClaim (MkFC fname start end) RigW vis [] claim)
  <|> do symbol "%"; commit
         directive fname indents
  <|> clause fname indents

-- All the clauses get parsed as one-clause definitions. Collect any
-- neighbouring clauses with the same function name into one definition.
export
collectDefs : List ImpDecl -> List ImpDecl
collectDefs [] = []
collectDefs (IDef loc fn cs :: ds)
    = let (cs', rest) = spanMap (isClause fn) ds in
          IDef loc fn (cs ++ cs') :: assert_total (collectDefs rest)
  where
    spanMap : (a -> Maybe (List b)) -> List a -> (List b, List a)
    spanMap f [] = ([], [])
    spanMap f (x :: xs) = case f x of
                               Nothing => ([], x :: xs)
                               Just y => case spanMap f xs of
                                              (ys, zs) => (y ++ ys, zs)

    isClause : Name -> ImpDecl -> Maybe (List ImpClause)
    isClause n (IDef _ n' cs) 
        = if n == n' then Just cs else Nothing
    isClause n _ = Nothing
collectDefs (INamespace loc ns nds :: ds)
    = INamespace loc ns (collectDefs nds) :: collectDefs ds
collectDefs (d :: ds)
    = d :: collectDefs ds

-- full programs
export
prog : FileName -> Rule (List ImpDecl)
prog fname
    = do ds <- nonEmptyBlock (topDecl fname)
         pure (collectDefs ds)

-- TTImp REPL commands
export
command : Rule ImpREPL
command
    = do symbol ":"; exactIdent "t"
         tm <- expr "(repl)" init
         pure (Check tm)
  <|> do symbol ":"; exactIdent "s"
         n <- name
         pure (ProofSearch n)
  <|> do symbol ":"; exactIdent "di"
         n <- name
         pure (DebugInfo n)
  <|> do symbol ":"; exactIdent "q"
         pure Quit
  <|> do tm <- expr "(repl)" init
         pure (Eval tm)
