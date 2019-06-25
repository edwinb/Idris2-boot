module Compiler.CompileExpr

import Core.CaseTree
import public Core.CompileExpr
import Core.Context
import Core.Env
import Core.Name
import Core.TT

import Data.NameMap
import Data.Vect

%default covering

-- Calculate tags for type constructors from all of the modules - they need
-- to be globally unique so we don't do this until just before compilation,
-- which is when we know how many we have
public export
NameTags : Type
NameTags = NameMap Int

||| Extract the number of arguments from a term
numArgs : Defs -> Term vars -> Core Nat
numArgs defs (Ref _ (DataCon tag arity) n) = pure arity
numArgs defs (Ref _ (TyCon tag arity) n) = pure arity
numArgs defs (Ref _ _ n)
    = case !(lookupDefExact n (gamma defs)) of
           Just (PMDef args _ _ _) => pure (length args)
           Just (ExternDef arity) => pure arity
           Just (Builtin {arity} f) => pure arity
           _ => pure 0
numArgs _ tm = pure 0

weakenVar : Var ns -> Var (a :: ns)
weakenVar (MkVar p) = (MkVar (Later p))

etaExpand : Int -> Nat -> CExp vars -> List (Var vars) -> CExp vars
etaExpand i Z exp args = mkApp exp (map (mkLocal (getFC exp)) (reverse args))
  where
    mkLocal : FC -> (Var vars) -> CExp vars
    mkLocal fc (MkVar p) = CLocal fc p

    mkApp : CExp vars -> List (CExp vars) -> CExp vars
    mkApp tm [] = tm
    mkApp (CApp fc f args) args' = CApp fc f (args ++ args')
    mkApp (CCon fc n t args) args' = CCon fc n t (args ++ args')
    mkApp (CExtPrim fc p args) args' = CExtPrim fc p (args ++ args')
    mkApp tm args = CApp (getFC tm) tm args
etaExpand i (S k) exp args
    = CLam (getFC exp) (MN "x" i) 
             (etaExpand (i + 1) k (weaken exp)
                  (MkVar First :: map weakenVar args))

expandToArity : Nat -> CExp vars -> List (CExp vars) -> CExp vars
-- No point in applying to anything
expandToArity _ (CErased fc) _ = CErased fc
-- Overapplied; apply everything as single arguments
expandToArity Z fn args = applyAll fn args
  where
    applyAll : CExp vars -> List (CExp vars) -> CExp vars
    applyAll fn [] = fn
    applyAll fn (a :: args) = applyAll (CApp (getFC fn) fn [a]) args
expandToArity (S k) fn (a :: args) = expandToArity k (addArg fn a) args
  where
    addArg : CExp vars -> CExp vars -> CExp vars
    addArg (CApp fc fn args) a = CApp fc fn (args ++ [a])
    addArg (CCon fc n tag args) a = CCon fc n tag (args ++ [a])
    addArg (CExtPrim fc p args) a = CExtPrim fc p (args ++ [a])
    addArg f a = CApp (getFC f) f [a]
-- Underapplied, saturate with lambdas
expandToArity num fn [] = etaExpand 0 num fn []

-- Rewrite applications of Nat constructors and functions to more optimal
-- versions using Integer

-- None of these should be hard coded, but we'll do it this way until we
-- have a more general approach to optimising data types!
natHack : CExp vars -> CExp vars
natHack (CCon fc (NS ["Prelude"] (UN "Z")) _ []) = CPrimVal fc (BI 0)
natHack (CCon fc (NS ["Prelude"] (UN "S")) _ [k])
    = CApp fc (CRef fc (UN "prim__add_Integer")) [CPrimVal fc (BI 1), k]
natHack (CApp fc (CRef _ (NS ["Prelude"] (UN "natToInteger"))) [k]) = k
natHack (CApp fc (CRef _ (NS ["Prelude"] (UN "integerToNat"))) [k]) = k
natHack (CApp fc (CRef fc' (NS ["Prelude"] (UN "plus"))) args)
    = CApp fc (CRef fc' (UN "prim__add_Integer")) args
natHack (CApp fc (CRef fc' (NS ["Prelude"] (UN "mult"))) args)
    = CApp fc (CRef fc' (UN "prim__mul_Integer")) args
natHack (CApp fc (CRef fc' (NS ["Nat", "Data"] (UN "minus"))) args)
    = CApp fc (CRef fc' (UN "prim__sub_Integer")) args
natHack t = t

isNatCon : Name -> Bool
isNatCon (NS ["Prelude"] (UN "Z")) = True
isNatCon (NS ["Prelude"] (UN "S")) = True
isNatCon _ = False

natBranch : CConAlt vars -> Bool
natBranch (MkConAlt n _ _ _) = isNatCon n

trySBranch : CExp vars -> CConAlt vars -> Maybe (CExp vars)
trySBranch n (MkConAlt (NS ["Prelude"] (UN "S")) _ [arg] sc)
    = let fc = getFC n in
          Just (CLet fc arg (CApp fc (CRef fc (UN "prim__sub_Integer")) 
                    [n, CPrimVal fc (BI 1)]) sc)
trySBranch _ _ = Nothing

tryZBranch : CConAlt vars -> Maybe (CExp vars)
tryZBranch (MkConAlt (NS ["Prelude"] (UN "Z")) _ [] sc) = Just sc
tryZBranch _ = Nothing

getSBranch : CExp vars -> List (CConAlt vars) -> Maybe (CExp vars)
getSBranch n [] = Nothing
getSBranch n (x :: xs) = trySBranch n x <+> getSBranch n xs

getZBranch : List (CConAlt vars) -> Maybe (CExp vars)
getZBranch [] = Nothing
getZBranch (x :: xs) = tryZBranch x <+> getZBranch xs

-- Rewrite case trees on Nat to be case trees on Integer
natHackTree : CExp vars -> CExp vars
natHackTree (CConCase fc sc alts def)
   = if any natBranch alts
        then let def' = maybe def Just (getSBranch sc alts) in
                 case getZBranch alts of
                      Nothing => maybe (CCrash fc "No branches") id def'
                      Just zalt => CConstCase fc sc [MkConstAlt (BI 0) zalt] def'
        else CConCase fc sc alts def
natHackTree t = t

mutual
  toCExpTm : {auto c : Ref Ctxt Defs} ->
             NameTags -> Name -> Term vars -> Core (CExp vars)
  toCExpTm tags n (Local fc _ _ prf) 
      = pure $ CLocal fc prf
  toCExpTm tags n (Ref fc (DataCon tag arity) fn) 
      = let tag' = case lookup fn tags of
                        Just t => t
                        _ => tag in
            -- get full name for readability, and the Nat hack
            pure $ CCon fc !(getFullName fn) tag' []
  toCExpTm tags n (Ref fc (TyCon tag arity) fn)
      = let tag' = case lookup fn tags of
                        Just t => t
                        _ => tag in
            pure $ CCon fc fn tag' []
  toCExpTm tags n (Ref fc _ fn) 
      = do full <- getFullName fn 
               -- ^ For readability of output code, and the Nat hack, 
           pure $ CApp fc (CRef fc full) []
  toCExpTm tags n (Meta fc mn i args)
      = pure $ CApp fc (CRef fc mn) !(traverse (toCExp tags n) args)
  toCExpTm tags n (Bind fc x (Lam _ _ _) sc)
      = pure $ CLam fc x !(toCExp tags n sc)
  toCExpTm tags n (Bind fc x (Let Rig0 val _) sc)
      = pure $ CLet fc x (CErased fc) !(toCExp tags n sc)
  toCExpTm tags n (Bind fc x (Let _ val _) sc)
      = pure $ CLet fc x !(toCExp tags n val) !(toCExp tags n sc)
  toCExpTm tags n (Bind fc x (Pi c e ty) sc) 
      = pure $ CCon fc (UN "->") 1 [!(toCExp tags n ty),
                                    CLam fc x !(toCExp tags n sc)]
  toCExpTm tags n (Bind fc x b tm) = pure $ CErased fc
  -- We'd expect this to have been dealt with in toCExp, but for completeness...
  toCExpTm tags n (App fc tm arg) 
      = pure $ CApp fc !(toCExp tags n tm) [!(toCExp tags n arg)]
  -- This shouldn't be in terms any more, but here for completeness
  toCExpTm tags n (As _ _ p) = toCExpTm tags n p
  -- TODO: Either make sure 'Delayed' is always Rig0, or add to typecase
  toCExpTm tags n (TDelayed fc _ _) = pure $ CErased fc
  toCExpTm tags n (TDelay fc _ _ arg)
      = pure (CDelay fc !(toCExp tags n arg))
  toCExpTm tags n (TForce fc arg)
      = pure (CForce fc !(toCExp tags n arg))
  toCExpTm tags n (PrimVal fc c) 
      = let t = constTag c in
            if t == 0
               then pure $ CPrimVal fc c
               else pure $ CCon fc (UN (show c)) t []
  toCExpTm tags n (Erased fc) = pure $ CErased fc
  toCExpTm tags n (TType fc) = pure $ CCon fc (UN "Type") 2 []

  toCExp : {auto c : Ref Ctxt Defs} ->
           NameTags -> Name -> Term vars -> Core (CExp vars)
  toCExp tags n tm
      = case getFnArgs tm of
             (f, args) =>
                do args' <- traverse (toCExp tags n) args
                   defs <- get Ctxt
                   let res = expandToArity !(numArgs defs f)
                                           !(toCExpTm tags n f) args'
                   pure $ natHack res

mutual
  conCases : {auto c : Ref Ctxt Defs} ->
             NameTags -> Name -> List (CaseAlt vars) -> 
             Core (List (CConAlt vars))
  conCases tags n [] = pure []
  conCases tags n (ConCase x tag args sc :: ns)
      = do let tag' = case lookup x tags of
                           Just t => t
                           _ => tag
           xn <- getFullName x
           pure $ MkConAlt xn tag' args !(toCExpTree tags n sc) 
                     :: !(conCases tags n ns)
  conCases tags n (_ :: ns) = conCases tags n ns

  constCases : {auto c : Ref Ctxt Defs} ->
               NameTags -> Name -> List (CaseAlt vars) -> 
               Core (List (CConstAlt vars))
  constCases tags n [] = pure []
  constCases tags n (ConstCase x sc :: ns)
      = pure $ MkConstAlt x !(toCExpTree tags n sc) :: 
                    !(constCases tags n ns)
  constCases tags n (_ :: ns) = constCases tags n ns

  getDef : {auto c : Ref Ctxt Defs} ->
           NameTags -> Name -> List (CaseAlt vars) -> 
           Core (Maybe (CExp vars))
  getDef tags n [] = pure Nothing
  getDef tags n (DefaultCase sc :: ns) 
      = pure $ Just !(toCExpTree tags n sc)
  getDef tags n (_ :: ns) = getDef tags n ns

  toCExpTree : {auto c : Ref Ctxt Defs} ->
               NameTags -> Name -> CaseTree vars -> 
               Core (CExp vars)
  toCExpTree tags n alts@(Case _ x scTy (DelayCase ty arg sc :: rest))
      = let fc = getLoc scTy in
            pure $ 
              CLet fc arg (CForce fc (CLocal (getLoc scTy) x)) $
              CLet fc ty (CErased fc)
                   !(toCExpTree tags n sc)
  toCExpTree tags n alts = toCExpTree' tags n alts

  toCExpTree' : {auto c : Ref Ctxt Defs} ->
                NameTags -> Name -> CaseTree vars -> 
                Core (CExp vars)
  toCExpTree' tags n (Case _ x scTy alts@(ConCase _ _ _ _ :: _)) 
      = let fc = getLoc scTy in
            pure $ natHackTree 
             (CConCase fc (CLocal fc x) !(conCases tags n alts) 
                                        !(getDef tags n alts))
  toCExpTree' tags n (Case _ x scTy alts@(DelayCase _ _ _ :: _))
      = throw (InternalError "Unexpected DelayCase")
  toCExpTree' tags n (Case _ x scTy alts@(ConstCase _ _ :: _)) 
      = let fc = getLoc scTy in
            pure $ CConstCase fc (CLocal fc x) 
                !(constCases tags n alts) !(getDef tags n alts)
  toCExpTree' tags n (Case _ x scTy alts@(DefaultCase sc :: _)) 
      = toCExpTree tags n sc
  toCExpTree' tags n (Case _ x scTy []) 
      = pure $ CCrash (getLoc scTy) $ "Missing case tree in " ++ show n
  toCExpTree' tags n (STerm tm) = toCExp tags n tm
  toCExpTree' tags n (Unmatched msg) 
      = pure $ CCrash emptyFC msg 
  toCExpTree' tags n Impossible 
      = pure $ CCrash emptyFC ("Impossible case encountered in " ++ show n)

-- Need this for ensuring that argument list matches up to operator arity for
-- builtins
data ArgList : Nat -> List Name -> Type where
     NoArgs : ArgList Z []
     ConsArg : (a : Name) -> ArgList k as -> ArgList (S k) (a :: as)

mkArgList : Int -> (n : Nat) -> (ns ** ArgList n ns)
mkArgList i Z = (_ ** NoArgs)
mkArgList i (S k)
    = let (_ ** rec) = mkArgList (i + 1) k in
          (_ ** ConsArg (MN "arg" i) rec)

toCDef : {auto c : Ref Ctxt Defs} -> 
         NameTags -> Name -> Def -> 
         Core CDef
toCDef tags n None
    = pure $ MkError $ CCrash emptyFC ("Encountered undefined name " ++ show !(getFullName n))
toCDef tags n (PMDef args _ tree _)
    = pure $ MkFun _ !(toCExpTree tags n tree)
toCDef tags n (ExternDef arity)
    = let (ns ** args) = mkArgList 0 arity in
          pure $ MkFun _ (CExtPrim emptyFC !(getFullName n) (map toArgExp (getVars args)))
  where
    toArgExp : (Var ns) -> CExp ns
    toArgExp (MkVar p) = CLocal emptyFC p

    getVars : ArgList k ns -> List (Var ns)
    getVars NoArgs = []
    getVars (ConsArg a rest) = MkVar First :: map weakenVar (getVars rest)
toCDef tags n (Builtin {arity} op)
    = let (ns ** args) = mkArgList 0 arity in
          pure $ MkFun _ (COp emptyFC op (map toArgExp (getVars args)))
  where
    toArgExp : (Var ns) -> CExp ns
    toArgExp (MkVar p) = CLocal emptyFC p

    getVars : ArgList k ns -> Vect k (Var ns)
    getVars NoArgs = []
    getVars (ConsArg a rest) = MkVar First :: map weakenVar (getVars rest)
toCDef tags n (DCon tag arity)
    = case lookup n tags of
           Just t => pure $ MkCon t arity
           _ => pure $ MkCon tag arity
toCDef tags n (TCon tag arity _ _ _ _)
    = case lookup n tags of
           Just t => pure $ MkCon t arity
           _ => pure $ MkCon tag arity
-- We do want to be able to compile these, but also report an error at run time
-- (and, TODO: warn at compile time)
toCDef tags n (Hole _ _)
    = pure $ MkError $ CCrash emptyFC ("Encountered unimplemented hole " ++ show n)
toCDef tags n (Guess _ _)
    = pure $ MkError $ CCrash emptyFC ("Encountered constrained hole " ++ show n)
toCDef tags n (BySearch _ _ _)
    = pure $ MkError $ CCrash emptyFC ("Encountered incomplete proof search " ++ show n)
toCDef tags n def
    = pure $ MkError $ CCrash emptyFC ("Encountered uncompilable name " ++ show (n, def))

export
compileExp : {auto c : Ref Ctxt Defs} -> 
             NameTags -> ClosedTerm -> Core (CExp [])
compileExp tags tm
    = toCExp tags (UN "main") tm

||| Given a name, look up an expression, and compile it to a CExp in the environment
export
compileDef : {auto c : Ref Ctxt Defs} -> NameTags -> Name -> Core ()
compileDef tags n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (InternalError ("Trying to compile unknown name " ++ show n))
         ce <- toCDef tags n (definition gdef)
         setCompiled n ce
