module Compiler.Inline

import Compiler.CompileExpr

import Core.CompileExpr
import Core.Context
import Core.FC
import Core.TT

import Data.Vect
import Data.LengthMatch

%default covering

data EEnv : List Name -> List Name -> Type where
     Nil : EEnv free []
     (::) : CExp free -> EEnv free vars -> EEnv free (x :: vars)

extend : EEnv free vars -> (args : List (CExp free)) -> (args' : List Name) ->
         LengthMatch args args' -> EEnv free (args' ++ vars)
extend env [] [] NilMatch = env
extend env (a :: xs) (n :: ns) (ConsMatch w)
    = a :: extend env xs ns w

Stack : List Name -> Type
Stack vars = List (CExp vars)

unload : Stack vars -> CExp vars -> CExp vars
unload [] e = e
unload (a :: args) e = unload args (CApp (getFC e) e [a])

unloadApp : Nat -> Stack vars -> CExp vars -> CExp vars
unloadApp n args e = unload (drop n args) (CApp (getFC e) e (take n args))

getArity : CDef -> Nat
getArity (MkFun args _) = length args
getArity (MkCon _ arity _) = arity
getArity (MkForeign _ args _) = length args
getArity (MkError _) = 0

takeFromStack : EEnv free vars -> Stack free -> (args : List Name) ->
                Maybe (EEnv free (args ++ vars), Stack free)
takeFromStack env (e :: es) (a :: as)
  = do (env', stk') <- takeFromStack env es as
       pure (e :: env', stk')
takeFromStack env stk [] = pure (env, stk)
takeFromStack env [] args = Nothing

data LVar : Type where

genName : {auto l : Ref LVar Int} ->
          String -> Core Name
genName n
    = do i <- get LVar
         put LVar (i + 1)
         pure (MN n i)

refToLocal : Name -> (x : Name) -> CExp vars -> CExp (x :: vars)
refToLocal x new tm = refsToLocals (Add new x None) tm

mutual
  used : {idx : Nat} -> .(IsVar n idx free) -> CExp free -> Int
  used {idx} n (CLocal _ {idx=pidx} prf) = if idx == pidx then 1 else 0
  used n (CLam _ _ sc) = used (Later n) sc
  used n (CLet _ _ _ val sc) = used n val + used (Later n) sc
  used n (CApp _ x args) = foldr (+) (used n x) (map (used n) args)
  used n (CCon _ _ _ args) = foldr (+) 0 (map (used n) args)
  used n (COp _ _ args) = foldr (+) 0 (map (used n) args)
  used n (CExtPrim _ _ args) = foldr (+) 0 (map (used n) args)
  used n (CForce _ x) = used n x
  used n (CDelay _ x) = used n x
  used n (CConCase fc sc alts def)
     = foldr (+) (used n sc) (map (usedCon n) alts)
          + maybe 0 (used n) def
  used n (CConstCase fc sc alts def)
     = foldr (+) (used n sc) (map (usedConst n) alts)
          + maybe 0 (used n) def
  used _ tm = 0

  usedCon : {idx : Nat} -> .(IsVar n idx free) -> CConAlt free -> Int
  usedCon n (MkConAlt _ _ args sc)
      = let MkVar n' = weakenNs args (MkVar n) in
            used n' sc

  usedConst : {idx : Nat} -> .(IsVar n idx free) -> CConstAlt free -> Int
  usedConst n (MkConstAlt _ sc) = used n sc

mutual
  evalLocal : {auto c : Ref Ctxt Defs} ->
              {auto l : Ref LVar Int} ->
              FC -> List Name -> Stack free ->
              EEnv free vars ->
              {idx : Nat} -> .(IsVar x idx (vars ++ free)) ->
              Core (CExp free)
  evalLocal {vars = []} fc rec stk env p
      = pure $ unload stk (CLocal fc p)
  evalLocal {vars = x :: xs} fc rec stk (v :: env) First
      = case stk of
             [] => pure v
             _ => eval rec env stk (weakenNs xs v)
  evalLocal {vars = x :: xs} fc rec stk (_ :: env) (Later p)
      = evalLocal fc rec stk env p

  tryApply : {auto c : Ref Ctxt Defs} ->
             {auto l : Ref LVar Int} ->
             List Name -> Stack free -> EEnv free vars -> CDef ->
             Core (Maybe (CExp free))
  tryApply {free} {vars} rec stk env (MkFun args exp)
      = do let Just (env', stk') = takeFromStack env stk args
               | Nothing => pure Nothing
           res <- eval rec env' stk'
                     (rewrite sym (appendAssociative args vars free) in
                              embed {vars = vars ++ free} exp)
           pure (Just res)
  tryApply rec stk env _ = pure Nothing

  eval : {auto c : Ref Ctxt Defs} ->
         {auto l : Ref LVar Int} ->
         List Name -> EEnv free vars -> Stack free -> CExp (vars ++ free) ->
         Core (CExp free)
  eval rec env stk (CLocal fc p) = evalLocal fc rec stk env p
  eval rec env stk (CRef fc n)
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact n (gamma defs)
                | Nothing => pure (unload stk (CRef fc n))
           let Just def = compexpr gdef
                | Nothing => pure (unload stk (CRef fc n))
           let arity = getArity def
           if (Inline `elem` flags gdef) && (not (n `elem` rec))
              then do ap <- tryApply (n :: rec) stk env def
                      pure $ maybe (unloadApp arity stk (CRef fc n)) id ap
              else pure $ unloadApp arity stk (CRef fc n)
  eval {vars} {free} rec env [] (CLam fc x sc)
      = do xn <- genName "lamv"
           sc' <- eval rec (CRef fc xn :: env) [] sc
           pure $ CLam fc x (refToLocal xn x sc')
  eval rec env (e :: stk) (CLam fc x sc) = eval rec (e :: env) stk sc
  eval {vars} {free} rec env stk (CLet fc x inl val sc)
      = do let u = used First sc
           xn <- genName "letv"
           sc' <- eval rec (CRef fc xn :: env) [] sc
           if u > 0 || not inl
                then do val' <- eval rec env [] val
                        pure (unload stk $ CLet fc x inl val' (refToLocal xn x sc'))
                else pure sc'
  eval rec env stk (CApp fc f args)
      = eval rec env (!(traverse (eval rec env []) args) ++ stk) f
  eval rec env stk (CCon fc n t args)
      = pure $ unload stk $ CCon fc n t !(traverse (eval rec env []) args)
  eval rec env stk (COp fc p args)
      = pure $ unload stk $ COp fc p !(traverseVect (eval rec env []) args)
  eval rec env stk (CExtPrim fc p args)
      = pure $ unload stk $ CExtPrim fc p !(traverse (eval rec env []) args)
  eval rec env stk (CForce fc e)
      = case !(eval rec env [] e) of
             CDelay _ e' => eval rec [] stk e'
             res => pure $ unload stk (CForce fc res)
  eval rec env stk (CDelay fc e)
      = pure $ unload stk (CDelay fc !(eval rec env [] e))
  eval rec env stk (CConCase fc sc alts def)
      = do sc' <- eval rec env [] sc
           Nothing <- pickAlt rec env stk sc' alts def | Just val => pure val
           def' <- traverseOpt (eval rec env stk) def
           pure $ CConCase fc sc'
                     !(traverse (evalAlt fc rec env stk) alts)
                     def'
  eval rec env stk (CConstCase fc sc alts def)
      = do sc' <- eval rec env [] sc
           Nothing <- pickConstAlt rec env stk sc' alts def | Just val => pure val
           def' <- traverseOpt (eval rec env stk) def
           pure $ CConstCase fc sc'
                         !(traverse (evalConstAlt rec env stk) alts)
                         def'
  eval rec env stk (CPrimVal fc c) = pure $ unload stk $ CPrimVal fc c
  eval rec env stk (CErased fc) = pure $ unload stk $ CErased fc
  eval rec env stk (CCrash fc str) = pure $ unload stk $ CCrash fc str

  extendLoc : {auto l : Ref LVar Int} ->
              FC -> EEnv free vars -> (args' : List Name) ->
              Core (Bounds args', EEnv free (args' ++ vars))
  extendLoc fc env [] = pure (None, env)
  extendLoc fc env (n :: ns)
      = do xn <- genName "cv"
           (bs', env') <- extendLoc fc env ns
           pure (Add n xn bs', CRef fc xn :: env')

  evalAlt : {auto c : Ref Ctxt Defs} ->
            {auto l : Ref LVar Int} ->
            FC -> List Name -> EEnv free vars -> Stack free -> CConAlt (vars ++ free) ->
            Core (CConAlt free)
  evalAlt {free} {vars} fc rec env stk (MkConAlt n t args sc)
      = do (bs, env') <- extendLoc fc env args
           scEval <- eval rec env' stk
                          (rewrite sym (appendAssociative args vars free) in sc)
           pure $ MkConAlt n t args (refsToLocals bs scEval)

  evalConstAlt : {auto c : Ref Ctxt Defs} ->
                 {auto l : Ref LVar Int} ->
                 List Name -> EEnv free vars -> Stack free -> CConstAlt (vars ++ free) ->
                 Core (CConstAlt free)
  evalConstAlt rec env stk (MkConstAlt c sc)
      = MkConstAlt c <$> eval rec env stk sc

  pickAlt : {auto c : Ref Ctxt Defs} ->
            {auto l : Ref LVar Int} ->
            List Name -> EEnv free vars -> Stack free ->
            CExp free -> List (CConAlt (vars ++ free)) ->
            Maybe (CExp (vars ++ free)) ->
            Core (Maybe (CExp free))
  pickAlt rec env stk (CCon fc n t args) [] def
      = traverseOpt (eval rec env stk) def
  pickAlt {vars} {free} rec env stk (CCon fc n t args) (MkConAlt n' t' args' sc :: alts) def
      = if t == t'
           then case checkLengthMatch args args' of
                     Nothing => pure Nothing
                     Just m =>
                         do let env' : EEnv free (args' ++ vars)
                                   = extend env args args' m
                            pure $ Just !(eval rec env' stk
                                    (rewrite sym (appendAssociative args' vars free) in
                                             sc))
           else pickAlt rec env stk (CCon fc n t args) alts def
  pickAlt rec env stk _ _ _ = pure Nothing

  pickConstAlt : {auto c : Ref Ctxt Defs} ->
                 {auto l : Ref LVar Int} ->
                 List Name -> EEnv free vars -> Stack free ->
                 CExp free -> List (CConstAlt (vars ++ free)) ->
                 Maybe (CExp (vars ++ free)) ->
                 Core (Maybe (CExp free))
  pickConstAlt rec env stk (CPrimVal fc c) [] def
      = traverseOpt (eval rec env stk) def
  pickConstAlt {vars} {free} rec env stk (CPrimVal fc c) (MkConstAlt c' sc :: alts) def
      = if c == c'
           then Just <$> eval rec env stk sc
           else pickConstAlt rec env stk (CPrimVal fc c) alts def
  pickConstAlt rec env stk _ _ _ = pure Nothing

-- Inlining may have messed with function arity (e.g. by adding lambdas to
-- the LHS to avoid needlessly making a closure) so fix them up here. This
-- needs to be right because typically back ends need to know whether a
-- name is under- or over-applied
fixArityTm : {auto c : Ref Ctxt Defs} ->
             CExp vars -> List (CExp vars) -> Core (CExp vars)
fixArityTm (CRef fc n) args
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure (unload args (CRef fc n))
         let Just def = compexpr gdef
              | Nothing => pure (unload args (CRef fc n))
         let arity = getArity def
         pure $ expandToArity arity (CApp fc (CRef fc n) []) args
fixArityTm (CLam fc x sc) args
    = pure $ expandToArity Z (CLam fc x !(fixArityTm sc [])) args
fixArityTm (CLet fc x inl val sc) args
    = pure $ expandToArity Z
                 (CLet fc x inl !(fixArityTm val []) !(fixArityTm sc [])) args
fixArityTm (CApp fc f fargs) args
    = fixArityTm f (!(traverse (\tm => fixArityTm tm []) fargs) ++ args)
fixArityTm (CCon fc n t args) []
    = pure $ CCon fc n t !(traverse (\tm => fixArityTm tm []) args)
fixArityTm (COp fc op args) []
    = pure $ COp fc op !(traverseArgs args)
  where
    traverseArgs : Vect n (CExp vs) -> Core (Vect n (CExp vs))
    traverseArgs [] = pure []
    traverseArgs (a :: as) = pure $ !(fixArityTm a []) :: !(traverseArgs as)
fixArityTm (CExtPrim fc p args) []
    = pure $ CExtPrim fc p !(traverse (\tm => fixArityTm tm []) args)
fixArityTm (CForce fc tm) args
    = pure $ expandToArity Z (CForce fc !(fixArityTm tm [])) args
fixArityTm (CDelay fc tm) args
    = pure $ expandToArity Z (CDelay fc !(fixArityTm tm [])) args
fixArityTm (CConCase fc sc alts def) args
    = pure $ expandToArity Z
              (CConCase fc !(fixArityTm sc [])
                           !(traverse fixArityAlt alts)
                           !(traverseOpt (\tm => fixArityTm tm []) def)) args
  where
    fixArityAlt : CConAlt vars -> Core (CConAlt vars)
    fixArityAlt (MkConAlt n t a sc)
        = pure $ MkConAlt n t a !(fixArityTm sc [])
fixArityTm (CConstCase fc sc alts def) args
    = pure $ expandToArity Z
              (CConstCase fc !(fixArityTm sc [])
                             !(traverse fixArityConstAlt alts)
                             !(traverseOpt (\tm => fixArityTm tm []) def)) args
  where
    fixArityConstAlt : CConstAlt vars -> Core (CConstAlt vars)
    fixArityConstAlt (MkConstAlt c sc)
        = pure $ MkConstAlt c !(fixArityTm sc [])
fixArityTm t [] = pure t
fixArityTm t args = pure $ expandToArity Z t args

export
fixArityExp : {auto c : Ref Ctxt Defs} ->
              CExp vars -> Core (CExp vars)
fixArityExp tm = fixArityTm tm []

fixArity : {auto c : Ref Ctxt Defs} ->
           CDef -> Core CDef
fixArity (MkFun args exp) = pure $ MkFun args !(fixArityTm exp [])
fixArity (MkError exp) = pure $ MkError !(fixArityTm exp [])
fixArity d = pure d

getLams : Int -> SubstCEnv done args -> CExp (done ++ args) ->
          (args' ** (SubstCEnv args' args, CExp (args' ++ args)))
getLams {done} i env (CLam fc x sc)
    = getLams {done = x :: done} (i + 1) (CRef fc (MN "ext" i) :: env) sc
getLams {done} i env sc = (done ** (env, sc))

mkBounds : (xs : _) -> Bounds xs
mkBounds [] = None
mkBounds (x :: xs) = Add x x (mkBounds xs)

getNewArgs : SubstCEnv done args -> List Name
getNewArgs [] = []
getNewArgs (CRef _ n :: xs) = n :: getNewArgs xs
getNewArgs {done = x :: xs} (_ :: sub) = x :: getNewArgs sub

-- Move any lambdas in the body of the definition into the lhs list of vars.
-- Annoyingly, the indices will need fixing up because the order in the top
-- level definition goes left to right (i.e. first argument has lowest index,
-- not the highest, as you'd expect if they were all lambdas).
mergeLambdas : (args : List Name) -> CExp args -> (args' ** CExp args')
mergeLambdas args (CLam fc x sc)
    = let (args' ** (env, exp')) = getLams 0 [] (CLam fc x sc)
          expNs = substs env exp'
          newArgs = reverse $ getNewArgs env
          expLocs = mkLocals {later = args} {vars=[]} (mkBounds newArgs)
                             (rewrite appendNilRightNeutral args in expNs) in
          (_ ** expLocs)
mergeLambdas args exp = (args ** exp)

doEval : {auto c : Ref Ctxt Defs} ->
         Name -> CExp args -> Core (CExp args)
doEval n exp
    = do l <- newRef LVar (the Int 0)
         log 10 (show n ++ ": " ++ show exp)
         exp' <- eval [] [] [] exp
         log 10 ("Inlined: " ++ show exp')
         pure exp'

inline : {auto c : Ref Ctxt Defs} ->
         Name -> CDef -> Core CDef
inline n (MkFun args def)
    = pure $ MkFun args !(doEval n def)
inline n d = pure d

-- merge lambdas from expression into top level arguments
mergeLam : {auto c : Ref Ctxt Defs} ->
           CDef -> Core CDef
mergeLam (MkFun args def)
    = do let (args' ** exp') = mergeLambdas args def
         pure $ MkFun args' exp'
mergeLam d = pure d

export
inlineDef : {auto c : Ref Ctxt Defs} ->
            Name -> Core ()
inlineDef n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure ()
         let Just cexpr =  compexpr def             | Nothing => pure ()
         setCompiled n !(inline n cexpr)

export
fixArityDef : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
fixArityDef n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure ()
         let Just cexpr =  compexpr def             | Nothing => pure ()
         setCompiled n !(fixArity cexpr)

export
mergeLamDef : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
mergeLamDef n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure ()
         let Just cexpr =  compexpr def             | Nothing => pure ()
         setCompiled n !(mergeLam cexpr)
