module Compiler.Inline

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

weakenEnv : EEnv free vars -> EEnv (x :: free) vars
weakenEnv [] = []
weakenEnv (e :: env) = weaken e :: weakenEnv env

weakenNsEnv : (xs : List Name) -> EEnv free vars -> EEnv (xs ++ free) vars
weakenNsEnv [] env = env
weakenNsEnv (x :: xs) env = weakenEnv (weakenNsEnv xs env)

extend : EEnv free vars -> (args : List (CExp free)) -> (args' : List Name) ->
         LengthMatch args args' -> EEnv free (args' ++ vars)
extend env [] [] NilMatch = env
extend env (a :: xs) (n :: ns) (ConsMatch w)
    = a :: extend env xs ns w

extendLoc : FC -> EEnv free vars -> (args' : List Name) ->
            EEnv (args' ++ free) (args' ++ vars)
extendLoc fc env [] = env
extendLoc fc env (n :: ns)
    = CLocal fc First :: weakenEnv (extendLoc fc env ns)

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

mkPrf : (later : List Name) -> Var (later ++ x :: vars)
mkPrf [] = MkVar First
mkPrf {x} {vars} (n :: ns)
    = let MkVar p' = mkPrf {x} {vars} ns in
          MkVar (Later p')

mutual
  mkLocal : {later, vars : _} ->
            Name -> (x : Name) ->
            CExp (later ++ vars) -> CExp (later ++ (x :: vars))
  mkLocal old new (CLocal {idx} {x} fc p)
      = let MkNVar p' = insertNVar {n=new} idx p in CLocal {x} fc p'
  mkLocal {later} {vars} old new (CRef fc var)
      = if var == old
           then let MkVar p' = mkPrf {x=new} {vars} later in
                    CLocal fc p'
           else CRef fc var
  mkLocal {later} {vars} old new (CLam fc x sc)
      = let sc' = mkLocal old new {later = x :: later} {vars} sc in
            CLam fc x sc'
  mkLocal {later} {vars} old new (CLet fc x val sc)
      = let sc' = mkLocal old new {later = x :: later} {vars} sc in
            CLet fc x (mkLocal old new val) sc'
  mkLocal old new (CApp fc f xs)
      = CApp fc (mkLocal old new f) (assert_total (map (mkLocal old new) xs))
  mkLocal old new (CCon fc x tag xs)
      = CCon fc x tag (assert_total (map (mkLocal old new) xs))
  mkLocal old new (COp fc x xs)
      = COp fc x (assert_total (map (mkLocal old new) xs))
  mkLocal old new (CExtPrim fc x xs)
      = CExtPrim fc x (assert_total (map (mkLocal old new) xs))
  mkLocal old new (CForce fc x)
      = CForce fc (mkLocal old new x)
  mkLocal old new (CDelay fc x)
      = CDelay fc (mkLocal old new x)
  mkLocal old new (CConCase fc sc xs def)
      = CConCase fc (mkLocal old new sc)
                 (assert_total (map (mkLocalConAlt old new) xs))
                 (assert_total (map (mkLocal old new) def))
  mkLocal old new (CConstCase fc sc xs def)
      = CConstCase fc (mkLocal old new sc)
                 (assert_total (map (mkLocalConstAlt old new) xs))
                 (assert_total (map (mkLocal old new) def))
  mkLocal old new (CPrimVal fc x) = CPrimVal fc x
  mkLocal old new (CErased fc) = CErased fc
  mkLocal old new (CCrash fc x) = CCrash fc x

  mkLocalConAlt : Name -> (x : Name) ->
                  CConAlt (later ++ vars) -> CConAlt (later ++ x :: vars)
  mkLocalConAlt {later} {vars} old new (MkConAlt x tag args sc)
        = let sc' : CExp ((args ++ later) ++ vars)
                  = rewrite sym (appendAssociative args later vars) in sc in
              MkConAlt x tag args
               (rewrite appendAssociative args later (new :: vars) in
                        mkLocal old new sc')

  mkLocalConstAlt : Name -> (x : Name) ->
                    CConstAlt (later ++ vars) -> CConstAlt (later ++ x :: vars)
  mkLocalConstAlt old new (MkConstAlt x sc) = MkConstAlt x (mkLocal old new sc)

refToLocal : Name -> (x : Name) -> CExp vars -> CExp (x :: vars)
refToLocal old new tm = mkLocal {later = []} old new tm

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
              then do ap <-  tryApply (n :: rec) stk env def
                      pure $ maybe (unloadApp arity stk (CRef fc n)) id ap
              else pure $ unloadApp arity stk (CRef fc n)
  eval {vars} {free} rec env [] (CLam fc x sc)
      = do xn <- genName "lamv"
           sc' <- eval rec (CRef fc xn :: env) [] sc
           pure $ CLam fc x (refToLocal xn x sc')
  eval rec env (e :: stk) (CLam fc x sc) = eval rec (e :: env) stk sc
  eval {vars} {free} rec env stk (CLet fc x val sc)
      = do xn <- genName "letv"
           sc' <- eval rec (CRef fc xn :: env) [] sc
           pure $ unload stk $ CLet fc x !(eval rec env [] val)
                                         (refToLocal xn x sc')
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

  evalAlt : {auto c : Ref Ctxt Defs} ->
            {auto l : Ref LVar Int} ->
            FC -> List Name -> EEnv free vars -> Stack free -> CConAlt (vars ++ free) ->
            Core (CConAlt free)
  evalAlt {free} {vars} fc rec env stk (MkConAlt n t args sc)
      = do let sc' = insertNames {outer=args ++ vars} {inner=free} args
                        (rewrite sym (appendAssociative args vars free) in sc)
           scEval <- eval rec (extendLoc fc env args) (map (weakenNs args) stk) sc'
           pure $ MkConAlt n t args scEval

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

inline : {auto c : Ref Ctxt Defs} ->
         CDef -> Core CDef
inline (MkFun args exp)
    = do l <- newRef LVar (the Int 0)
         MkFun args <$> eval [] [] [] exp
inline d = pure d

export
inlineDef : {auto c : Ref Ctxt Defs} ->
            Name -> Core ()
inlineDef n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure ()
         let Just cexpr =  compexpr def             | Nothing => pure ()
         setCompiled n !(inline cexpr)

