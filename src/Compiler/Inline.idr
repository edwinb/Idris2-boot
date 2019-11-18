module Compiler.Inline

import Core.CompileExpr
import Core.Context
import Core.FC
import Core.TT

import Data.Vect

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

-- TODO: This is in CaseBuilder too, so tidy it up...
data LengthMatch : List a -> List b -> Type where
     NilMatch : LengthMatch [] []
     ConsMatch : LengthMatch xs ys -> LengthMatch (x :: xs) (y :: ys)

checkLengthMatch : (xs : List a) -> (ys : List b) -> Maybe (LengthMatch xs ys)
checkLengthMatch [] [] = Just NilMatch
checkLengthMatch [] (x :: xs) = Nothing
checkLengthMatch (x :: xs) [] = Nothing
checkLengthMatch (x :: xs) (y :: ys)
    = Just (ConsMatch !(checkLengthMatch xs ys))

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
getArity (MkCon _ arity) = arity
getArity (MkForeign _ args _) = length args
getArity (MkError _) = 0

takeFromStack : EEnv free vars -> Stack free -> (args : List Name) ->
                Maybe (EEnv free (args ++ vars), Stack free)
takeFromStack env (e :: es) (a :: as)
  = do (env', stk') <- takeFromStack env es as
       pure (e :: env', stk')
takeFromStack env stk [] = pure (env, stk)
takeFromStack env [] args = Nothing

thinAll : (ns : List Name) -> CExp (outer ++ inner) -> CExp (outer ++ ns ++ inner)
thinAll [] exp = exp
thinAll {outer} {inner} (n :: ns) exp
    = thin {outer} {inner = ns ++ inner} n (thinAll ns exp)

mutual
  evalLocal : {auto c : Ref Ctxt Defs} ->
              FC -> List Name -> Stack free ->
              EEnv free vars ->
              {idx : Nat} -> .(IsVar x idx (vars ++ free)) ->
              Core (CExp free)
  evalLocal {vars = []} fc rec stk env p
      = pure $ unload stk (CLocal fc p)
  evalLocal {vars = x :: xs} fc rec stk (v :: env) First
      = eval rec env stk (weakenNs xs v)
  evalLocal {vars = x :: xs} fc rec stk (_ :: env) (Later p)
      = evalLocal fc rec stk env p

  tryApply : {auto c : Ref Ctxt Defs} ->
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
      = do let thinsc = thin x {outer = x :: vars} {inner = free} sc
           sc' <- eval rec (CLocal fc First :: weakenEnv env) [] thinsc
           pure $ CLam fc x sc'
  eval rec env (e :: stk) (CLam fc x sc) = eval rec (e :: env) stk sc
  eval {vars} {free} rec env stk (CLet fc x val sc)
      = do let thinsc = thin x {outer = x :: vars} {inner = free} sc
           sc' <- eval rec (CLocal fc First :: weakenEnv env) [] thinsc
           pure $ CLet fc x !(eval rec env [] val) sc'
  eval rec env stk (CApp fc f args)
      = eval rec env (!(traverse (eval rec env []) args) ++ stk) f
  eval rec env stk (CCon fc n t args)
      = pure $ unload stk $ CCon fc n t !(traverse (eval rec env []) args)
  eval rec env stk (COp fc p args)
      = pure $ unload stk $ COp fc p !(mapV (eval rec env []) args)
    where
      mapV : (a -> Core b) -> Vect n a -> Core (Vect n b)
      mapV f [] = pure []
      mapV f (x :: xs) = pure $ !(f x) :: !(mapV f xs)
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
           case !(pickAlt rec env stk sc' alts def) of
                Nothing =>
                   do def' <- case def of
                                   Nothing => pure Nothing
                                   Just d => pure (Just !(eval rec env stk d))
                      pure $
                         CConCase fc sc'
                                !(traverse (evalAlt fc rec env stk) alts)
                                def'
                Just val => pure val
  eval rec env stk (CConstCase fc sc alts def)
      = do sc' <- eval rec env [] sc
           case !(pickConstAlt rec env stk sc' alts def) of
                Nothing =>
                   do def' <- case def of
                                   Nothing => pure Nothing
                                   Just d => pure (Just !(eval rec env stk d))
                      pure $
                         CConstCase fc sc'
                                    !(traverse (evalConstAlt rec env stk) alts)
                                    def'
                Just val => pure val
  eval rec env stk (CPrimVal fc c) = pure $ unload stk $ CPrimVal fc c
  eval rec env stk (CErased fc) = pure $ unload stk $ CErased fc
  eval rec env stk (CCrash fc str) = pure $ unload stk $ CCrash fc str

  evalAlt : {auto c : Ref Ctxt Defs} ->
            FC -> List Name -> EEnv free vars -> Stack free -> CConAlt (vars ++ free) ->
            Core (CConAlt free)
  evalAlt {free} {vars} fc rec env stk (MkConAlt n t args sc)
      = do let sc' = thinAll {outer=args ++ vars} {inner=free} args
                        (rewrite sym (appendAssociative args vars free) in sc)
           scEval <- eval rec (extendLoc fc env args) (map (weakenNs args) stk) sc'
           pure $ MkConAlt n t args scEval

  evalConstAlt : {auto c : Ref Ctxt Defs} ->
                 List Name -> EEnv free vars -> Stack free -> CConstAlt (vars ++ free) ->
                 Core (CConstAlt free)
  evalConstAlt rec env stk (MkConstAlt c sc)
      = pure $ MkConstAlt c !(eval rec env stk sc)

  pickAlt : {auto c : Ref Ctxt Defs} ->
            List Name -> EEnv free vars -> Stack free ->
            CExp free -> List (CConAlt (vars ++ free)) ->
            Maybe (CExp (vars ++ free)) ->
            Core (Maybe (CExp free))
  pickAlt rec env stk (CCon fc n t args) [] def
      = case def of
             Nothing => pure Nothing
             Just d => pure $ Just !(eval rec env stk d)
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
                 List Name -> EEnv free vars -> Stack free ->
                 CExp free -> List (CConstAlt (vars ++ free)) ->
                 Maybe (CExp (vars ++ free)) ->
                 Core (Maybe (CExp free))
  pickConstAlt rec env stk (CPrimVal fc c) [] def
      = case def of
             Nothing => pure Nothing
             Just d => pure $ Just !(eval rec env stk d)
  pickConstAlt {vars} {free} rec env stk (CPrimVal fc c) (MkConstAlt c' sc :: alts) def
      = if c == c'
           then pure $ Just !(eval rec env stk sc)
           else pickConstAlt rec env stk (CPrimVal fc c) alts def
  pickConstAlt rec env stk _ _ _ = pure Nothing

inline : {auto c : Ref Ctxt Defs} ->
         CDef -> Core CDef
inline (MkFun args exp) = pure $ MkFun args !(eval [] [] [] exp)
inline d = pure d

export
inlineDef : {auto c : Ref Ctxt Defs} ->
            Name -> Core ()
inlineDef n
    = do defs <- get Ctxt
         case !(lookupCtxtExact n (gamma defs)) of
              Nothing => pure ()
              Just def =>
                   case compexpr def of
                        Nothing => pure ()
                        Just cexpr =>
                             do -- coreLift $ putStrLn $ show (fullname def) ++ " before: " ++ show cexpr
                                inlined <- inline cexpr
                                -- coreLift $ putStrLn $ show (fullname def) ++ " after: " ++ show inlined
                                setCompiled n inlined

