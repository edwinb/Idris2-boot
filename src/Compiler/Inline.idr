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

resolveRef : (done : List Name) -> Bounds bound -> FC -> Name ->
             Maybe (CExp (later ++ (done ++ bound ++ vars)))
resolveRef done None fc n = Nothing
resolveRef {later} {vars} done (Add {xs} new old bs) fc n
    = if n == old
         then rewrite appendAssociative later done (new :: xs ++ vars) in
              let MkNVar p = weakenNVar {inner = new :: xs ++ vars}
                                        (later ++ done) First in
                    Just (CLocal fc p)
         else rewrite appendAssociative done [new] (xs ++ vars)
                in resolveRef (done ++ [new]) bs fc n

mutual
  mkLocals : {later, vars : _} ->
             Bounds bound ->
             CExp (later ++ vars) -> CExp (later ++ (bound ++ vars))
  mkLocals bs (CLocal {idx} {x} fc p)
      = let MkNVar p' = addVars bs p in CLocal {x} fc p'
  mkLocals {later} {vars} bs (CRef fc var)
      = maybe (CRef fc var) id (resolveRef [] bs fc var)
  mkLocals {later} {vars} bs (CLam fc x sc)
      = let sc' = mkLocals bs {later = x :: later} {vars} sc in
            CLam fc x sc'
  mkLocals {later} {vars} bs (CLet fc x val sc)
      = let sc' = mkLocals bs {later = x :: later} {vars} sc in
            CLet fc x (mkLocals bs val) sc'
  mkLocals bs (CApp fc f xs)
      = CApp fc (mkLocals bs f) (assert_total (map (mkLocals bs) xs))
  mkLocals bs (CCon fc x tag xs)
      = CCon fc x tag (assert_total (map (mkLocals bs) xs))
  mkLocals bs (COp fc x xs)
      = COp fc x (assert_total (map (mkLocals bs) xs))
  mkLocals bs (CExtPrim fc x xs)
      = CExtPrim fc x (assert_total (map (mkLocals bs) xs))
  mkLocals bs (CForce fc x)
      = CForce fc (mkLocals bs x)
  mkLocals bs (CDelay fc x)
      = CDelay fc (mkLocals bs x)
  mkLocals bs (CConCase fc sc xs def)
      = CConCase fc (mkLocals bs sc)
                 (assert_total (map (mkLocalsConAlt bs) xs))
                 (assert_total (map (mkLocals bs) def))
  mkLocals bs (CConstCase fc sc xs def)
      = CConstCase fc (mkLocals bs sc)
                 (assert_total (map (mkLocalsConstAlt bs) xs))
                 (assert_total (map (mkLocals bs) def))
  mkLocals bs (CPrimVal fc x) = CPrimVal fc x
  mkLocals bs (CErased fc) = CErased fc
  mkLocals bs (CCrash fc x) = CCrash fc x

  mkLocalsConAlt : Bounds bound ->
                   CConAlt (later ++ vars) -> CConAlt (later ++ (bound ++ vars))
  mkLocalsConAlt {bound} {later} {vars} bs (MkConAlt x tag args sc)
        = let sc' : CExp ((args ++ later) ++ vars)
                  = rewrite sym (appendAssociative args later vars) in sc in
              MkConAlt x tag args
               (rewrite appendAssociative args later (bound ++ vars) in
                        mkLocals bs sc')

  mkLocalsConstAlt : Bounds bound ->
                     CConstAlt (later ++ vars) -> CConstAlt (later ++ (bound ++ vars))
  mkLocalsConstAlt bs (MkConstAlt x sc) = MkConstAlt x (mkLocals bs sc)

refsToLocals : Bounds bound -> CExp vars -> CExp (bound ++ vars)
refsToLocals None tm = tm
refsToLocals bs y = mkLocals {later = []} bs y

refToLocal : Name -> (x : Name) -> CExp vars -> CExp (x :: vars)
refToLocal x new tm = refsToLocals (Add new x None) tm

mutual
  used : Name -> CExp free -> Bool
  used n (CRef _ n') = n == n'
  used n (CLam _ _ sc) = used n sc
  used n (CLet _ _ val sc) = used n val || used n sc
  used n (CApp _ x args) = used n x || or (map Delay (map (used n) args))
  used n (CCon _ _ _ args) = or (map Delay (map (used n) args))
  used n (COp _ _ args) = or (map Delay (map (used n) args))
  used n (CExtPrim _ _ args) = or (map Delay (map (used n) args))
  used n (CForce _ x) = used n x
  used n (CDelay _ x) = used n x
  used n (CConCase fc sc alts def)
     = used n sc || or (map Delay (map (usedCon n) alts))
                 || maybe False (used n) def
  used n (CConstCase fc sc alts def)
     = used n sc || or (map Delay (map (usedConst n) alts))
                 || maybe False (used n) def
  used _ tm = False

  usedCon : Name -> CConAlt free -> Bool
  usedCon n (MkConAlt _ _ _ sc) = used n sc

  usedConst : Name -> CConstAlt free -> Bool
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
  eval {vars} {free} rec env stk (CLet fc x val sc)
      = do xn <- genName "letv"
           sc' <- eval rec (CRef fc xn :: env) [] sc
           if used xn sc'
              then do val' <- eval rec env [] val
                      pure (unload stk $ CLet fc x val' (refToLocal xn x sc'))
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
fixArityTm (CLet fc x val sc) args
    = pure $ expandToArity Z
                 (CLet fc x !(fixArityTm val []) !(fixArityTm sc [])) args
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
