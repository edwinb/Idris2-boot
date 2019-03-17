module Core.Normalise

import Core.Context
import Core.Core
import Core.Env
import Core.TT
import Core.Value

%default covering

Stack : List Name -> Type
Stack vars = List (AppInfo, Closure vars)

evalWithOpts : {vars : _} ->
               Defs -> UCtxt free -> EvalOpts ->
               Env Term free -> LocalEnv free vars -> 
               Term (vars ++ free) -> Stack free -> Core (NF free)

export
evalClosure : Defs -> Closure free -> Core (NF free)

export
toClosure : EvalOpts -> UCtxt outer -> Env Term outer -> Term outer -> Closure outer
toClosure opts ucs env tm = MkClosure opts ucs [] env tm

parameters (defs : Defs, ucs : UCtxt free, opts : EvalOpts)
  mutual
    eval : {vars : _} ->
           Env Term free -> LocalEnv free vars -> 
           Term (vars ++ free) -> Stack free -> Core (NF free)
    eval env locs (Local fc mrig idx prf) stk 
        = evalLocal env locs fc mrig idx prf stk
    eval env locs (Ref fc nt fn) stk 
        = evalRef env locs fc nt fn stk (NApp fc (NRef nt fn) stk)
    eval env locs (Bind fc x (Lam r _ ty) scope) ((p, thunk) :: stk)
         = eval env (thunk :: locs) scope stk
    eval env locs (Bind fc x (Let r val ty) scope) stk
         = eval env (MkClosure opts ucs locs env val :: locs) scope stk
    eval env locs (Bind fc x b scope) stk 
         = do b' <- mapBinder (\tm => eval env locs tm stk) b
              pure $ NBind fc x b'
                       (\arg => eval env (arg :: locs) scope stk)
    eval env locs (App fc fn p arg) stk 
         = eval env locs fn ((p, MkClosure opts ucs locs env arg) :: stk)
    eval env locs (Case fc cs ty x alts) stk 
       = throw (InternalError "Case evaluator not implemented")
    eval env locs (TDelayed fc r ty) stk 
       = pure (NDelayed fc r (MkClosure opts ucs locs env ty))
    eval env locs (TDelay fc r tm) stk 
       = pure (NDelay fc r (MkClosure opts ucs locs env tm))
    eval env locs (TForce fc tm) stk 
       = do tm' <- eval env locs tm stk
            case tm' of
                 NDelay fc r arg => evalClosure defs arg
                 _ => pure (NForce fc tm')
    eval env locs (PrimVal fc c) stk = pure $ NPrimVal fc c
    eval env locs (Erased fc) stk = pure $ NErased fc
    eval env locs (TType fc) stk = pure $ NType fc
    
    evalLocal : {vars : _} ->
                Env Term free -> LocalEnv free vars -> 
                FC -> Maybe RigCount -> 
                (idx : Nat) -> IsVar name idx (vars ++ free) ->
                Stack free ->
                Core (NF free)
    evalLocal {vars = []} env locs fc mrig idx prf stk
        = case getLetBinder prf env of
               Nothing => pure $ NApp fc (NLocal mrig idx prf) stk
               Just val => eval env [] val stk
    evalLocal env (MkClosure opts ucs' locs' env' tm' :: locs) fc mrig Z First stk
        = evalWithOpts defs ucs' opts env' locs' tm' stk
    evalLocal {free} {vars = x :: xs} 
              env (MkNFClosure nf :: locs) fc mrig Z First stk
        = applyToStack nf stk
      where
        applyToStack : NF free -> Stack free -> Core (NF free)
        applyToStack (NBind fc _ (Lam r e ty) sc) ((p, arg) :: stk)
            = do arg' <- sc arg
                 applyToStack arg' stk
        applyToStack (NApp fc (NRef nt fn) args) stk
            = evalRef {vars = xs} env locs fc nt fn (args ++ stk)
                      (NApp fc (NRef nt fn) args)
        applyToStack (NApp fc (NLocal mrig idx p) args) stk
          = let (idx' ** p') = insertVarNames {outer=[]} {ns = xs} idx p in
               evalLocal env locs fc mrig idx' p' (args ++ stk)
        applyToStack (NDCon fc n t a args) stk 
            = pure $ NDCon fc n t a (args ++ stk)
        applyToStack (NTCon fc n t a args) stk 
            = pure $ NTCon fc n t a (args ++ stk)
        applyToStack nf _ = pure nf

    evalLocal {vars = x :: xs} {free}
              env (_ :: locs) fc mrig (S idx) (Later p) stk
        = evalLocal {vars = xs} env locs fc mrig idx p stk

    evalRef : {vars : _} ->
              Env Term free -> LocalEnv free vars -> 
              FC -> NameType -> Name -> Stack free -> (def : Lazy (NF free)) ->
              Core (NF free)
    evalRef {vars} env locs fc nt (MV i) stk def
        = do Just res <- lookup i ucs
                  | Nothing => pure def
             eval env locs (weakenNs vars res) stk
    evalRef env locs fc (DataCon tag arity) fn stk def
        = pure $ NDCon fc fn tag arity stk
    evalRef env locs fc (TyCon tag arity) fn stk def
        = pure $ NTCon fc fn tag arity stk
    evalRef env locs fc Bound fn stk def
        = pure def
    evalRef env locs fc nt n stk def 
        = do Just res <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure def 
             evalDef env locs (definition res) stk def

    evalDef : {vars : _} ->
              Env Term free -> LocalEnv free vars ->
              Def -> Stack free -> (def : Lazy (NF free)) ->
              Core (NF free)
    evalDef {vars} env locs (Fn tm) stk def
        = eval env locs (embed tm) stk
    -- All other cases, use the default value, which is already applied to
    -- the stack
    evalDef env locs _ stk def = pure def

-- Make sure implicit argument order is right... 'vars' is used so we'll
-- write it explicitly, but it does appear after the parameters in 'eval'!
evalWithOpts {vars} defs ucs opts = eval {vars} defs ucs opts

evalClosure defs (MkClosure opts ucs locs env tm)
    = eval defs ucs opts env locs tm []
evalClosure defs (MkNFClosure nf) = pure nf

export
nf : Defs -> UCtxt vars -> Env Term vars -> Term vars -> Core (NF vars)
nf defs ucs env tm = eval defs ucs defaultOpts env [] tm []

export
data QVar : Type where

public export
interface Quote (tm : List Name -> Type) where
    quote : Defs -> UCtxt vars -> Env Term vars -> tm vars -> Core (Term vars)
    quoteGen : Ref QVar Int -> Defs -> UCtxt vars -> Env Term vars -> tm vars -> Core (Term vars)

    quote defs ucs env tm
        = do q <- newRef QVar 0
             quoteGen q defs ucs env tm

genName : {auto q : Ref QVar Int} -> String -> Core Name
genName n
    = do i <- get QVar
         put QVar (i + 1)
         pure (MN n i)

mutual
  quoteArgs : {bound : _} ->
              Ref QVar Int -> Defs -> UCtxt free -> Bounds bound ->
              Env Term free -> List (AppInfo, Closure free) -> 
              Core (List (AppInfo, Term (bound ++ free)))
  quoteArgs q defs ucs bounds env [] = pure []
  quoteArgs q defs ucs bounds env ((p, a) :: args)
      = pure $ ((p, !(quoteGenNF q defs ucs bounds env !(evalClosure defs a))) ::
                !(quoteArgs q defs ucs bounds env args))

  quoteHead : {bound : _} ->
              Ref QVar Int -> FC -> Bounds bound -> NHead free -> 
              Core (Term (bound ++ free))
  quoteHead {bound} q fc bounds (NLocal mrig _ prf) 
      = let (_ ** prf') = addLater bound prf in
            pure $ Local fc mrig _ prf'
    where
      addLater : (ys : List Name) -> IsVar n idx xs -> 
                 (idx' ** IsVar n idx' (ys ++ xs))
      addLater [] isv = (_ ** isv)
      addLater (x :: xs) isv 
          = let (_ ** isv') = addLater xs isv in
                (_ ** Later isv')
  quoteHead q fc bounds (NRef Bound n) 
      = case findName bounds of
             Just (_ ** _ ** p) => pure $ Local fc Nothing _ (varExtend p)
             Nothing => pure $ Ref fc Bound n
    where
      findName : Bounds bound' -> Maybe (x ** idx ** IsVar x idx bound')
      findName None = Nothing
      findName (Add x n' ns) 
          = case nameEq n n' of
                 Just Refl => Just (_ ** _ ** First)
                 Nothing => 
                    do (_ ** _ ** p) <- findName ns
                       Just (_ ** _ ** Later p)
  quoteHead q fc bounds (NRef nt n) = pure $ Ref fc nt n

  quoteBinder : {bound : _} ->
                Ref QVar Int -> Defs -> UCtxt free -> Bounds bound ->
                Env Term free -> Binder (NF free) -> 
                Core (Binder (Term (bound ++ free)))
  quoteBinder q defs ucs bounds env (Lam r p ty) 
      = do ty' <- quoteGenNF q defs ucs bounds env ty
           pure (Lam r p ty')
  quoteBinder q defs ucs bounds env (Let r val ty)
      = do val' <- quoteGenNF q defs ucs bounds env val
           ty' <- quoteGenNF q defs ucs bounds env ty
           pure (Let r val' ty')
  quoteBinder q defs ucs bounds env (Pi r p ty)
      = do ty' <- quoteGenNF q defs ucs bounds env ty
           pure (Pi r p ty')
  quoteBinder q defs ucs bounds env (PVar r ty)
      = do ty' <- quoteGenNF q defs ucs bounds env ty
           pure (PVar r ty')
  quoteBinder q defs ucs bounds env (PVTy r ty)
      = do ty' <- quoteGenNF q defs ucs bounds env ty
           pure (PVTy r ty')

  quoteGenNF : {bound : _} ->
               Ref QVar Int ->
               Defs -> UCtxt vars -> Bounds bound -> 
               Env Term vars -> NF vars -> Core (Term (bound ++ vars))
  quoteGenNF q defs ucs bound env (NBind fc n b sc)
      = do var <- genName "qv"
           sc' <- quoteGenNF q defs ucs (Add n var bound) env 
                       !(sc (toClosure defaultOpts ucs env (Ref fc Bound var)))
           b' <- quoteBinder q defs ucs bound env b
           pure (Bind fc n b' sc')
  quoteGenNF q defs ucs bound env (NApp fc f args)
      = do f' <- quoteHead q fc bound f
           args' <- quoteArgs q defs ucs bound env args
           pure $ applyInfo fc f' args'
  quoteGenNF q defs ucs bound env (NDCon fc n t ar args) 
      = do args' <- quoteArgs q defs ucs bound env args
           pure $ applyInfo fc (Ref fc (DataCon t ar) n) args'
  quoteGenNF q defs ucs bound env (NTCon fc n t ar args) 
      = do args' <- quoteArgs q defs ucs bound env args
           pure $ applyInfo fc (Ref fc (TyCon t ar) n) args'
  quoteGenNF q defs ucs bound env (NDelayed fc r arg)
      = do argNF <- evalClosure defs arg
           argQ <- quoteGenNF q defs ucs bound env argNF
           pure (TDelayed fc r argQ)
  quoteGenNF q defs ucs bound env (NDelay fc r arg) 
      = do argNF <- evalClosure defs arg
           argQ <- quoteGenNF q defs ucs bound env argNF
           pure (TDelay fc r argQ)
  quoteGenNF q defs ucs bound env (NForce fc arg) 
      = case arg of
             NDelay fc _ arg =>
                do argNF <- evalClosure defs arg
                   quoteGenNF q defs ucs bound env argNF
             t => do arg' <- quoteGenNF q defs ucs bound env arg
                     pure (TForce fc arg')
  quoteGenNF q defs ucs bound env (NPrimVal fc c) = pure $ PrimVal fc c
  quoteGenNF q defs ucs bound env (NErased fc) = pure $ Erased fc
  quoteGenNF q defs ucs bound env (NType fc) = pure $ TType fc

export
Quote NF where
  quoteGen q defs ucs env tm = quoteGenNF q defs ucs None env tm

export
Quote Term where
  quoteGen q defs ucs env tm = pure tm

export
Quote Closure where
  quoteGen q defs ucs env c = quoteGen q defs ucs env !(evalClosure defs c)

export
normalise : Defs -> Env Term free -> Term free -> Core (Term free)
normalise defs env tm 
    = do ucs <- initUCtxt
         quote defs ucs env !(nf defs ucs env tm)

public export
interface Convert (tm : List Name -> Type) where
  convert : Defs -> UCtxt vars -> Env Term vars -> 
            tm vars -> tm vars -> Core Bool
  convGen : Ref QVar Int ->
            Defs -> UCtxt vars -> Env Term vars -> 
            tm vars -> tm vars -> Core Bool

  convert defs ucs env tm tm' 
      = do q <- newRef QVar 0
           convGen q defs ucs env tm tm'

mutual
  allConv : Ref QVar Int -> Defs -> UCtxt vars -> Env Term vars ->
            List (Closure vars) -> List (Closure vars) -> Core Bool
  allConv q defs ucs env [] [] = pure True
  allConv q defs ucs env (x :: xs) (y :: ys)
      = pure $ !(convGen q defs ucs env x y) && !(allConv q defs ucs env xs ys)
  allConv q defs ucs env _ _ = pure False

  chkConvHead : NHead vars -> NHead vars -> Bool 
  chkConvHead (NLocal _ idx _) (NLocal _ idx' _) = idx == idx'
  chkConvHead (NRef _ n) (NRef _ n') = n == n'
  chkConvHead _ _ = False

  -- Comparing multiplicities when converting pi binders
  subRig : RigCount -> RigCount -> Bool
  subRig Rig1 RigW = True -- we can pass a linear function if a general one is expected
  subRig x y = x == y -- otherwise, the multiplicities need to match up

  convBinders : Ref QVar Int -> Defs -> UCtxt vars -> Env Term vars ->
                Binder (NF vars) -> Binder (NF vars) -> Core Bool
  convBinders q defs ucs env (Pi cx ix tx) (Pi cy iy ty)
      = if ix /= iy || not (subRig cx cy)
           then pure False
           else convGen q defs ucs env tx ty
  convBinders q defs ucs env (Lam cx ix tx) (Lam cy iy ty)
      = if ix /= iy || cx /= cy
           then pure False
           else convGen q defs ucs env tx ty
  convBinders q defs ucs env bx by
      = if multiplicity bx /= multiplicity by
           then pure False
           else convGen q defs ucs env (binderType bx) (binderType by)


  export
  Convert NF where
    convGen q defs ucs env (NBind fc x b sc) (NBind _ x' b' sc') 
        = do var <- genName "conv"
             let c = MkClosure defaultOpts ucs [] env (Ref fc Bound var)
             bok <- convBinders q defs ucs env b b'
             if bok
                then do bsc <- sc c
                        bsc' <- sc' c
                        convGen q defs ucs env bsc bsc'
                else pure False

    convGen q defs ucs env tmx@(NBind fc x (Lam c ix tx) scx) tmy 
        = do empty <- clearDefs defs
             etay <- nf defs ucs env 
                        (Bind fc x (Lam c ix !(quote empty ucs env tx))
                           (App fc (weaken !(quote empty ucs env tmy))
                                (appInf ix) (Local fc Nothing _ First)))
             convGen q defs ucs env tmx etay
    convGen q defs ucs env tmx tmy@(NBind fc y (Lam c iy ty) scy)
        = do empty <- clearDefs defs
             etax <- nf defs ucs env 
                        (Bind fc y (Lam c iy !(quote empty ucs env ty))
                           (App fc (weaken !(quote empty ucs env tmx))
                                (appInf iy) (Local fc Nothing _ First)))
             convGen q defs ucs env etax tmy

    convGen q defs ucs env (NApp _ val args) (NApp _ val' args')
        = if chkConvHead val val'
             then allConv q defs ucs env (map snd args) (map snd args')
             else pure False

    convGen q defs ucs env (NDCon _ nm tag _ args) (NDCon _ nm' tag' _ args')
        = if tag == tag'
             then allConv q defs ucs env (map snd args) (map snd args')
             else pure False
    convGen q defs ucs env (NTCon _ nm tag _ args) (NTCon _ nm' tag' _ args')
        = if nm == nm'
             then allConv q defs ucs env (map snd args) (map snd args')
             else pure False

    convGen q defs ucs env (NDelayed _ r arg) (NDelayed _ r' arg')
        = if r == r'
             then convGen q defs ucs env arg arg'
             else pure False
    convGen q defs ucs env (NDelay _ r arg) (NDelay _ r' arg')
        = if r == r'
             then convGen q defs ucs env arg arg'
             else pure False
    convGen q defs ucs env (NForce _ arg) (NForce _ arg')
        = convGen q defs ucs env arg arg'

    convGen q defs ucs env (NPrimVal _ c) (NPrimVal _ c') = pure (c == c')
    convGen q defs ucs env (NErased _) _ = pure True
    convGen q defs ucs env _ (NErased _) = pure True
    convGen q defs ucs env (NType _) (NType _) = pure True
    convGen q defs ucs env x y = pure False

  export
  Convert Term where
    convGen q defs ucs env x y
        = convGen q defs ucs env !(nf defs ucs env x) !(nf defs ucs env y)

  export
  Convert Closure where
    convGen q defs ucs env x y
        = convGen q defs ucs env !(evalClosure defs x) !(evalClosure defs y)
