module Core.Normalise

import Core.Context
import Core.Core
import Core.Env
import Core.TT
import Core.Value

%default covering

-- A pair of a term and its normal form. This could be constructed either
-- from a term (via 'gnf') or a normal form (via 'glueBack') but the other
-- part will only be constructed when needed, because it's in Core.
public export
data Glued : List Name -> Type where
     MkGlue : Core (Term vars) -> Core (NF vars) -> Glued vars

export
getTerm : Glued vars -> Core (Term vars)
getTerm (MkGlue tm _) = tm

export
getNF : Glued vars -> Core (NF vars)
getNF (MkGlue _ nf) = nf

Stack : List Name -> Type
Stack vars = List (AppInfo, Closure vars)

evalWithOpts : {vars : _} ->
               Defs -> EvalOpts ->
               Env Term free -> LocalEnv free vars -> 
               Term (vars ++ free) -> Stack free -> Core (NF free)

export
evalClosure : Defs -> Closure free -> Core (NF free)

export
toClosure : EvalOpts -> Env Term outer -> Term outer -> Closure outer
toClosure opts env tm = MkClosure opts [] env tm

parameters (defs : Defs, opts : EvalOpts)
  mutual
    eval : {vars : _} ->
           Env Term free -> LocalEnv free vars -> 
           Term (vars ++ free) -> Stack free -> Core (NF free)
    eval env locs (Local fc mrig idx prf) stk 
        = evalLocal env locs fc mrig idx prf stk
    eval env locs (Ref fc nt fn) stk 
        = evalRef env locs False fc nt fn stk (NApp fc (NRef nt fn) stk)
    eval env locs (Meta fc name idx args) stk
        = do let args' = map (\a => (explApp Nothing, MkClosure opts locs env a)) args
             evalMeta env locs fc name idx args' stk
    eval env locs (Bind fc x (Lam r _ ty) scope) ((p, thunk) :: stk)
        = eval env (thunk :: locs) scope stk
    eval env locs (Bind fc x (Let r val ty) scope) stk
        = eval env (MkClosure opts locs env val :: locs) scope stk
    eval env locs (Bind fc x b scope) stk 
        = do b' <- traverse (\tm => eval env locs tm stk) b
             pure $ NBind fc x b'
                      (\arg => eval env (arg :: locs) scope stk)
    eval env locs (App fc fn p arg) stk 
        = eval env locs fn ((p, MkClosure opts locs env arg) :: stk)
    eval env locs (Case fc cs ty x alts) stk 
        = throw (InternalError "Case evaluator not implemented")
    eval env locs (As fc idx p tm) stk = eval env locs tm stk 
    eval env locs (TDelayed fc r ty) stk 
        = pure (NDelayed fc r (MkClosure opts locs env ty))
    eval env locs (TDelay fc r tm) stk 
        = pure (NDelay fc r (MkClosure opts locs env tm))
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
    evalLocal env (MkClosure opts locs' env' tm' :: locs) fc mrig Z First stk
        = evalWithOpts defs opts env' locs' tm' stk
    evalLocal {free} {vars = x :: xs} 
              env (MkNFClosure nf :: locs) fc mrig Z First stk
        = applyToStack nf stk
      where
        applyToStack : NF free -> Stack free -> Core (NF free)
        applyToStack (NBind fc _ (Lam r e ty) sc) ((p, arg) :: stk)
            = do arg' <- sc arg
                 applyToStack arg' stk
        applyToStack (NApp fc (NRef nt fn) args) stk
            = evalRef {vars = xs} env locs False fc nt fn (args ++ stk)
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
    
    evalMeta : {vars : _} ->
               Env Term free -> LocalEnv free vars -> 
               FC -> Name -> Int -> List (AppInfo, Closure free) ->
               Stack free -> Core (NF free)
    evalMeta {vars} env locs fc nm i args stk
        = evalRef env locs True fc Func (Resolved i) (args ++ stk)
                  (NApp fc (NMeta nm i args) stk)

    evalRef : {vars : _} ->
              Env Term free -> LocalEnv free vars -> (isMeta : Bool) ->
              FC -> NameType -> Name -> Stack free -> (def : Lazy (NF free)) ->
              Core (NF free)
    evalRef env locs meta fc (DataCon tag arity) fn stk def
        = pure $ NDCon fc fn tag arity stk
    evalRef env locs meta fc (TyCon tag arity) fn stk def
        = pure $ NTCon fc fn tag arity stk
    evalRef env locs meta fc Bound fn stk def
        = pure def
    evalRef env locs meta fc nt n stk def 
        = do Just res <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure def 
             evalDef env locs meta (definition res) (flags res) stk def

    evalDef : {vars : _} ->
              Env Term free -> LocalEnv free vars ->
              (isMeta : Bool) ->
              Def -> List DefFlag -> Stack free -> (def : Lazy (NF free)) ->
              Core (NF free)
    evalDef {vars} env locs meta (Fn tm) flags stk def
       -- If evaluating the definition fails (e.g. due to a case being
       -- stuck) return the default
        = if meta || not (holesOnly opts) ||
                (tcInline opts && elem TCInline flags)
             then catch (eval env locs (embed tm) stk)
                        (\err => pure def)
             else pure def
    -- All other cases, use the default value, which is already applied to
    -- the stack
    evalDef env locs _ _ _ stk def = pure def

-- Make sure implicit argument order is right... 'vars' is used so we'll
-- write it explicitly, but it does appear after the parameters in 'eval'!
evalWithOpts {vars} defs opts = eval {vars} defs opts

evalClosure defs (MkClosure opts locs env tm)
    = eval defs opts env locs tm []
evalClosure defs (MkNFClosure nf) = pure nf

export
nf : Defs -> Env Term vars -> Term vars -> Core (NF vars)
nf defs env tm = eval defs defaultOpts env [] tm []

export
nfOpts : EvalOpts -> Defs -> Env Term vars -> Term vars -> Core (NF vars)
nfOpts opts defs env tm = eval defs opts env [] tm []

export
gnf : Defs -> Env Term vars -> Term vars -> Glued vars
gnf defs env tm = MkGlue (pure tm) (nf defs env tm)

export
gType : FC -> Glued vars
gType fc = MkGlue (pure (TType fc)) (pure (NType fc))

export
data QVar : Type where

public export
interface Quote (tm : List Name -> Type) where
    quote : Defs -> Env Term vars -> tm vars -> Core (Term vars)
    quoteGen : Ref QVar Int -> Defs -> Env Term vars -> tm vars -> Core (Term vars)

    quote defs env tm
        = do q <- newRef QVar 0
             quoteGen q defs env tm

genName : {auto q : Ref QVar Int} -> String -> Core Name
genName n
    = do i <- get QVar
         put QVar (i + 1)
         pure (MN n i)

mutual
  quoteArgs : {bound : _} ->
              Ref QVar Int -> Defs -> Bounds bound ->
              Env Term free -> List (AppInfo, Closure free) -> 
              Core (List (AppInfo, Term (bound ++ free)))
  quoteArgs q defs bounds env [] = pure []
  quoteArgs q defs bounds env ((p, a) :: args)
      = pure $ ((p, !(quoteGenNF q defs bounds env !(evalClosure defs a))) ::
                !(quoteArgs q defs bounds env args))

  quoteHead : {bound : _} ->
              Ref QVar Int -> Defs -> 
              FC -> Bounds bound -> Env Term free -> NHead free -> 
              Core (Term (bound ++ free))
  quoteHead {bound} q defs fc bounds env (NLocal mrig _ prf) 
      = let (_ ** prf') = addLater bound prf in
            pure $ Local fc mrig _ prf'
    where
      addLater : (ys : List Name) -> IsVar n idx xs -> 
                 (idx' ** IsVar n idx' (ys ++ xs))
      addLater [] isv = (_ ** isv)
      addLater (x :: xs) isv 
          = let (_ ** isv') = addLater xs isv in
                (_ ** Later isv')
  quoteHead q defs fc bounds env (NRef Bound n) 
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
  quoteHead q defs fc bounds env (NRef nt n) = pure $ Ref fc nt n
  quoteHead q defs fc bounds env (NMeta n i args)
      = do args' <- quoteArgs q defs bounds env args
           pure $ Meta fc n i (map snd args')

  quoteBinder : {bound : _} ->
                Ref QVar Int -> Defs -> Bounds bound ->
                Env Term free -> Binder (NF free) -> 
                Core (Binder (Term (bound ++ free)))
  quoteBinder q defs bounds env (Lam r p ty) 
      = do ty' <- quoteGenNF q defs bounds env ty
           pure (Lam r p ty')
  quoteBinder q defs bounds env (Let r val ty)
      = do val' <- quoteGenNF q defs bounds env val
           ty' <- quoteGenNF q defs bounds env ty
           pure (Let r val' ty')
  quoteBinder q defs bounds env (Pi r p ty)
      = do ty' <- quoteGenNF q defs bounds env ty
           pure (Pi r p ty')
  quoteBinder q defs bounds env (PVar r ty)
      = do ty' <- quoteGenNF q defs bounds env ty
           pure (PVar r ty')
  quoteBinder q defs bounds env (PLet r val ty)
      = do val' <- quoteGenNF q defs bounds env val
           ty' <- quoteGenNF q defs bounds env ty
           pure (PLet r val' ty')
  quoteBinder q defs bounds env (PVTy r ty)
      = do ty' <- quoteGenNF q defs bounds env ty
           pure (PVTy r ty')

  quoteGenNF : {bound : _} ->
               Ref QVar Int ->
               Defs -> Bounds bound -> 
               Env Term vars -> NF vars -> Core (Term (bound ++ vars))
  quoteGenNF q defs bound env (NBind fc n b sc)
      = do var <- genName "qv"
           sc' <- quoteGenNF q defs (Add n var bound) env 
                       !(sc (toClosure defaultOpts env (Ref fc Bound var)))
           b' <- quoteBinder q defs bound env b
           pure (Bind fc n b' sc')
  quoteGenNF q defs bound env (NApp fc f args)
      = do f' <- quoteHead q defs fc bound env f
           args' <- quoteArgs q defs bound env args
           pure $ applyInfo fc f' args'
  quoteGenNF q defs bound env (NDCon fc n t ar args) 
      = do args' <- quoteArgs q defs bound env args
           pure $ applyInfo fc (Ref fc (DataCon t ar) n) args'
  quoteGenNF q defs bound env (NTCon fc n t ar args) 
      = do args' <- quoteArgs q defs bound env args
           pure $ applyInfo fc (Ref fc (TyCon t ar) n) args'
  quoteGenNF q defs bound env (NDelayed fc r arg)
      = do argNF <- evalClosure defs arg
           argQ <- quoteGenNF q defs bound env argNF
           pure (TDelayed fc r argQ)
  quoteGenNF q defs bound env (NDelay fc r arg) 
      = do argNF <- evalClosure defs arg
           argQ <- quoteGenNF q defs bound env argNF
           pure (TDelay fc r argQ)
  quoteGenNF q defs bound env (NForce fc arg) 
      = case arg of
             NDelay fc _ arg =>
                do argNF <- evalClosure defs arg
                   quoteGenNF q defs bound env argNF
             t => do arg' <- quoteGenNF q defs bound env arg
                     pure (TForce fc arg')
  quoteGenNF q defs bound env (NPrimVal fc c) = pure $ PrimVal fc c
  quoteGenNF q defs bound env (NErased fc) = pure $ Erased fc
  quoteGenNF q defs bound env (NType fc) = pure $ TType fc

export
Quote NF where
  quoteGen q defs env tm = quoteGenNF q defs None env tm

export
Quote Term where
  quoteGen q defs env tm = pure tm

export
Quote Closure where
  quoteGen q defs env c = quoteGen q defs env !(evalClosure defs c)

export
glueBack : Defs -> Env Term vars -> NF vars -> Glued vars
glueBack defs env nf 
    = MkGlue (do empty <- clearDefs defs
                 quote empty env nf) 
             (pure nf)

export
normalise : Defs -> Env Term free -> Term free -> Core (Term free)
normalise defs env tm = quote defs env !(nf defs env tm)

export
normaliseHoles : Defs -> Env Term free -> Term free -> Core (Term free)
normaliseHoles defs env tm 
    = quote defs env !(nfOpts withHoles defs env tm)

public export
interface Convert (tm : List Name -> Type) where
  convert : Defs -> Env Term vars -> 
            tm vars -> tm vars -> Core Bool
  convGen : Ref QVar Int ->
            Defs -> Env Term vars -> 
            tm vars -> tm vars -> Core Bool

  convert defs env tm tm' 
      = do q <- newRef QVar 0
           convGen q defs env tm tm'

mutual
  allConv : Ref QVar Int -> Defs -> Env Term vars ->
            List (Closure vars) -> List (Closure vars) -> Core Bool
  allConv q defs env [] [] = pure True
  allConv q defs env (x :: xs) (y :: ys)
      = pure $ !(convGen q defs env x y) && !(allConv q defs env xs ys)
  allConv q defs env _ _ = pure False

  chkConvHead : Ref QVar Int -> Defs -> Env Term vars ->
                NHead vars -> NHead vars -> Core Bool 
  chkConvHead q defs env (NLocal _ idx _) (NLocal _ idx' _) = pure $ idx == idx'
  chkConvHead q defs env (NRef _ n) (NRef _ n') = pure $ n == n'
  chkConvHead q defs env (NMeta n i args) (NMeta n' i' args') 
     = if i == i'
          then allConv q defs env (map snd args) (map snd args')
          else pure False
  chkConvHead q defs env _ _ = pure False

  -- Comparing multiplicities when converting pi binders
  subRig : RigCount -> RigCount -> Bool
  subRig Rig1 RigW = True -- we can pass a linear function if a general one is expected
  subRig x y = x == y -- otherwise, the multiplicities need to match up

  convBinders : Ref QVar Int -> Defs -> Env Term vars ->
                Binder (NF vars) -> Binder (NF vars) -> Core Bool
  convBinders q defs env (Pi cx ix tx) (Pi cy iy ty)
      = if ix /= iy || not (subRig cx cy)
           then pure False
           else convGen q defs env tx ty
  convBinders q defs env (Lam cx ix tx) (Lam cy iy ty)
      = if ix /= iy || cx /= cy
           then pure False
           else convGen q defs env tx ty
  convBinders q defs env bx by
      = if multiplicity bx /= multiplicity by
           then pure False
           else convGen q defs env (binderType bx) (binderType by)


  export
  Convert NF where
    convGen q defs env (NBind fc x b sc) (NBind _ x' b' sc') 
        = do var <- genName "conv"
             let c = MkClosure defaultOpts [] env (Ref fc Bound var)
             bok <- convBinders q defs env b b'
             if bok
                then do bsc <- sc c
                        bsc' <- sc' c
                        convGen q defs env bsc bsc'
                else pure False

    convGen q defs env tmx@(NBind fc x (Lam c ix tx) scx) tmy 
        = do empty <- clearDefs defs
             etay <- nf defs env 
                        (Bind fc x (Lam c ix !(quote empty env tx))
                           (App fc (weaken !(quote empty env tmy))
                                (appInf (Just x) ix) (Local fc Nothing _ First)))
             convGen q defs env tmx etay
    convGen q defs env tmx tmy@(NBind fc y (Lam c iy ty) scy)
        = do empty <- clearDefs defs
             etax <- nf defs env 
                        (Bind fc y (Lam c iy !(quote empty env ty))
                           (App fc (weaken !(quote empty env tmx))
                                (appInf (Just y) iy) (Local fc Nothing _ First)))
             convGen q defs env etax tmy

    convGen q defs env (NApp _ val args) (NApp _ val' args')
        = if !(chkConvHead q defs env val val')
             then allConv q defs env (map snd args) (map snd args')
             else pure False

    convGen q defs env (NDCon _ nm tag _ args) (NDCon _ nm' tag' _ args')
        = if tag == tag'
             then allConv q defs env (map snd args) (map snd args')
             else pure False
    convGen q defs env (NTCon _ nm tag _ args) (NTCon _ nm' tag' _ args')
        = if nm == nm'
             then allConv q defs env (map snd args) (map snd args')
             else pure False

    convGen q defs env (NDelayed _ r arg) (NDelayed _ r' arg')
        = if r == r'
             then convGen q defs env arg arg'
             else pure False
    convGen q defs env (NDelay _ r arg) (NDelay _ r' arg')
        = if r == r'
             then convGen q defs env arg arg'
             else pure False
    convGen q defs env (NForce _ arg) (NForce _ arg')
        = convGen q defs env arg arg'

    convGen q defs env (NPrimVal _ c) (NPrimVal _ c') = pure (c == c')
    convGen q defs env (NErased _) _ = pure True
    convGen q defs env _ (NErased _) = pure True
    convGen q defs env (NType _) (NType _) = pure True
    convGen q defs env x y = pure False

  export
  Convert Term where
    convGen q defs env x y
        = convGen q defs env !(nf defs env x) !(nf defs env y)

  export
  Convert Closure where
    convGen q defs env x y
        = convGen q defs env !(evalClosure defs x) !(evalClosure defs y)

export
getValArity : Defs -> Env Term vars -> NF vars -> Core Nat
getValArity defs env (NBind fc x (Pi _ _ _) sc) 
    = pure (S !(getValArity defs env !(sc (toClosure defaultOpts env (Erased fc)))))
getValArity defs env val = pure 0

export
getArity : Defs -> Env Term vars -> Term vars -> Core Nat
getArity defs env tm = getValArity defs env !(nf defs env tm)

-- Log message with a value, translating back to human readable names first
export
logNF : {auto c : Ref Ctxt Defs} ->
        Nat -> Lazy String -> Env Term vars -> NF vars -> Core ()
logNF lvl msg env tmnf
    = do opts <- getOpts
         if logLevel opts >= lvl
            then do defs <- get Ctxt
                    tm <- quote defs env tmnf
                    tm' <- toFullNames tm
                    coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg 
                                          ++ ": " ++ show tm'
            else pure ()

-- Log message with a term, reducing holes and translating back to human
-- readable names first
export
logTermNF : {auto c : Ref Ctxt Defs} ->
            Nat -> Lazy String -> Env Term vars -> Term vars -> Core ()
logTermNF lvl msg env tm
    = do opts <- getOpts
         if logLevel opts >= lvl
            then do defs <- get Ctxt
                    tmnf <- normaliseHoles defs env tm
                    tm' <- toFullNames tmnf
                    coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg 
                                          ++ ": " ++ show tm'
            else pure ()

export
logGlue : {auto c : Ref Ctxt Defs} ->
          Nat -> Lazy String -> Env Term vars -> Glued vars -> Core ()
logGlue lvl msg env gtm
    = do opts <- getOpts
         if logLevel opts >= lvl
            then do defs <- get Ctxt
                    tm <- getTerm gtm
                    tm' <- toFullNames tm
                    coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg 
                                          ++ ": " ++ show tm'
            else pure ()


