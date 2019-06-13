module Core.Normalise

import Core.CaseTree
import Core.Context
import Core.Core
import Core.Env
import Core.Options
import Core.Primitives
import Core.TT
import Core.Value

import Data.IntMap
import Data.Vect

%default covering

-- A pair of a term and its normal form. This could be constructed either
-- from a term (via 'gnf') or a normal form (via 'glueBack') but the other
-- part will only be constructed when needed, because it's in Core.
public export
data Glued : List Name -> Type where
     MkGlue : (fromTerm : Bool) -> -- is it built from the term; i.e. can
                                   -- we read the term straight back?
              Core (Term vars) -> (Ref Ctxt Defs -> Core (NF vars)) -> Glued vars

export
isFromTerm : Glued vars -> Bool
isFromTerm (MkGlue ft _ _) = ft

export
getTerm : Glued vars -> Core (Term vars)
getTerm (MkGlue _ tm _) = tm

export
getNF : {auto c : Ref Ctxt Defs} -> Glued vars -> Core (NF vars)
getNF {c} (MkGlue _ _ nf) = nf c

Stack : List Name -> Type
Stack vars = List (AppInfo, Closure vars)

evalWithOpts : {vars : _} ->
               Defs -> EvalOpts ->
               Env Term free -> LocalEnv free vars -> 
               Term (vars ++ free) -> Stack free -> Core (NF free)

export
evalClosure : Defs -> Closure free -> Core (NF free)

export
evalArg : Defs -> (AppInfo, Closure free) -> Core (NF free)
evalArg defs (p, c) = evalClosure defs c

export
toClosure : EvalOpts -> Env Term outer -> Term outer -> Closure outer
toClosure opts env tm = MkClosure opts [] env tm

useMeta : FC -> Name -> Defs -> EvalOpts -> Core EvalOpts
useMeta fc (Resolved i) defs opts
    = case lookup i (usedMetas opts) of
           Nothing => pure (record { usedMetas $= insert i () } opts)
           Just _ => throw (CyclicMeta fc (Resolved i))
useMeta fc n defs opts
    = do let Just i = getNameID n (gamma defs)
              | Nothing => throw (UndefinedName fc n)
         useMeta fc (Resolved i) defs opts

parameters (defs : Defs, topopts : EvalOpts)
  mutual
    eval : {vars : _} ->
           Env Term free -> LocalEnv free vars -> 
           Term (vars ++ free) -> Stack free -> Core (NF free)
    eval env locs (Local fc mrig idx prf) stk 
        = evalLocal env locs fc mrig idx prf stk
    eval env locs (Ref fc nt fn) stk 
        = evalRef env locs False fc nt fn stk (NApp fc (NRef nt fn) stk)
    eval env locs (Meta fc name idx args) stk
        = do let args' = map (\a => (explApp Nothing, MkClosure topopts locs env a)) args
             evalMeta env locs fc name idx args' stk
    eval env locs (Bind fc x (Lam r _ ty) scope) ((p, thunk) :: stk)
        = eval env (thunk :: locs) scope stk
    eval env locs (Bind fc x b@(Let r val ty) scope) stk
        = if holesOnly topopts || argHolesOnly topopts
             then do b' <- traverse (\tm => eval env locs tm []) b
                     pure $ NBind fc x b'
                        (\defs', arg => evalWithOpts defs' topopts 
                                                env (arg :: locs) scope stk)
             else eval env (MkClosure topopts locs env val :: locs) scope stk
    eval env locs (Bind fc x b scope) stk 
        = do b' <- traverse (\tm => eval env locs tm []) b
             pure $ NBind fc x b'
                      (\defs', arg => evalWithOpts defs' topopts 
                                              env (arg :: locs) scope stk)
    eval env locs (App fc fn p arg) stk 
        = eval env locs fn ((p, MkClosure topopts locs env arg) :: stk)
    eval env locs (As fc n tm) stk 
        = if removeAs topopts
             then eval env locs tm stk
             else do n' <- eval env locs n stk
                     tm' <- eval env locs tm stk 
                     pure (NAs fc n' tm')
    eval env locs (TDelayed fc r ty) stk 
        = do ty' <- eval env locs ty stk
             pure (NDelayed fc r ty')
    eval env locs (TDelay fc r ty tm) stk 
        = pure (NDelay fc r (MkClosure topopts locs env ty)
                            (MkClosure topopts locs env tm))
    eval env locs (TForce fc tm) stk 
        = do tm' <- eval env locs tm []
             case tm' of
                  NDelay fc r _ arg => 
                      eval env (arg :: locs) (Local {name = UN "fvar"} fc Nothing _ First) stk
                  _ => pure (NForce fc tm')
    eval env locs (PrimVal fc c) stk = pure $ NPrimVal fc c
    eval env locs (Erased fc) stk = pure $ NErased fc
    eval env locs (TType fc) stk = pure $ NType fc
    
    evalLocal : {vars : _} ->
                Env Term free -> LocalEnv free vars -> 
                FC -> Maybe RigCount -> 
                (idx : Nat) -> .(IsVar name idx (vars ++ free)) ->
                Stack free ->
                Core (NF free)
    evalLocal {vars = []} env locs fc mrig idx prf stk
        = if not (holesOnly topopts || argHolesOnly topopts) && isLet idx env
             then
               case getBinder prf env of
                    Let _ val _ => eval env [] val stk
                    _ => pure $ NApp fc (NLocal mrig idx prf) stk
             else pure $ NApp fc (NLocal mrig idx prf) stk
      where
        isLet : Nat -> Env tm vars -> Bool
        isLet Z (Let _ _ _ :: env) = True
        isLet Z _ = False
        isLet (S k) (b :: env) = isLet k env
        isLet (S k) [] = False
    evalLocal env (MkClosure opts locs' env' tm' :: locs) fc mrig Z First stk
        = evalWithOpts defs opts env' locs' tm' stk
    evalLocal {free} {vars = x :: xs} 
              env (MkNFClosure nf :: locs) fc mrig Z First stk
        = applyToStack nf stk
      where
        applyToStack : NF free -> Stack free -> Core (NF free)
        applyToStack (NBind fc _ (Lam r e ty) sc) ((p, arg) :: stk)
            = do arg' <- sc defs arg
                 applyToStack arg' stk
        applyToStack (NApp fc (NRef nt fn) args) stk
            = evalRef {vars = xs} env locs False fc nt fn (args ++ stk)
                      (NApp fc (NRef nt fn) args)
        applyToStack (NApp fc (NLocal mrig idx p) args) stk
          = let MkVar p' = insertVarNames {outer=[]} {ns = xs} idx p in
               evalLocal env locs fc mrig _ p' (args ++ stk)
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
              Env Term free -> LocalEnv free vars -> 
              (isMeta : Bool) ->
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
             let redok = True -- evalAll topopts ||
--                          reducibleIn (currentNS defs) 
--                                      (fullname res) 
--                                      (visibility res)
             if redok
                then do
                   opts' <- if noCycles res
                               then useMeta fc n defs topopts
                               else pure topopts
                   evalDef env locs opts' meta fc 
                           (multiplicity res) (definition res) (flags res) stk def
                else pure def

    getCaseBound : List (AppInfo, Closure free) ->
                   (args : List Name) ->
                   LocalEnv free vars ->
                   Maybe (LocalEnv free (args ++ vars))
    getCaseBound [] [] loc = Just loc
    getCaseBound [] (x :: xs) loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) [] loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) (n :: ns) loc 
         = do loc' <- getCaseBound args ns loc
              pure (snd arg :: loc')

    evalConAlt : Env Term free -> 
                 LocalEnv free (more ++ vars) -> EvalOpts -> FC ->
                 Stack free -> 
                 (args : List Name) -> 
                 List (AppInfo, Closure free) -> 
                 CaseTree (args ++ more) ->
                 (default : Core (NF free)) -> 
                 Core (NF free)
    evalConAlt {more} {vars} env loc opts fc stk args args' sc def
         = maybe def (\bound => 
                            let loc' : LocalEnv _ ((args ++ more) ++ vars) 
                                = rewrite sym (appendAssociative args more vars) in
                                          bound in
                                evalTree env loc' opts fc stk sc def)
                     (getCaseBound args' args loc)

    tryAlt : Env Term free ->
             LocalEnv free (more ++ vars) -> EvalOpts -> FC -> 
             Stack free -> NF free -> CaseAlt more ->
             (default : Core (NF free)) -> Core (NF free)
    -- Ordinary constructor matching
    tryAlt {more} {vars} env loc opts fc stk (NDCon _ nm tag' arity args') (ConCase x tag args sc) def
         = if tag == tag'
              then evalConAlt env loc opts fc stk args args' sc def
              else def
    -- Type constructor matching, in typecase
    tryAlt {more} {vars} env loc opts fc stk (NTCon _ nm tag' arity args') (ConCase nm' tag args sc) def
         = if nm == nm'
              then evalConAlt env loc opts fc stk args args' sc def
              else def
    -- Primitive type matching, in typecase
    tryAlt env loc opts fc stk (NPrimVal _ c) (ConCase (UN x) tag [] sc) def
         = if show c == x
              then evalTree env loc opts fc stk sc def
              else def
    -- Type of type matching, in typecase
    tryAlt env loc opts fc stk (NType _) (ConCase (UN "Type") tag [] sc) def
         = evalTree env loc opts fc stk sc def
    -- Arrow matching, in typecase
    tryAlt {more} {vars}  
           env loc opts fc stk (NBind pfc x (Pi r e aty) scty) (ConCase (UN "->") tag [s,t] sc) def
       = evalConAlt {more} {vars} env loc opts fc stk [s,t]
                  [(explApp Nothing, MkNFClosure aty), 
                   (explApp Nothing, MkNFClosure (NBind pfc x (Lam r e aty) scty))]
                  sc def
    -- Delay matching
    tryAlt env loc opts fc stk (NDelay _ _ ty arg) (DelayCase tyn argn sc) def
         = evalTree env (ty :: arg :: loc) opts fc stk sc def
    -- Constant matching
    tryAlt env loc opts fc stk (NPrimVal _ c') (ConstCase c sc) def
         = if c == c' then evalTree env loc opts fc stk sc def
                      else def
    -- Default case matches against any *concrete* value
    tryAlt env loc opts fc stk val (DefaultCase sc) def
         = if concrete val 
              then evalTree env loc opts fc stk sc def
              else def
      where
        concrete : NF free -> Bool
        concrete (NDCon _ _ _ _ _) = True
        concrete (NTCon _ _ _ _ _) = True
        concrete (NPrimVal _ _) = True
        concrete (NBind _ _ _ _) = True
        concrete (NType _) = True
        concrete _ = False
    tryAlt _ _ _ _ _ _ _ def = def

    findAlt : Env Term free ->
              LocalEnv free (args ++ vars) -> EvalOpts -> FC ->
              Stack free -> NF free -> List (CaseAlt args) ->
              (default : Core (NF free)) -> Core (NF free)
    findAlt env loc opts fc stk val [] def = def
    findAlt env loc opts fc stk val (x :: xs) def
         = tryAlt env loc opts fc stk val x (findAlt env loc opts fc stk val xs def)

    evalTree : {vars : _} ->
               Env Term free -> LocalEnv free (args ++ vars) -> 
               EvalOpts -> FC ->
               Stack free -> CaseTree args ->
               (default : Core (NF free)) -> Core (NF free)
    evalTree {args} {vars} {free} env loc opts fc stk (Case idx x _ alts) def
      = do let x' : IsVar _ _ ((args ++ vars) ++ free) 
               = rewrite sym (appendAssociative args vars free) in
                         varExtend x
           xval <- evalLocal env loc fc Nothing idx x' []
           findAlt env loc opts fc stk xval alts def
    evalTree {args} {vars} {free} env loc opts fc stk (STerm tm) def
          = do let tm' : Term ((args ++ vars) ++ free) 
                    = rewrite sym (appendAssociative args vars free) in
                              embed tm 
               case fuel opts of
                    Nothing => evalWithOpts defs opts env loc tm' stk
                    Just Z => def
                    Just (S k) => 
                         do let opts' = record { fuel = Just k } opts
                            evalWithOpts defs opts' env loc tm' stk
    evalTree env loc opts fc stk _ def = def

    -- Take arguments from the stack, as long as there's enough.
    -- Returns the arguments, and the rest of the stack
    takeFromStack : (arity : Nat) -> Stack free ->
                    Maybe (Vect arity (Closure free), Stack free)
    takeFromStack arity stk = takeStk arity stk []
      where
        takeStk : (remain : Nat) -> Stack free -> 
                  Vect got (Closure free) -> 
                  Maybe (Vect (got + remain) (Closure free), Stack free)
        takeStk {got} Z stk acc = Just (rewrite plusZeroRightNeutral got in
                                    reverse acc, stk)
        takeStk (S k) [] acc = Nothing
        takeStk {got} (S k) (arg :: stk) acc 
           = rewrite sym (plusSuccRightSucc got k) in
                     takeStk k stk (snd arg :: acc)

    extendFromStack : (args : List Name) -> 
                      LocalEnv free vars -> Stack free ->
                      Maybe (LocalEnv free (args ++ vars), Stack free)
    extendFromStack [] loc stk = Just (loc, stk)
    extendFromStack (n :: ns) loc [] = Nothing
    extendFromStack (n :: ns) loc (arg :: args) 
         = do (loc', stk') <- extendFromStack ns loc args
              pure (snd arg :: loc', stk')

    evalOp : (Vect arity (NF free) -> Maybe (NF free)) ->
             Stack free -> (def : Lazy (NF free)) ->
             Core (NF free)
    evalOp {arity} fn stk def
        = case takeFromStack arity stk of
               -- Stack must be exactly the right height
               Just (args, []) => 
                  do argsnf <- evalAll args
                     case fn argsnf of
                          Nothing => pure def
                          Just res => pure res
               _ => pure def
      where
        -- No traverse for Vect in Core...
        evalAll : Vect n (Closure free) -> Core (Vect n (NF free))
        evalAll [] = pure []
        evalAll (c :: cs) = pure $ !(evalClosure defs c) :: !(evalAll cs)
                   
    evalDef : {vars : _} ->
              Env Term free -> LocalEnv free vars -> EvalOpts ->
              (isMeta : Bool) -> FC ->
              RigCount -> Def -> List DefFlag -> 
              Stack free -> (def : Lazy (NF free)) ->
              Core (NF free)
    evalDef {vars} env locs opts meta fc rigd (PMDef args tree _ _) flags stk def
       -- If evaluating the definition fails (e.g. due to a case being
       -- stuck) return the default.
       -- We can use the definition if one of the following is true:
       --   + We're not in 'holesOnly', 'argHolesOnly' or 'tcInline'
       --         (that's the default mode)
       --   + It's a metavariable and not in Rig0
       --   + It's a metavariable and we're not in 'argHolesOnly'
       --   + It's inlinable and and we're in 'tcInline'
        = if (not (holesOnly opts) && not (argHolesOnly opts) && not (tcInline opts))
             || (meta && rigd /= Rig0)
             || (meta && holesOnly opts)
             || (tcInline opts && elem TCInline flags)
             then case extendFromStack args locs stk of
                       Nothing => pure def
                       Just (locs', stk') => 
                            evalTree env locs' opts fc stk' tree (pure def)
             else pure def
    evalDef {vars} env locs opts meta fc rigd (Builtin op) flags stk def
        = evalOp (getOp op) stk def
    -- All other cases, use the default value, which is already applied to
    -- the stack
    evalDef env locs opts _ _ _ _ _ stk def = pure def

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
gnf : Env Term vars -> Term vars -> Glued vars
gnf env tm 
    = MkGlue True
             (pure tm) 
             (\c => do defs <- get Ctxt
                       nf defs env tm)

export
gnfOpts : EvalOpts -> Env Term vars -> Term vars -> Glued vars
gnfOpts opts env tm 
    = MkGlue True
             (pure tm) 
             (\c => do defs <- get Ctxt
                       nfOpts opts defs env tm)

export
gType : FC -> Glued vars
gType fc = MkGlue True (pure (TType fc)) (const (pure (NType fc)))

export
gErased : FC -> Glued vars
gErased fc = MkGlue True (pure (Erased fc)) (const (pure (NErased fc)))

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
      = let MkVar prf' = addLater bound prf in
            pure $ Local fc mrig _ prf'
    where
      addLater : (ys : List Name) -> IsVar n idx xs -> 
                 Var (ys ++ xs)
      addLater [] isv = MkVar isv
      addLater (x :: xs) isv 
          = let MkVar isv' = addLater xs isv in
                MkVar (Later isv')
  quoteHead q defs fc bounds env (NRef Bound n) 
      = case findName bounds of
             Just (MkVar p) => pure $ Local fc Nothing _ (varExtend p)
             Nothing => pure $ Ref fc Bound n
    where
      findName : Bounds bound' -> Maybe (Var bound')
      findName None = Nothing
      findName (Add x n' ns) 
          = case nameEq n n' of
                 Just Refl => Just (MkVar First)
                 Nothing => 
                    do (MkVar p) <- findName ns
                       Just (MkVar (Later p))
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
                       !(sc defs (toClosure defaultOpts env (Ref fc Bound var)))
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
  quoteGenNF q defs bound env (NAs fc n pat)
      = do n' <- quoteGenNF q defs bound env n
           pat' <- quoteGenNF q defs bound env pat
           pure (As fc n' pat')
  quoteGenNF q defs bound env (NDelayed fc r arg)
      = do argQ <- quoteGenNF q defs bound env arg
           pure (TDelayed fc r argQ)
  quoteGenNF q defs bound env (NDelay fc LInf ty arg)
      = do argNF <- evalClosure defs (toHolesOnly arg)
           argQ <- quoteGenNF q defs bound env argNF
           tyNF <- evalClosure defs (toHolesOnly ty)
           tyQ <- quoteGenNF q defs bound env tyNF
           pure (TDelay fc LInf tyQ argQ)
    where
      toHolesOnly : Closure vs -> Closure vs
      toHolesOnly (MkClosure _ locs env tm) 
          = MkClosure withArgHoles locs env tm
      toHolesOnly c = c
  quoteGenNF q defs bound env (NDelay fc r ty arg) 
      = do argNF <- evalClosure defs arg
           argQ <- quoteGenNF q defs bound env argNF
           tyNF <- evalClosure defs ty
           tyQ <- quoteGenNF q defs bound env tyNF
           pure (TDelay fc r tyQ argQ)
  quoteGenNF q defs bound env (NForce fc arg) 
      = case arg of
             NDelay fc _ _ arg =>
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
    = MkGlue False
             (do empty <- clearDefs defs
                 quote empty env nf) 
             (const (pure nf))

export
normalise : Defs -> Env Term free -> Term free -> Core (Term free)
normalise defs env tm = quote defs env !(nf defs env tm)

export
normaliseOpts : EvalOpts -> Defs -> Env Term free -> Term free -> Core (Term free)
normaliseOpts opts defs env tm 
    = quote defs env !(nfOpts opts defs env tm)

export
normaliseHoles : Defs -> Env Term free -> Term free -> Core (Term free)
normaliseHoles defs env tm 
    = quote defs env !(nfOpts withHoles defs env tm)

export
normaliseLHS : Defs -> Env Term free -> Term free -> Core (Term free)
normaliseLHS defs env tm 
    = quote defs env !(nfOpts onLHS defs env tm)

export
normaliseArgHoles : Defs -> Env Term free -> Term free -> Core (Term free)
normaliseArgHoles defs env tm 
    = quote defs env !(nfOpts withArgHoles defs env tm)

export
normaliseAll : Defs -> Env Term free -> Term free -> Core (Term free)
normaliseAll defs env tm 
    = quote defs env !(nfOpts withAll defs env tm)

-- Normalise, but without normalising the types of binders. Dealing with
-- binders is the slow part of normalisation so whenever we can avoid it, it's
-- a big win
export
normaliseScope : Defs -> Env Term vars -> Term vars -> Core (Term vars)
normaliseScope defs env (Bind fc n b sc) 
    = pure $ Bind fc n b !(normaliseScope defs (b :: env) sc)
normaliseScope defs env tm = normalise defs env tm

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
            List (a, Closure vars) -> List (a, Closure vars) -> Core Bool
  allConv q defs env [] [] = pure True
  allConv q defs env ((_, x) :: xs) ((_, y) :: ys)
      = pure $ !(convGen q defs env x y) && !(allConv q defs env xs ys)
  allConv q defs env _ _ = pure False

  chkConvHead : Ref QVar Int -> Defs -> Env Term vars ->
                NHead vars -> NHead vars -> Core Bool 
  chkConvHead q defs env (NLocal _ idx _) (NLocal _ idx' _) = pure $ idx == idx'
  chkConvHead q defs env (NRef _ n) (NRef _ n') = pure $ n == n'
  chkConvHead q defs env (NMeta n i args) (NMeta n' i' args') 
     = if i == i'
          then allConv q defs env args args'
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
                then do bsc <- sc defs c
                        bsc' <- sc' defs c
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
             then allConv q defs env args args'
             else pure False

    convGen q defs env (NDCon _ nm tag _ args) (NDCon _ nm' tag' _ args')
        = if tag == tag'
             then allConv q defs env args args'
             else pure False
    convGen q defs env (NTCon _ nm tag _ args) (NTCon _ nm' tag' _ args')
        = if nm == nm'
             then allConv q defs env args args'
             else pure False
    convGen q defs env (NAs _ _ tm) (NAs _ _ tm')
        = convGen q defs env tm tm'

    convGen q defs env (NDelayed _ r arg) (NDelayed _ r' arg')
        = if compatible r r'
             then convGen q defs env arg arg'
             else pure False
    convGen q defs env (NDelay _ r _ arg) (NDelay _ r' _ arg')
        = if compatible r r'
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
    = pure (S !(getValArity defs env !(sc defs (toClosure defaultOpts env (Erased fc)))))
getValArity defs env val = pure 0

export
getArity : Defs -> Env Term vars -> Term vars -> Core Nat
getArity defs env tm = getValArity defs env !(nf defs env tm)

-- Log message with a value, translating back to human readable names first
export
logNF : {auto c : Ref Ctxt Defs} ->
        Nat -> Lazy String -> Env Term vars -> NF vars -> Core ()
logNF lvl msg env tmnf
    = do opts <- getSession
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
    = do opts <- getSession
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
    = do opts <- getSession
         if logLevel opts >= lvl
            then do defs <- get Ctxt
                    tm <- getTerm gtm
                    tm' <- toFullNames tm
                    coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg 
                                          ++ ": " ++ show tm'
            else pure ()

export
logGlueNF : {auto c : Ref Ctxt Defs} ->
            Nat -> Lazy String -> Env Term vars -> Glued vars -> Core ()
logGlueNF lvl msg env gtm
    = do opts <- getSession
         if logLevel opts >= lvl
            then do defs <- get Ctxt
                    tm <- getTerm gtm
                    tmnf <- normaliseHoles defs env tm
                    tm' <- toFullNames tmnf
                    coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg 
                                          ++ ": " ++ show tm'
            else pure ()

export
logEnv : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         Nat -> String -> Env Term vars -> Core ()
logEnv lvl msg env
    = do opts <- getSession
         if logLevel opts >= lvl
            then dumpEnv env
            else pure ()
  where
    dumpEnv : {vs : List Name} -> Env Term vs -> Core ()
    dumpEnv [] = pure ()
    dumpEnv {vs = x :: _} (Let c val ty :: bs)
        = do logTermNF lvl (msg ++ ": let " ++ show x) bs val
             logTermNF lvl (msg ++ ":" ++ show c ++ " " ++ 
                            show x) bs ty
             dumpEnv bs
    dumpEnv {vs = x :: _} (b :: bs)
        = do logTermNF lvl (msg ++ ":" ++ show (multiplicity b) ++ " " ++ 
                            show x) bs (binderType b)
             dumpEnv bs

replace' : Int -> Defs -> Env Term vars ->
           (lhs : NF vars) -> (parg : Term vars) -> (exp : NF vars) ->
           Core (Term vars)
replace' {vars} tmpi defs env lhs parg tm
    = if !(convert defs env lhs tm)
         then pure parg
         else repSub tm
  where
    repArg : (AppInfo, Closure vars) -> Core (AppInfo, Term vars)
    repArg (p, c)
        = do tmnf <- evalClosure defs c
             tm <- replace' tmpi defs env lhs parg tmnf
             pure (p, tm)

    repSub : NF vars -> Core (Term vars)
    repSub (NBind fc x b scfn)
        = do b' <- traverse repSub b 
             let x' = MN "tmp" tmpi
             sc' <- replace' (tmpi + 1) defs env lhs parg 
                             !(scfn defs (toClosure defaultOpts env (Ref fc Bound x')))
             pure (Bind fc x b' (refsToLocals (Add x x' None) sc'))
    repSub (NApp fc hd []) 
        = do empty <- clearDefs defs
             quote empty env (NApp fc hd [])
    repSub (NApp fc hd args) 
        = do args' <- traverse repArg args
             pure $ applyInfo fc 
                        !(replace' tmpi defs env lhs parg (NApp fc hd []))
                        args'
    repSub (NDCon fc n t a args) 
        = do args' <- traverse repArg args
             empty <- clearDefs defs
             pure $ applyInfo fc 
                        !(quote empty env (NDCon fc n t a []))
                        args'
    repSub (NTCon fc n t a args) 
        = do args' <- traverse repArg args
             empty <- clearDefs defs
             pure $ applyInfo fc 
                        !(quote empty env (NTCon fc n t a []))
                        args'
    repSub (NAs fc a p)
        = do a' <- repSub a
             p' <- repSub p
             pure (As fc a' p')
    repSub (NDelayed fc r tm)
        = do tm' <- repSub tm
             pure (TDelayed fc r tm')
    repSub (NDelay fc r ty tm)
        = do ty' <- replace' tmpi defs env lhs parg !(evalClosure defs ty)
             tm' <- replace' tmpi defs env lhs parg !(evalClosure defs tm)
             pure (TDelay fc r ty' tm')
    repSub (NForce fc tm)
        = do tm' <- repSub tm
             pure (TForce fc tm')
    repSub tm = do empty <- clearDefs defs
                   quote empty env tm

export
replace : Defs -> Env Term vars ->
          (orig : NF vars) -> (new : Term vars) -> (tm : NF vars) ->
          Core (Term vars)
replace = replace' 0


