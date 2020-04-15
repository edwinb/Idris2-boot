module TTImp.Elab.Check
-- Interface (or, rather, type declaration) for the main checker function,
-- used by the checkers for each construct. Also some utility functions for
-- reading and writing elaboration state

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.UnifyState
import Core.TT
import Core.Value

import TTImp.TTImp

import Data.IntMap
import Data.NameMap
import Data.StringMap

public export
data ElabMode = InType | InLHS RigCount | InExpr

Show ElabMode where
  show InType = "InType"
  show (InLHS c) = "InLHS " ++ show c
  show InExpr = "InExpr"

public export
data ElabOpt
  = HolesOkay
  | InCase

public export
Eq ElabOpt where
  HolesOkay == HolesOkay = True
  InCase == InCase = True
  _ == _ = False

-- Descriptions of implicit name bindings. They're either just the name,
-- or a binding of an @-pattern which has an associated pattern.
public export
data ImplBinding : List Name -> Type where
     NameBinding : RigCount -> PiInfo (Term vars) -> (elabAs : Term vars) -> (expTy : Term vars) ->
                   ImplBinding vars
     AsBinding : RigCount -> PiInfo (Term vars) -> (elabAs : Term vars) -> (expTy : Term vars) ->
                 (pat : Term vars) ->
                 ImplBinding vars

export
Show (ImplBinding vars) where
  show (NameBinding c p tm ty) = show (tm, ty)
  show (AsBinding c p tm ty pat) = show (tm, ty) ++ "@" ++ show tm

export
bindingMetas : ImplBinding vars -> NameMap Bool
bindingMetas (NameBinding c p tm ty) = getMetas ty
bindingMetas (AsBinding c p tm ty pat)
    = insertAll (toList (getMetas ty)) (getMetas pat)
  where
    insertAll : List (Name, Bool) -> NameMap Bool -> NameMap Bool
    insertAll [] ns = ns
    insertAll ((k, v) :: ks) ns = insert k v (insertAll ks ns)

-- Get the type of an implicit name binding
export
bindingType : ImplBinding vars -> Term vars
bindingType (NameBinding _ _ _ ty) = ty
bindingType (AsBinding _ _ _ ty _) = ty

-- Get the term (that is, the expanded thing it elaborates to, of the name
-- applied to the context) from an implicit binding
export
bindingTerm : ImplBinding vars -> Term vars
bindingTerm (NameBinding _ _ tm _) = tm
bindingTerm (AsBinding _ _ tm _ _) = tm

export
bindingRig : ImplBinding vars -> RigCount
bindingRig (NameBinding c _ _ _) = c
bindingRig (AsBinding c _ _ _ _) = c

export
bindingPiInfo : ImplBinding vars -> PiInfo (Term vars)
bindingPiInfo (NameBinding _ p _ _) = p
bindingPiInfo (AsBinding _ p _ _ _) = p

-- Current elaboration state (preserved/updated throughout elaboration)
public export
record EState (vars : List Name) where
  constructor MkEState
  -- The function/constructor name we're currently working on (resolved id)
  defining : Int
  -- The outer environment in which we're running the elaborator. Things here should
  -- be considered parametric as far as case expression elaboration goes, and are
  -- the only things that unbound implicits can depend on
  outerEnv : Env Term outer
  subEnv : SubVars outer vars
  boundNames : List (Name, ImplBinding vars)
                  -- implicit pattern/type variable bindings and the
                  -- term/type they elaborated to
  toBind : List (Name, ImplBinding vars)
                  -- implicit pattern/type variables which haven't been
                  -- bound yet. Record how they're bound (auto-implicit bound
                  -- pattern vars need to be dealt with in with-application on
                  -- the RHS)
  bindIfUnsolved : List (Name, RigCount,
                          (vars' ** (Env Term vars', PiInfo (Term vars'),
                                     Term vars', Term vars', SubVars outer vars')))
                  -- names to add as unbound implicits if they are still holes
                  -- when unbound implicits are added
  lhsPatVars : List Name
                  -- names which we've bound in elab mode InLHS (i.e. not
                  -- in a dot pattern). We keep track of this because every
                  -- occurrence other than the first needs to be dotted
  allPatVars : List Name
                  -- Holes standing for pattern variables, which we'll delete
                  -- once we're done elaborating
  allowDelay : Bool -- Delaying elaborators is okay. We can't nest delays.
  linearUsed : List (Var vars)
  saveHoles : NameMap () -- things we'll need to save to TTC, even if solved

export
data EST : Type where

export
initEStateSub : Int -> Env Term outer -> SubVars outer vars -> EState vars
initEStateSub n env sub = MkEState n env sub [] [] [] [] [] True [] empty

export
initEState : Int -> Env Term vars -> EState vars
initEState n env = initEStateSub n env SubRefl

export
saveHole : {auto e : Ref EST (EState vars)} ->
           Name -> Core ()
saveHole n
    = do est <- get EST
         put EST (record { saveHoles $= insert n () } est)

weakenedEState : {auto e : Ref EST (EState vars)} ->
                 Core (Ref EST (EState (n :: vars)))
weakenedEState {e}
    = do est <- get EST
         eref <- newRef EST
                    (MkEState (defining est)
                              (outerEnv est)
                              (DropCons (subEnv est))
                              (map wknTms (boundNames est))
                              (map wknTms (toBind est))
                              (bindIfUnsolved est)
                              (lhsPatVars est)
                              (allPatVars est)
                              (allowDelay est)
                              (map weaken (linearUsed est))
                              (saveHoles est))
         pure eref
  where
    wknTms : (Name, ImplBinding vs) ->
             (Name, ImplBinding (n :: vs))
    wknTms (f, NameBinding c p x y)
        = (f, NameBinding c (map weaken p) (weaken x) (weaken y))
    wknTms (f, AsBinding c p x y z)
        = (f, AsBinding c (map weaken p) (weaken x) (weaken y) (weaken z))

strengthenedEState : Ref Ctxt Defs ->
                     Ref EST (EState (n :: vars)) ->
                     FC -> Env Term (n :: vars) ->
                     Core (EState vars)
strengthenedEState {n} {vars} c e fc env
    = do est <- get EST
         defs <- get Ctxt
         svs <- dropSub (subEnv est)
         bns <- traverse (strTms defs) (boundNames est)
         todo <- traverse (strTms defs) (toBind est)

         pure (MkEState (defining est)
                        (outerEnv est)
                        svs
                        bns
                        todo
                        (bindIfUnsolved est)
                        (lhsPatVars est)
                        (allPatVars est)
                        (allowDelay est)
                        (mapMaybe dropTop (linearUsed est))
                        (saveHoles est))
  where
    dropSub : SubVars xs (y :: ys) -> Core (SubVars xs ys)
    dropSub (DropCons sub) = pure sub
    dropSub _ = throw (InternalError "Badly formed weakened environment")

    -- This helps persuade the erasure checker that it can erase IsVar,
    -- because there's no matching on it in removeArgVars below.
    dropLater : IsVar name (S idx) (v :: vs) -> IsVar name idx vs
    dropLater (Later p) = p

    -- Remove any instance of the top level local variable from an
    -- application. Fail if it turns out to be necessary.
    -- NOTE: While this isn't strictly correct given the type of the hole
    -- which stands for the unbound implicits, it's harmless because we
    -- never actualy *use* that hole - this process is only to ensure that the
    -- unbound implicit doesn't depend on any variables it doesn't have
    -- in scope.
    removeArgVars : List (Term (n :: vs)) -> Maybe (List (Term vs))
    removeArgVars [] = pure []
    removeArgVars (Local fc r (S k) p :: args)
        = do args' <- removeArgVars args
             pure (Local fc r _ (dropLater p) :: args')
    removeArgVars (Local fc r Z p :: args)
        = removeArgVars args
    removeArgVars (a :: args)
        = do a' <- shrinkTerm a (DropCons SubRefl)
             args' <- removeArgVars args
             pure (a' :: args')

    removeArg : Term (n :: vs) -> Maybe (Term vs)
    removeArg tm
        = case getFnArgs tm of
               (f, args) =>
                   do args' <- removeArgVars args
                      f' <- shrinkTerm f (DropCons SubRefl)
                      pure (apply (getLoc f) f' args')

    strTms : Defs -> (Name, ImplBinding (n :: vars)) ->
             Core (Name, ImplBinding vars)
    strTms defs (f, NameBinding c p x y)
        = do xnf <- normaliseHoles defs env x
             ynf <- normaliseHoles defs env y
             case (shrinkPi p (DropCons SubRefl),
                   removeArg xnf,
                   shrinkTerm ynf (DropCons SubRefl)) of
               (Just p', Just x', Just y') =>
                    pure (f, NameBinding c p' x' y')
               _ => throw (BadUnboundImplicit fc env f y)
    strTms defs (f, AsBinding c p x y z)
        = do xnf <- normaliseHoles defs env x
             ynf <- normaliseHoles defs env y
             znf <- normaliseHoles defs env z
             case (shrinkPi p (DropCons SubRefl),
                   shrinkTerm xnf (DropCons SubRefl),
                   shrinkTerm ynf (DropCons SubRefl),
                   shrinkTerm znf (DropCons SubRefl)) of
               (Just p', Just x', Just y', Just z') =>
                    pure (f, AsBinding c p' x' y' z')
               _ => throw (BadUnboundImplicit fc env f y)

    dropTop : (Var (n :: vs)) -> Maybe (Var vs)
    dropTop (MkVar First) = Nothing
    dropTop (MkVar (Later p)) = Just (MkVar p)

export
inScope : {auto c : Ref Ctxt Defs} ->
          {auto e : Ref EST (EState vars)} ->
          FC -> Env Term (n :: vars) ->
          (Ref EST (EState (n :: vars)) -> Core a) ->
          Core a
inScope {c} {e} fc env elab
    = do e' <- weakenedEState
         res <- elab e'
         st' <- strengthenedEState c e' fc env
         put {ref=e} EST st'
         pure res

export
updateEnv : Env Term new -> SubVars new vars ->
            List (Name, RigCount,
                   (vars' ** (Env Term vars', PiInfo (Term vars'),
                              Term vars', Term vars', SubVars new vars'))) ->
            EState vars -> EState vars
updateEnv env sub bif st
    = MkEState (defining st) env sub
               (boundNames st) (toBind st) bif
               (lhsPatVars st)
               (allPatVars st)
               (allowDelay st)
               (linearUsed st)
               (saveHoles st)

export
addBindIfUnsolved : Name -> RigCount -> PiInfo (Term vars) ->
                    Env Term vars -> Term vars -> Term vars ->
                    EState vars -> EState vars
addBindIfUnsolved hn r p env tm ty st
    = MkEState (defining st)
               (outerEnv st) (subEnv st)
               (boundNames st) (toBind st)
               ((hn, r, (_ ** (env, p, tm, ty, subEnv st))) :: bindIfUnsolved st)
               (lhsPatVars st)
               (allPatVars st)
               (allowDelay st)
               (linearUsed st)
               (saveHoles st)

clearBindIfUnsolved : EState vars -> EState vars
clearBindIfUnsolved st
    = MkEState (defining st)
               (outerEnv st) (subEnv st)
               (boundNames st) (toBind st) []
               (lhsPatVars st)
               (allPatVars st)
               (allowDelay st)
               (linearUsed st)
               (saveHoles st)

-- Clear the 'toBind' list, except for the names given
export
clearToBind : {auto e : Ref EST (EState vars)} ->
              (excepts : List Name) -> Core ()
clearToBind excepts
    = do est <- get EST
         put EST (record { toBind $= filter (\x => fst x `elem` excepts) }
                         (clearBindIfUnsolved est))

export
noteLHSPatVar : {auto e : Ref EST (EState vars)} ->
                ElabMode -> Name -> Core ()
noteLHSPatVar (InLHS _) n
    = do est <- get EST
         put EST (record { lhsPatVars $= (n ::) } est)
noteLHSPatVar _ _ = pure ()

export
notePatVar : {auto e : Ref EST (EState vars)} ->
             Name -> Core ()
notePatVar n
    = do est <- get EST
         put EST (record { allPatVars $= (n ::) } est)

export
metaVar : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          FC -> RigCount ->
          Env Term vars -> Name -> Term vars -> Core (Term vars)
metaVar fc rig env n ty
    = do (_, tm) <- newMeta fc rig env n ty (Hole (length env) False) True
         pure tm

export
implBindVar : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount ->
              Env Term vars -> Name -> Term vars -> Core (Term vars)
implBindVar fc rig env n ty
    = do (_, tm) <- newMeta fc rig env n ty (Hole (length env) True) True
         pure tm

export
metaVarI : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          FC -> RigCount ->
          Env Term vars -> Name -> Term vars -> Core (Int, Term vars)
metaVarI fc rig env n ty
    = newMeta fc rig env n ty (Hole (length env) False) True

export
argVar : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         FC -> RigCount ->
         Env Term vars -> Name -> Term vars -> Core (Int, Term vars)
argVar fc rig env n ty
    = newMetaLets fc rig env n ty (Hole (length env) False) False True

export
searchVar : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            FC -> RigCount -> Nat -> Name ->
            Env Term vars -> Name -> Term vars -> Core (Term vars)
searchVar fc rig depth def env n ty
    = do (_, tm) <- newSearch fc rig depth def env n ty
         pure tm

-- Elaboration info (passed to recursive calls)
public export
record ElabInfo where
  constructor MkElabInfo
  elabMode : ElabMode
  implicitMode : BindMode
  topLevel : Bool
  bindingVars : Bool
  preciseInf : Bool -- are types inferred precisely (True) or do we generalise
                    -- pi bindings to RigW (False, default)
  ambigTries : List Name

export
initElabInfo : ElabMode -> ElabInfo
initElabInfo m = MkElabInfo m NONE False True False []

export
tryError : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           Core a -> Core (Either Error a)
tryError elab
    = do ust <- get UST
         est <- get EST
         md <- get MD
         defs <- branch
         catch (do res <- elab
                   commit
                   pure (Right res))
               (\err => do put UST ust
                           put EST est
                           put MD md
                           defs' <- get Ctxt
                           put Ctxt (record { timings = timings defs' } defs)
                           pure (Left err))

export
try : {vars : _} ->
      {auto c : Ref Ctxt Defs} ->
      {auto m : Ref MD Metadata} ->
      {auto u : Ref UST UState} ->
      {auto e : Ref EST (EState vars)} ->
      Core a -> Core a -> Core a
try elab1 elab2
    = do Right ok <- tryError elab1
               | Left err => elab2
         pure ok

export
handle : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         {auto m : Ref MD Metadata} ->
         {auto u : Ref UST UState} ->
         {auto e : Ref EST (EState vars)} ->
         Core a -> (Error -> Core a) -> Core a
handle elab1 elab2
    = do Right ok <- tryError elab1
               | Left err => elab2 err
         pure ok

successful : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto e : Ref EST (EState vars)} ->
             Bool -> -- constraints allowed
             List (Maybe Name, Core a) ->
             Core (List (Either (Maybe Name, Error)
                                (Nat, a, Defs, UState, EState vars)))
successful allowCons [] = pure []
successful allowCons ((tm, elab) :: elabs)
    = do ust <- get UST
         let ncons = if allowCons
                        then 0
                        else length (toList (guesses ust))
         est <- get EST
         md <- get MD
         defs <- branch
         catch (do -- Run the elaborator
                   logC 5 $ do tm' <- maybe (pure (UN "__"))
                                            toFullNames tm
                               pure ("Running " ++ show tm')
                   res <- elab
                   -- Record post-elaborator state
                   ust' <- get UST
                   let ncons' = if allowCons
                                   then 0
                                   else length (toList (guesses ust'))

                   est' <- get EST
                   md' <- get MD
                   defs' <- get Ctxt

                   -- Reset to previous state and try the rest
                   put UST ust
                   put EST est
                   put MD md
                   put Ctxt defs
                   logC 5 $ do tm' <- maybe (pure (UN "__"))
                                            toFullNames tm
                               pure ("Success " ++ show tm' ++
                                     " (" ++ show ncons' ++ " - "
                                          ++ show ncons ++ ")")
                   elabs' <- successful allowCons elabs
                   -- Record success, and the state we ended at
                   pure (Right (minus ncons' ncons,
                                res, defs', ust', est') :: elabs'))
               (\err => do put UST ust
                           put EST est
                           put MD md
                           put Ctxt defs
                           elabs' <- successful allowCons elabs
                           pure (Left (tm, !(normaliseErr err)) :: elabs'))

export
exactlyOne' : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              Bool -> FC -> Env Term vars ->
              List (Maybe Name, Core (Term vars, Glued vars)) ->
              Core (Term vars, Glued vars)
exactlyOne' allowCons fc env [(tm, elab)] = elab
exactlyOne' {vars} allowCons fc env all
    = do elabs <- successful allowCons all
         case getRight elabs of
              Right (res, defs, ust, est) =>
                    do put UST ust
                       put EST est
                       put Ctxt defs
                       commit
                       pure res
              Left rs => throw (altError (lefts elabs) rs)
  where
    getRight : List (Either err (Nat, res)) -> Either (List res) res
    getRight es
        = case rights es of
               [(_, res)] => Right res
               rs => case filter (\x => fst x == Z) rs of
                          [(_, res)] => Right res
                          _ => Left (map snd rs)

    getRes : ((Term vars, Glued vars), st) -> Term vars
    getRes ((tm, _), thisst) = tm

    getDepthError : Error -> Maybe Error
    getDepthError e@(AmbiguityTooDeep _ _ _) = Just e
    getDepthError _ = Nothing

    depthError : List (Maybe Name, Error) -> Maybe Error
    depthError [] = Nothing
    depthError ((_, e) :: es)
        = maybe (depthError es) Just (getDepthError e)

    -- If they've all failed, collect all the errors
    -- If more than one succeeded, report the ambiguity
    altError : List (Maybe Name, Error) ->
               List ((Term vars, Glued vars), st) ->
               Error
    altError ls []
        = case depthError ls of
               Nothing => AllFailed ls
               Just err => err
    altError ls rs = AmbiguousElab fc env (map getRes rs)

export
exactlyOne : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto e : Ref EST (EState vars)} ->
             FC -> Env Term vars ->
             List (Maybe Name, Core (Term vars, Glued vars)) ->
             Core (Term vars, Glued vars)
exactlyOne = exactlyOne' True

export
anyOne : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         {auto m : Ref MD Metadata} ->
         {auto u : Ref UST UState} ->
         {auto e : Ref EST (EState vars)} ->
         FC -> List (Maybe Name, Core (Term vars, Glued vars)) ->
         Core (Term vars, Glued vars)
anyOne fc [] = throw (GenericMsg fc "No elaborators provided")
anyOne fc [(tm, elab)] = elab
anyOne fc ((tm, elab) :: es) = try elab (anyOne fc es)

-- Implemented in TTImp.Elab.Term; delaring just the type allows us to split
-- the elaborator over multiple files more easily
export
check : {vars : _} ->
        {auto c : Ref Ctxt Defs} ->
        {auto m : Ref MD Metadata} ->
        {auto u : Ref UST UState} ->
        {auto e : Ref EST (EState vars)} ->
        RigCount -> ElabInfo ->
        NestedNames vars -> Env Term vars -> RawImp ->
        Maybe (Glued vars) ->
        Core (Term vars, Glued vars)

-- As above, but doesn't add any implicit lambdas, forces, delays, etc
export
checkImp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> ElabInfo ->
           NestedNames vars -> Env Term vars -> RawImp -> Maybe (Glued vars) ->
           Core (Term vars, Glued vars)

-- Implemented in TTImp.ProcessDecls
export
processDecl : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              List ElabOpt -> NestedNames vars ->
              Env Term vars -> ImpDecl -> Core ()

-- Check whether two terms are convertible. May solve metavariables (in Ctxt)
-- in doing so.
-- Returns a list of constraints which need to be solved for the conversion
-- to work; if this is empty, the terms are convertible.
convertWithLazy
        : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto e : Ref EST (EState vars)} ->
          (withLazy : Bool) -> (precise : Bool) ->
          FC -> ElabInfo -> Env Term vars -> Glued vars -> Glued vars ->
          Core UnifyResult
convertWithLazy withLazy prec fc elabinfo env x y
    = let umode : UnifyInfo
                = case elabMode elabinfo of
                       InLHS _ => inLHS
                       _ => inTermP prec in
          catch
            (do let lazy = !isLazyActive && withLazy
                logGlueNF 5 ("Unifying " ++ show withLazy ++ " "
                             ++ show (elabMode elabinfo)) env x
                logGlueNF 5 "....with" env y
                vs <- if isFromTerm x && isFromTerm y
                         then do xtm <- getTerm x
                                 ytm <- getTerm y
                                 if lazy
                                    then unifyWithLazy umode fc env xtm ytm
                                    else unify umode fc env xtm ytm
                         else do xnf <- getNF x
                                 ynf <- getNF y
                                 if lazy
                                    then unifyWithLazy umode fc env xnf ynf
                                    else unify umode fc env xnf ynf
                when (holesSolved vs) $
                    solveConstraints umode Normal
                pure vs)
            (\err =>
               do defs <- get Ctxt
                  xtm <- getTerm x
                  ytm <- getTerm y
                  -- See if we can improve the error message by
                  -- resolving any more constraints
                  catch (solveConstraints umode Normal)
                        (\err => pure ())
                  -- We need to normalise the known holes before
                  -- throwing because they may no longer be known
                  -- by the time we look at the error
                  defs <- get Ctxt
                  throw !(normaliseErr (WhenUnifying fc env xtm ytm err)))

export
convert : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto e : Ref EST (EState vars)} ->
          FC -> ElabInfo -> Env Term vars -> Glued vars -> Glued vars ->
          Core UnifyResult
convert = convertWithLazy False False

export
convertP : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           (precise : Bool) ->
           FC -> ElabInfo -> Env Term vars -> Glued vars -> Glued vars ->
           Core UnifyResult
convertP = convertWithLazy False

-- Check whether the type we got for the given type matches the expected
-- type.
-- Returns the term and its type.
-- This may generate new constraints; if so, the term returned is a constant
-- guarded by the constraints which need to be solved.
export
checkExpP : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            RigCount -> (precise : Bool) -> ElabInfo -> Env Term vars -> FC ->
            (term : Term vars) ->
            (got : Glued vars) -> (expected : Maybe (Glued vars)) ->
            Core (Term vars, Glued vars)
checkExpP rig prec elabinfo env fc tm got (Just exp)
    = do vs <- convertWithLazy True prec fc elabinfo env got exp
         case (constraints vs) of
              [] => case addLazy vs of
                         NoLazy => do logTerm 5 "Solved" tm
                                      pure (tm, got)
                         AddForce r => do logTerm 5 "Force" tm
                                          logGlue 5 "Got" env got
                                          logGlue 5 "Exp" env exp
                                          pure (TForce fc r tm, exp)
                         AddDelay r => do ty <- getTerm got
                                          logTerm 5 "Delay" tm
                                          pure (TDelay fc r ty tm, exp)
              cs => do logTerm 5 "Not solved" tm
                       defs <- get Ctxt
                       empty <- clearDefs defs
                       cty <- getTerm exp
                       ctm <- newConstant fc rig env tm cty cs
                       dumpConstraints 5 False
                       case addLazy vs of
                            NoLazy => pure (ctm, got)
                            AddForce r => pure (TForce fc r tm, exp)
                            AddDelay r => do ty <- getTerm got
                                             pure (TDelay fc r ty tm, exp)
checkExpP rig prec elabinfo env fc tm got Nothing = pure (tm, got)

export
checkExp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> ElabInfo -> Env Term vars -> FC ->
           (term : Term vars) ->
           (got : Glued vars) -> (expected : Maybe (Glued vars)) ->
           Core (Term vars, Glued vars)
checkExp rig elabinfo = checkExpP rig (preciseInf elabinfo) elabinfo
