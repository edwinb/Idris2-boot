module TTImp.Elab.Check
-- Interface (or, rather, type declaration) for the main checker function,
-- used by the checkers for each construct. Also some utility functions for
-- reading and writing elaboration state

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.Unify
import Core.UnifyState
import Core.TT
import Core.Value

import TTImp.TTImp

import Data.IntMap
import Data.NameMap

public export
data ElabMode = InType | InLHS RigCount | InExpr

-- Descriptions of implicit name bindings. They're either just the name,
-- or a binding of an @-pattern which has an associated pattern.
public export
data ImplBinding : List Name -> Type where
     NameBinding : (elabAs : Term vars) -> (expTy : Term vars) ->
                   ImplBinding vars
     AsBinding : (elabAs : Term vars) -> (expTy : Term vars) ->
                 (pat : Term vars) ->
                 ImplBinding vars

export
Show (ImplBinding vars) where
  show (NameBinding p ty) = show (p, ty)
  show (AsBinding p ty tm) = show (p, ty) ++ "@" ++ show tm

export
bindingMetas : ImplBinding vars -> NameMap ()
bindingMetas (NameBinding tm ty) = getMetas ty
bindingMetas (AsBinding tm ty pat) 
    = insertAll (toList (getMetas ty)) (getMetas pat)
  where
    insertAll : List (Name, ()) -> NameMap () -> NameMap ()
    insertAll [] ns = ns
    insertAll ((k, v) :: ks) ns = insert k v (insertAll ks ns)

-- Get the type of an implicit name binding
export
bindingType : ImplBinding vars -> Term vars
bindingType (NameBinding _ ty) = ty
bindingType (AsBinding _ ty _) = ty

-- Get the term (that is, the expanded thing it elaborates to, of the name
-- applied to the context) from an implicit binding
export
bindingTerm : ImplBinding vars -> Term vars
bindingTerm (NameBinding tm _) = tm
bindingTerm (AsBinding tm _ _) = tm

-- Current elaboration state (preserved/updated throughout elaboration)
public export
record EState (vars : List Name) where
  constructor MkEState
  -- The function/constructor name we're currently working on
  defining : Name
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
                  -- bound yet.
  bindIfUnsolved : List (Name, RigCount,
                          (vars' ** (Env Term vars', Term vars', Term vars', 
                                          SubVars outer vars'))) 
                  -- names to add as unbound implicits if they are still holes
                  -- when unbound implicits are added
  lhsPatVars : List String
                  -- names which we've bound in elab mode InLHS (i.e. not
                  -- in a dot pattern). We keep track of this because every
                  -- occurrence other than the first needs to be dotted
  allPatVars : List Name
                  -- Holes standing for pattern variables, which we'll delete
                  -- once we're done elaborating

export
data EST : Type where

export
initEStateSub : Name -> Env Term outer -> SubVars outer vars -> EState vars
initEStateSub n env sub = MkEState n env sub [] [] [] [] []

export
initEState : Name -> Env Term vars -> EState vars
initEState n env = initEStateSub n env SubRefl

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
                              (allPatVars est))
         pure eref
  where
    wknTms : (Name, ImplBinding vs) -> 
             (Name, ImplBinding (n :: vs))
    wknTms (f, NameBinding x y) = (f, NameBinding (weaken x) (weaken y))
    wknTms (f, AsBinding x y z)
        = (f, AsBinding (weaken x) (weaken y) (weaken z))

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
                        (allPatVars est))
  where
    dropSub : SubVars xs (y :: ys) -> Core (SubVars xs ys)
    dropSub (DropCons sub) = pure sub
    dropSub _ = throw (InternalError "Badly formed weakened environment")

    strTms : Defs -> (Name, ImplBinding (n :: vars)) -> 
             Core (Name, ImplBinding vars)
    strTms defs (f, NameBinding x y)
        = do xnf <- normaliseHoles defs env x
             ynf <- normaliseHoles defs env y
             case (shrinkTerm xnf (DropCons SubRefl), 
                   shrinkTerm ynf (DropCons SubRefl)) of
               (Just x', Just y') => pure (f, NameBinding x' y')
               _ => throw (GenericMsg fc ("Invalid unbound implicit " ++ 
                               show f ++ " " ++ show xnf ++ " : " ++ show ynf))
    strTms defs (f, AsBinding x y z)
        = do xnf <- normaliseHoles defs env x
             ynf <- normaliseHoles defs env y
             znf <- normaliseHoles defs env y
             case (shrinkTerm xnf (DropCons SubRefl), 
                   shrinkTerm ynf (DropCons SubRefl),
                   shrinkTerm znf (DropCons SubRefl)) of
               (Just x', Just y', Just z') => pure (f, AsBinding x' y' z')
               _ => throw (GenericMsg fc ("Invalid as binding " ++ 
                               show f ++ " " ++ show xnf ++ " : " ++ show ynf))

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
            List (Name, RigCount, (vars' ** (Env Term vars', Term vars', Term vars', SubVars new vars'))) ->
            EState vars -> EState vars
updateEnv env sub bif st
    = MkEState (defining st) env sub
               (boundNames st) (toBind st) bif
               (lhsPatVars st)
               (allPatVars st)

export
addBindIfUnsolved : Name -> RigCount -> Env Term vars -> Term vars -> Term vars ->
                    EState vars -> EState vars
addBindIfUnsolved hn r env tm ty st
    = MkEState (defining st)
               (outerEnv st) (subEnv st)
               (boundNames st) (toBind st) 
               ((hn, r, (_ ** (env, tm, ty, subEnv st))) :: bindIfUnsolved st)
               (lhsPatVars st)
               (allPatVars st)

clearBindIfUnsolved : EState vars -> EState vars
clearBindIfUnsolved st
    = MkEState (defining st)
               (outerEnv st) (subEnv st)
               (boundNames st) (toBind st) []
               (lhsPatVars st)
               (allPatVars st)

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
                ElabMode -> String -> Core ()
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
    = do (_, tm) <- newMeta fc rig env n ty
         pure tm

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
  level : Nat

export
initElabInfo : ElabMode -> ElabInfo
initElabInfo m = MkElabInfo m NONE 0

export
nextLevel : ElabInfo -> ElabInfo
nextLevel = record { level $= (+1) }

export
bindingVars : ElabInfo -> Bool
bindingVars e
    = case elabMode e of
           InExpr => False
           _ => True

export
tryError : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           Core a -> Core (Either Error a)
tryError elab
    = do ust <- get UST
         est <- get EST
         defs <- branch
         catch (do res <- elab
                   commit
                   pure (Right res))
               (\err => do put UST ust
                           put EST est
                           put Ctxt defs
                           pure (Left err))

export
try : {vars : _} ->
      {auto c : Ref Ctxt Defs} ->
      {auto u : Ref UST UState} ->
      {auto e : Ref EST (EState vars)} ->
      Core a -> Core a -> Core a
try elab1 elab2
    = do Right ok <- tryError elab1
               | Left err => elab2
         pure ok

-- Implemented in TTImp.Elab.Term; delaring just the type allows us to split
-- the elaborator over multiple files more easily
export
check : {vars : _} ->
        {auto c : Ref Ctxt Defs} ->
        {auto u : Ref UST UState} ->
        {auto e : Ref EST (EState vars)} ->
        RigCount -> ElabInfo -> Env Term vars -> RawImp -> 
        Maybe (Glued vars) ->
        Core (Term vars, Glued vars)

-- As above, but doesn't add any implicit lambdas, forces, delays, etc
export
checkImp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> ElabInfo -> Env Term vars -> RawImp -> Maybe (Glued vars) ->
           Core (Term vars, Glued vars)

-- Check whether two terms are convertible. May solve metavariables (in Ctxt)
-- in doing so.
-- Returns a list of constraints which need to be solved for the conversion
-- to work; if this is empty, the terms are convertible.
export
convert : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto e : Ref EST (EState vars)} ->
          FC -> ElabInfo -> Env Term vars -> Glued vars -> Glued vars ->
          Core (List Int)
convert fc elabinfo env x y
    = let umode : UnifyMode
                = case elabMode elabinfo of
                       InLHS _ => InLHS
                       _ => InTerm in
          catch (do vs <- unify umode fc env !(getNF x) !(getNF y)
                    when (holesSolved vs) $
                      solveConstraints umode Normal
                    pure (constraints vs))
                (\err => do xtm <- getTerm x
                            ytm <- getTerm y
                            -- See if we can improve the error message by
                            -- resolving any more constraints
                            catch (solveConstraints umode Normal)
                                  (\err => pure ())
                            throw (WhenUnifying fc env xtm ytm err))

-- Check whether the type we got for the given type matches the expected
-- type.
-- Returns the term and its type.
-- This may generate new constraints; if so, the term returned is a constant
-- guarded by the constraints which need to be solved.
export
checkExp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> ElabInfo -> Env Term vars -> FC ->
           (term : Term vars) -> 
           (got : Glued vars) -> (expected : Maybe (Glued vars)) -> 
           Core (Term vars, Glued vars)
checkExp rig elabinfo env fc tm got (Just exp) 
    = do constr <- convert fc elabinfo env got exp
         case constr of
              [] => pure (tm, got)
              cs => do defs <- get Ctxt
                       empty <- clearDefs defs
                       cty <- getTerm exp
                       ctm <- newConstant fc rig env tm cty cs
                       pure (ctm, exp)
checkExp rig elabinfo env fc tm got Nothing = pure (tm, got)
