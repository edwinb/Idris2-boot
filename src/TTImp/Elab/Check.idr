module TTImp.Elab.Check
-- Interface (or, rather, type declaration) for the main checker function,
-- used by the checkers for each construct. Also some utility functions

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.Unify
import Core.UnifyState
import Core.TT
import Core.Value

import TTImp.TTImp

public export
data ElabMode = InType | InLHS RigCount | InExpr

-- Current elaboration state (preserved/updated throughout elaboration)
public export
record EState (vars : List Name) where
  constructor MkEState
  nextVar : Int

export
data EST : Type where

weakenedEState : {auto e : Ref EST (EState vars)} ->
                 Core (Ref EST (EState (n :: vars)))
weakenedEState {e}
    = do est <- get EST
         eref <- newRef EST (MkEState (nextVar est))
         pure eref

strengthenedEState : Ref EST (EState (n :: vars)) ->
                     Core (EState vars)
strengthenedEState e
    = do est <- get EST
         pure (MkEState (nextVar est))

export
inScope : {auto e : Ref EST (EState vars)} ->
          (Ref EST (EState (n :: vars)) -> Core a) -> Core a
inScope {e} elab
    = do e' <- weakenedEState
         res <- elab e'
         st' <- strengthenedEState e'
         put {ref=e} EST st'
         pure res

-- Elaboration info (passed to recursive calls)
public export
record ElabInfo where
  constructor MkElabInfo
  elabMode : ElabMode
  level : Nat

export
nextLevel : ElabInfo -> ElabInfo
nextLevel = record { level $= (+1) }

export
getMVName : {auto e : Ref EST (EState vars)} ->
            Name -> Core Name
getMVName (UN n)
    = do est <- get EST
         put EST (record { nextVar $= (+1) } est)
         pure (MN n (nextVar est))
getMVName _
    = do est <- get EST
         put EST (record { nextVar $= (+1) } est)
         pure (MN "mv" (nextVar est))

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
          catch (do hs <- getHoles
                    vs <- unify umode fc env !(getNF x) !(getNF y)
                    hs' <- getHoles
                    when (isNil vs && length hs' < length hs) $
                      solveConstraints umode Normal
                    pure vs)
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
