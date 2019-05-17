module TTImp.Elab

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.UnifyState
import Core.Unify

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.Elab.Term
import TTImp.TTImp

getRigNeeded : ElabMode -> RigCount
getRigNeeded InType = Rig0 -- unrestricted usage in types
getRigNeeded (InLHS Rig0) = Rig0
getRigNeeded _ = Rig1

data ElabOpts
  = HolesOkay
  | InCase

Eq ElabOpts where
  HolesOkay == HolesOkay = True
  InCase == InCase = True
  _ == _ = False

export
elabTermSub : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              Int -> ElabMode -> 
              NestedNames vars -> Env Term vars ->
              Env Term inner -> SubVars inner vars ->
              RawImp -> Maybe (Glued vars) ->
              Core (Term vars, Glued vars)
elabTermSub defining mode nest env env' sub tm ty
    = do let incase = False -- TODO
         defs <- get Ctxt
         e <- newRef EST (initEStateSub defining env' sub)
         let rigc = getRigNeeded mode
         (chktm, chkty) <- check {e} rigc (initElabInfo mode) nest env tm ty
         -- Final retry of constraints and delayed elaborations
         -- - Solve any constraints, then retry any delayed elaborations
         -- - Finally, last attempts at solving constraints, but this
         --   is most likely just to be able to display helpful errors
         let solvemode = case mode of
                              InLHS _ => InLHS
                              _ => InTerm
         solveConstraints solvemode Normal
         solveConstraints solvemode Normal
         logTerm 5 "Looking for delayed in " chktm
         ust <- get UST
         catch (retryDelayed (delayedElab ust))
               (\err =>
                  do ust <- get UST
                     put UST (record { delayedElab = [] } ust)
                     throw err)
         -- As long as we're not in a case block, finish off constraint solving
         when (not incase) $
           -- resolve any default hints
           do solveConstraints solvemode Defaults
              -- perhaps resolving defaults helps...
              -- otherwise, this last go is most likely just to give us more
              -- helpful errors.
              solveConstraints solvemode LastChance

         when (not incase) $
           checkNoGuards -- all unification problems must now be solved
--          checkUserHoles True -- TODO on everything but types!
         pure (chktm, chkty)

export
elabTerm : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Int -> ElabMode -> 
           NestedNames vars -> Env Term vars ->
           RawImp -> Maybe (Glued vars) ->
           Core (Term vars, Glued vars)
elabTerm defining mode nest env tm ty
    = elabTermSub defining mode nest env env SubRefl tm ty

export
checkTermSub : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               Int -> ElabMode -> 
               NestedNames vars -> Env Term vars -> 
               Env Term inner -> SubVars inner vars ->
               RawImp -> Glued vars ->
               Core (Term vars)
checkTermSub defining mode nest env env' sub tm ty
    = do (tm_elab, _) <- elabTermSub defining mode nest env env' sub tm (Just ty)
         pure tm_elab

export
checkTerm : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Int -> ElabMode -> 
            NestedNames vars -> Env Term vars -> 
            RawImp -> Glued vars ->
            Core (Term vars)
checkTerm defining mode nest env tm ty
    = checkTermSub defining mode nest env env SubRefl tm ty
