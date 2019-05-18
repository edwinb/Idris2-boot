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

import Data.IntMap

getRigNeeded : ElabMode -> RigCount
getRigNeeded InType = Rig0 -- unrestricted usage in types
getRigNeeded (InLHS Rig0) = Rig0
getRigNeeded _ = Rig1

export
elabTermSub : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              Int -> ElabMode -> List ElabOpt ->
              NestedNames vars -> Env Term vars ->
              Env Term inner -> SubVars inner vars ->
              RawImp -> Maybe (Glued vars) ->
              Core (Term vars, Glued vars)
elabTermSub defining mode opts nest env env' sub tm ty
    = do let incase = elem InCase opts
         let holesokay = elem HolesOkay opts

         -- Record the current hole state; we only check the list of current
         -- holes is completely solved so this needs to be accurate.
         oldhs <- if not incase
                     then saveHoles
                     else pure empty

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

         -- on the LHS, all holes need to have been solved
         case mode of
              InLHS _ => checkUserHoles True
              -- elsewhere, all unification problems must be
              -- solved, though we defer that if it's a case block since we
              -- might learn a bit more later
              _ => when (not incase) $
                       checkNoGuards


         -- Put the current hole state back to what it was (minus anything 
         -- which has been solved in the meantime)
         when (not incase) $
           do hs <- getHoles
              restoreHoles (addHoles empty hs (toList oldhs))
         pure (chktm, chkty)
  where
    addHoles : (acc : IntMap (FC, Name)) -> 
               (allHoles : IntMap (FC, Name)) -> 
               List (Int, (FC, Name)) ->
               IntMap (FC, Name)
    addHoles acc allhs [] = acc
    addHoles acc allhs ((n, x) :: hs)
        = case lookup n allhs of
               Nothing => addHoles acc allhs hs
               Just _ => addHoles (insert n x acc) allhs hs

export
elabTerm : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Int -> ElabMode -> List ElabOpt ->
           NestedNames vars -> Env Term vars ->
           RawImp -> Maybe (Glued vars) ->
           Core (Term vars, Glued vars)
elabTerm defining mode opts nest env tm ty
    = elabTermSub defining mode opts nest env env SubRefl tm ty

export
checkTermSub : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               Int -> ElabMode -> List ElabOpt -> 
               NestedNames vars -> Env Term vars -> 
               Env Term inner -> SubVars inner vars ->
               RawImp -> Glued vars ->
               Core (Term vars)
checkTermSub defining mode opts nest env env' sub tm ty
    = do (tm_elab, _) <- elabTermSub defining mode opts nest 
                                     env env' sub tm (Just ty)
         pure tm_elab

export
checkTerm : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Int -> ElabMode -> List ElabOpt -> 
            NestedNames vars -> Env Term vars -> 
            RawImp -> Glued vars ->
            Core (Term vars)
checkTerm defining mode opts nest env tm ty
    = checkTermSub defining mode opts nest env env SubRefl tm ty
