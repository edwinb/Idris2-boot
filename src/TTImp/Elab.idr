module TTImp.Elab

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.UnifyState
import Core.Unify

import TTImp.Elab.Check
import TTImp.Elab.Term
import TTImp.TTImp

getRigNeeded : ElabMode -> RigCount
getRigNeeded InType = Rig0 -- unrestricted usage in types
getRigNeeded (InLHS Rig0) = Rig0
getRigNeeded _ = Rig1

export
elabTerm : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Name -> ElabMode -> 
           Env Term vars -> RawImp -> Maybe (Glued vars) ->
           Core (Term vars, Glued vars)
elabTerm defining mode env tm ty
    = do e <- newRef EST (initEState defining env)
         let rigc = getRigNeeded mode
         (chktm, chkty) <- check {e} rigc (initElabInfo mode) env tm ty
         -- Final retry of constraints and delayed elaborations
         -- - Solve any constraints, then retry any delayed elaborations
         -- - Finally, last attempts at solving constraints, but this
         --   is most likely just to be able to display helpful errors
         solveConstraints (case mode of
                                InLHS _ => InLHS
                                _ => InTerm) Normal
         solveConstraints (case mode of
                                InLHS _ => InLHS
                                _ => InTerm) LastChance
         checkNoGuards -- all unification problems must now be solved
         pure (chktm, chkty)

export
checkTerm : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Name -> ElabMode -> 
            Env Term vars -> RawImp -> Glued vars ->
            Core (Term vars)
checkTerm defining mode env tm ty
    = do (tm_elab, _) <- elabTerm defining mode env tm (Just ty)
         pure tm_elab
