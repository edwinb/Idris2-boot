module TTImp.Elab

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.UnifyState

import TTImp.Elab.Check
import TTImp.TTImp

getRigNeeded : ElabMode -> RigCount
getRigNeeded InType = Rig0 -- unrestricted usage in types
getRigNeeded (InLHS Rig0) = Rig0
getRigNeeded _ = Rig1

export
elabTerm : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Name -> ElabMode -> Env Term vars -> RawImp -> Maybe (Glued vars) ->
           Core (Term vars, Glued vars)
elabTerm defining mode env tm ty
    = do e <- newRef EST (initEState defining)
         let rigc = getRigNeeded mode
         check {e} rigc (initElabInfo mode) env tm ty
