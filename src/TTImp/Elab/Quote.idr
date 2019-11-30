module TTImp.Elab.Quote

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Reflect
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.Reflect
import TTImp.TTImp

%default covering

export
checkQuote : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto e : Ref EST (EState vars)} ->
             RigCount -> ElabInfo ->
             NestedNames vars -> Env Term vars ->
             FC -> RawImp -> Maybe (Glued vars) ->
             Core (Term vars, Glued vars)
checkQuote rig elabinfo nest env fc tm exp
    = do defs <- get Ctxt
         tm <- reflect fc defs env tm
         ty <- getCon fc defs (reflectionttimp "TTImp")
         checkExp rig elabinfo env fc tm (gnf env ty) exp
