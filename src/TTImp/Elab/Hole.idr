module TTImp.Elab.As

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.TTImp

%default covering

export
checkHole : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            RigCount -> ElabInfo ->
            NestedNames vars -> Env Term vars -> 
            FC -> String -> Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
checkHole rig elabinfo nest env fc n_in (Just gexpty)
    = do nm <- inCurrentNS (UN n_in)
         expty <- getTerm gexpty
         metaval <- metaVar fc rig env nm expty
         pure (metaval, gexpty)
checkHole rig elabinfo nest env fc n_in exp
    = do nmty <- genName "holeTy"
         ty <- metaVar fc Rig0 env nmty (TType fc)
         nm <- inCurrentNS (UN n_in)
         metaval <- metaVar fc rig env nm ty
         pure (metaval, gnf env ty)
