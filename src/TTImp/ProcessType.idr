module TTImp.ProcessType

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState

import TTImp.Elab.Check
import TTImp.Elab
import TTImp.TTImp

export
processType : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              Env Term vars -> FC -> RigCount -> Visibility ->
              List FnOpt -> ImpTy -> Core ()
processType env fc rig vis opts (MkImpTy tfc n_in ty_raw)
    = do n <- inCurrentNS n_in
         log 5 $ "Checking type decl " ++ show n ++ " : " ++ show ty_raw
         (ty, _) <- elabTerm n InType env 
                             ty_raw (Just (gType fc))
         log 0 $ show n ++ " : " ++ show (abstractEnvType tfc env ty)
         -- TODO: Check name visibility
         let def = None -- TODO: External definitions

         addDef n (newDef fc rig (abstractEnvType tfc env ty) vis def)

         -- TODO: Interface hash and saving
         pure ()
