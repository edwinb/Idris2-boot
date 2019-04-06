module TTImp.ProcessDef

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.UnifyState

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.TTImp

export
processDef : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             Env Term vars -> FC ->
             Name -> RawImp -> Core ()
processDef env fc n_in tm_raw
    = do n <- inCurrentNS n_in
         defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (NoDeclaration fc n)
         let expty = gnf defs [] (type gdef)
         -- TODO: abstract env in tm_raw
         (tm, _) <- elabTerm n InExpr [] tm_raw (Just expty)
         logC 5 $ (do -- tm' <- normalise defs [] tm
                      pure (show n ++ " = " ++ show tm))
         addDef n (record { definition = Fn tm } gdef)
         pure ()
