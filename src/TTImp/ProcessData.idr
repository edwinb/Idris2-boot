module TTImp.ProcessType

import Core.Context
import Core.Core
import Core.Env
import Core.UnifyState

import TTImp.Elab.Term
import TTImp.TTImp

export
processData : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              Env Term vars -> FC -> Visibility ->
              ImpData -> Core ()
