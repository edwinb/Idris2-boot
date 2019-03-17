module TTImp.ProcessDecls

import Core.Context
import Core.Core

import TTImp.Elab.Term
import TTImp.TTImp

export
processDecl : {auto c : Ref Ctxt Defs} ->
              ImpDecl -> Core ()
