module Core.Transform

import Core.Context
import Core.Env
import Core.TT

export
applyTransforms : {auto c : Ref Ctxt Defs} ->
                  Term vars -> Core (Term vars)
applyTransforms t = pure t -- TODO!
