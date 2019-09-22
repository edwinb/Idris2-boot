module TTImp.Elab.Utils

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

import TTImp.TTImp

findErasedFrom : Defs -> Nat -> NF [] -> Core (List Nat)
findErasedFrom defs pos (NBind fc x (Pi c _ _) scf)
    = do sc <- scf defs (toClosure defaultOpts [] (Erased fc))
         rest <- findErasedFrom defs (1 + pos) sc
         case c of
              Rig0 => pure (pos :: rest)
              _ => pure rest
findErasedFrom defs pos tm = pure []

-- Find the argument positions in the given type which are guaranteed to be
-- erasable
export
findErased : {auto c : Ref Ctxt Defs} ->
             ClosedTerm -> Core (List Nat)
findErased tm 
    = do defs <- get Ctxt
         tmnf <- nf defs [] tm
         findErasedFrom defs 0 tmnf

export
updateErasable : {auto c : Ref Ctxt Defs} ->
                 Name -> Core ()
updateErasable n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure ()
         es <- findErased (type gdef)
         addDef n (record { eraseArgs = es } gdef)
         pure ()
