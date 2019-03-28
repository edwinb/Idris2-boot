module TTImp.ProcessDecls

import Core.Context
import Core.Core
import Core.Env
import Core.UnifyState

import TTImp.Elab.Term
import TTImp.TTImp

processDecl : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              Env Term vars -> ImpDecl -> Core ()
processDecl env (IClaim fc rig vis opts ty) 
    = ?processDecl_rhs_1
processDecl env (IData fc vis ddef) = ?processDecl_rhs_2
processDecl env (IDef fc fname def) = ?processDecl_rhs_3

export
processDecls : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               Env Term vars -> List ImpDecl -> Core ()
processDecls env decls
    = do traverse (processDecl env) decls
         pure ()
