module TTImp.ProcessDecls

import Core.Context
import Core.Core
import Core.Env
import Core.UnifyState

import TTImp.ProcessData
import TTImp.ProcessDef
import TTImp.ProcessType
import TTImp.TTImp

processDecl : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              Env Term vars -> ImpDecl -> Core ()
processDecl env (IClaim fc rig vis opts ty) 
    = processType env fc rig vis opts ty
processDecl env (IData fc vis ddef) 
    = processData env fc vis ddef
processDecl env (IDef fc fname def) 
    = processDef env fc fname def
processDecl env (INamespace fc ns decls)
    = ?processNamespace

export
processDecls : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               Env Term vars -> List ImpDecl -> Core ()
processDecls env decls
    = do traverse (processDecl env) decls
         pure ()
