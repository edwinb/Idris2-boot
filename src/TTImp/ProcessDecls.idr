module TTImp.ProcessDecls

import Core.Context
import Core.Core
import Core.Env
import Core.UnifyState

import Parser.Support

import TTImp.Parser
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
               Env Term vars -> List ImpDecl -> Core Bool
processDecls env decls
    = do traverse (processDecl env) decls
         pure True -- TODO: False on error

export
processTTImpFile : {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   String -> Core Bool
processTTImpFile fname
    = do Right tti <- logTime "Parsing" $ coreLift $ parseFile fname
                            (do decls <- prog fname
                                eoi
                                pure decls)
               | Left err => do coreLift (putStrLn (show err))
                                pure False
         logTime "Elaboration" $
            catch (do processDecls [] tti
                      pure True)
                  (\err => do coreLift (printLn err)
                              pure False)
