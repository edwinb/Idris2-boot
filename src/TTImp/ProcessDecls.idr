module TTImp.ProcessDecls

import Core.Context
import Core.Core
import Core.Env
import Core.UnifyState

import Parser.Support

import TTImp.Elab.Check
import TTImp.Parser
import TTImp.ProcessData
import TTImp.ProcessDef
import TTImp.ProcessType
import TTImp.TTImp

-- Implements processDecl, declared in TTImp.Elab.Check
process : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          NestedNames vars -> Env Term vars -> ImpDecl -> Core ()
process nest env (IClaim fc rig vis opts ty) 
    = processType nest env fc rig vis opts ty
process nest env (IData fc vis ddef) 
    = processData nest env fc vis ddef
process nest env (IDef fc fname def) 
    = processDef nest env fc fname def
process nest env (INamespace fc ns decls)
    = do oldns <- getNS
         extendNS (reverse ns)
         traverse (processDecl nest env) decls
         setNS oldns
process {c} nest env (IPragma act)
    = act c nest env
process nest env (ILog n)
    = setLogLevel n

TTImp.Elab.Check.processDecl = process

export
processDecls : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               NestedNames vars -> Env Term vars -> List ImpDecl -> Core Bool
processDecls nest env decls
    = do traverse (processDecl nest env) decls
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
            catch (do processDecls (MkNested []) [] tti
                      pure True)
                  (\err => do coreLift (printLn err)
                              pure False)
