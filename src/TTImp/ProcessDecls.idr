module TTImp.ProcessDecls

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.UnifyState

import Parser.Support

import TTImp.Elab.Check
import TTImp.Parser
import TTImp.ProcessData
import TTImp.ProcessDef
import TTImp.ProcessParams
import TTImp.ProcessRecord
import TTImp.ProcessType
import TTImp.TTImp

-- Implements processDecl, declared in TTImp.Elab.Check
process : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          List ElabOpt ->
          NestedNames vars -> Env Term vars -> ImpDecl -> Core ()
process eopts nest env (IClaim fc rig vis opts ty)
    = processType eopts nest env fc rig vis opts ty
process eopts nest env (IData fc vis ddef)
    = processData eopts nest env fc vis ddef
process eopts nest env (IDef fc fname def)
    = processDef eopts nest env fc fname def
process eopts nest env (IParameters fc ps decls)
    = processParams nest env fc ps decls
process eopts nest env (IRecord fc vis rec)
    = processRecord eopts nest env vis rec
process eopts nest env (INamespace fc nested ns decls)
    = do defs <- get Ctxt
         let cns = currentNS defs
         let nns = nestedNS defs
         extendNS (reverse ns)
         newns <- getNS
         traverse_ (processDecl eopts nest env) decls
         defs <- get Ctxt
         put Ctxt (record { currentNS = cns,
                            nestedNS = if nested
                                          then newns :: nns
                                          else nns } defs)
process eopts nest env (ITransform fc lhs rhs)
    = throw (GenericMsg fc "%transform not yet implemented")
process {c} eopts nest env (IPragma act)
    = act c nest env
process eopts nest env (ILog n)
    = setLogLevel n

TTImp.Elab.Check.processDecl = process

export
processDecls : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               NestedNames vars -> Env Term vars -> List ImpDecl -> Core Bool
processDecls nest env decls
    = do traverse_ (processDecl [] nest env) decls
         pure True -- TODO: False on error

export
processTTImpFile : {auto c : Ref Ctxt Defs} ->
                   {auto m : Ref MD Metadata} ->
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
                      Nothing <- checkDelayedHoles
                          | Just err => throw err
                      pure True)
                  (\err => do coreLift (printLn err)
                              pure False)
