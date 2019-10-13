module Idris.REPL

import Compiler.Scheme.Chez
import Compiler.Scheme.Chicken
import Compiler.Scheme.Racket
import Compiler.Common

import Core.AutoSearch
import Core.CaseTree
import Core.CompileExpr
import Core.Context
import Core.Env
import Core.InitPrimitives
import Core.LinearCheck
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.Termination
import Core.TT
import Core.Unify

import Idris.Desugar
import Idris.Error
import Idris.IDEMode.CaseSplit
import Idris.IDEMode.Commands
import Idris.IDEMode.MakeClause
import Idris.ModTree
import Idris.Parser
import Idris.Resugar
import public Idris.REPLCommon
import Idris.Syntax
import Idris.Version

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Interactive.CaseSplit
import TTImp.Interactive.ExprSearch
import TTImp.Interactive.GenerateDef
import TTImp.Interactive.MakeLemma
import TTImp.TTImp
import TTImp.ProcessDecls

import Control.Catchable
import Data.NameMap

import System

%default covering

showInfo : {auto c : Ref Ctxt Defs} ->
           (Name, Int, GlobalDef) -> Core ()
showInfo (n, idx, d)
    = do coreLift $ putStrLn (show (fullname d) ++ " ==> " ++
                              show !(toFullNames (definition d)))
         coreLift $ putStrLn (show (multiplicity d))
         coreLift $ putStrLn ("Erasable args: " ++ show (eraseArgs d))
         case compexpr d of
              Nothing => pure ()
              Just expr => coreLift $ putStrLn ("Compiled: " ++ show expr)
         coreLift $ putStrLn ("Refers to: " ++
                               show !(traverse getFullName (keys (refersTo d))))
         when (not (isNil (sizeChange d))) $
            let scinfo = map (\s => show (fnCall s) ++ ": " ++
                                    show (fnArgs s)) !(traverse toFullNames (sizeChange d)) in
                coreLift $ putStrLn $
                        "Size change: " ++ showSep ", " scinfo

isHole : GlobalDef -> Maybe Nat
isHole def
    = case definition def of
           Hole locs _ => Just locs
           _ => Nothing

showCount : RigCount -> String
showCount Rig0 = " 0 "
showCount Rig1 = " 1 "
showCount RigW = "   "

impBracket : Bool -> String -> String
impBracket False str = str
impBracket True str = "{" ++ str ++ "}"

showName : Name -> Bool
showName (UN "_") = False
showName (MN "_" _) = False
showName _ = True

tidy : Name -> String
tidy (MN n _) = n
tidy n = show n

showEnv : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Defs -> Env Term vars -> Name -> Nat -> Term vars ->
          Core (List (Name, String), String)
showEnv defs env fn (S args) (Bind fc x (Let c val ty) sc)
    = showEnv defs env fn args (subst val sc)
showEnv defs env fn (S args) (Bind fc x b sc)
    = do ity <- resugar env !(normalise defs env (binderType b))
         let pre = if showName x
                      then showCount (multiplicity b) ++
                           impBracket (implicitBind b) (tidy x ++ " : " ++ show ity) ++ "\n"
                      else ""
         (envstr, ret) <- showEnv defs (b :: env) fn args sc
         pure ((x, pre) :: envstr, ret)
  where
    implicitBind : Binder (Term vars) -> Bool
    implicitBind (Pi _ Explicit _) = False
    implicitBind (Pi _ _ _) = True
    implicitBind (Lam _ Explicit _) = False
    implicitBind (Lam _ _ _) = True
    implicitBind _ = False
showEnv defs env fn args ty
    = do ity <- resugar env !(normalise defs env ty)
         pure ([], "-------------------------------------\n" ++
                    nameRoot fn ++ " : " ++ show ity)

showHole : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           Defs -> Env Term vars -> Name -> Nat -> Term vars ->
           Core String
showHole gam env fn args ty
    = do (envs, ret) <- showEnv gam env fn args ty
         pp <- getPPrint
         let envs' = if showImplicits pp
                        then envs
                        else dropShadows envs
         pure (concat (map snd envs') ++ ret)
  where
    dropShadows : List (Name, a) -> List (Name, a)
    dropShadows [] = []
    dropShadows ((n, ty) :: ns)
        = if n `elem` map fst ns
             then dropShadows ns
             else (n, ty) :: dropShadows ns

displayType : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> (Name, Int, GlobalDef) ->
              Core String
displayType defs (n, i, gdef)
    = maybe (do tm <- resugar [] !(normaliseHoles defs [] (type gdef))
                pure (show (fullname gdef) ++ " : " ++ show tm))
            (\num => showHole defs [] n num (type gdef))
            (isHole gdef)

getEnvTerm : List Name -> Env Term vars -> Term vars ->
             (vars' ** (Env Term vars', Term vars'))
getEnvTerm (n :: ns) env (Bind fc x b sc)
    = if n == x
         then getEnvTerm ns (b :: env) sc
         else (_ ** (env, Bind fc x b sc))
getEnvTerm _ env tm = (_ ** (env, tm))

displayTerm : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> ClosedTerm ->
              Core String
displayTerm defs tm
    = do ptm <- resugar [] !(normaliseHoles defs [] tm)
         pure (show ptm)

displayPatTerm : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 Defs -> ClosedTerm ->
                 Core String
displayPatTerm defs tm
    = do ptm <- resugarNoPatvars [] !(normaliseHoles defs [] tm)
         pure (show ptm)

displayClause : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                Defs -> (vs ** (Env Term vs, Term vs, Term vs)) ->
                Core String
displayClause defs (vs ** (env, lhs, rhs))
    = do lhstm <- resugar env !(normaliseHoles defs env lhs)
         rhstm <- resugar env !(normaliseHoles defs env rhs)
         pure (show lhstm ++ " = " ++ show rhstm)

displayPats : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> (Name, Int, GlobalDef) ->
              Core String
displayPats defs (n, idx, gdef)
    = case definition gdef of
           PMDef _ _ _ _ pats
               => do ty <- displayType defs (n, idx, gdef)
                     ps <- traverse (displayClause defs) pats
                     pure (ty ++ "\n" ++ showSep "\n" ps)
           _ => pure (show n ++ " is not a pattern matching definition")

setOpt : {auto c : Ref Ctxt Defs} ->
         {auto o : Ref ROpts REPLOpts} ->
         REPLOpt -> Core ()
setOpt (ShowImplicits t)
    = do pp <- getPPrint
         setPPrint (record { showImplicits = t } pp)
setOpt (ShowNamespace t)
    = do pp <- getPPrint
         setPPrint (record { fullNamespace = t } pp)
setOpt (ShowTypes t)
    = do opts <- get ROpts
         put ROpts (record { showTypes = t } opts)
setOpt (EvalMode m)
    = do opts <- get ROpts
         put ROpts (record { evalMode = m } opts)
setOpt (Editor e)
    = do opts <- get ROpts
         put ROpts (record { editor = e } opts)
setOpt (CG e)
    = case getCG e of
           Just cg => setCG cg
           Nothing => iputStrLn "No such code generator available"

findCG : {auto c : Ref Ctxt Defs} -> Core Codegen
findCG
    = do defs <- get Ctxt
         case codegen (session (options defs)) of
              Chez => pure codegenChez
              Chicken => pure codegenChicken
              Racket => pure codegenRacket

anyAt : (FC -> Bool) -> FC -> a -> Bool
anyAt p loc y = p loc

printClause : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Nat -> ImpClause ->
              Core String
printClause i (PatClause _ lhsraw rhsraw)
    = do lhs <- pterm lhsraw
         rhs <- pterm rhsraw
         pure (pack (replicate i ' ') ++ show lhs ++ " = " ++ show rhs)
printClause i (WithClause _ lhsraw wvraw csraw)
    = do lhs <- pterm lhsraw
         wval <- pterm wvraw
         cs <- traverse (printClause (i + 2)) csraw
         pure (pack (replicate i ' ') ++ show lhs ++ " with (" ++ show wval ++ ")\n" ++
                 showSep "\n" cs)
printClause i (ImpossibleClause _ lhsraw)
    = do lhs <- pterm lhsraw
         pure (pack (replicate i ' ') ++ show lhs ++ " impossible")

lookupDefTyName : Name -> Context ->
                  Core (List (Name, Int, (Def, ClosedTerm)))
lookupDefTyName = lookupNameBy (\g => (definition g, type g))

public export
data EditResult : Type where
  DisplayEdit : List String -> EditResult
  EditError : String -> EditResult
  MadeLemma : Name -> PTerm -> String -> EditResult

processEdit : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto m : Ref MD Metadata} ->
              {auto o : Ref ROpts REPLOpts} ->
              EditCmd -> Core EditResult
processEdit (TypeAt line col name)
    = do defs <- get Ctxt
         glob <- lookupCtxtName name (gamma defs)
         res <- the (Core String) $ case glob of
                     [] => pure ""
                     ts => do tys <- traverse (displayType defs) ts
                              pure (showSep "\n" tys)
         Just (n, num, t) <- findTypeAt (\p, n => within (line-1, col-1) p)
            | Nothing => if res == ""
                            then throw (UndefinedName (MkFC "(interactive)" (0,0) (0,0)) name)
                            else pure (DisplayEdit [res])
         if res == ""
            then pure (DisplayEdit [ nameRoot n ++ " : " ++
                                       !(displayTerm defs t)])
            else pure (DisplayEdit [])  -- ? Why () This means there is a global name and a type at (line,col)
processEdit (CaseSplit line col name)
    = do let find = if col > 0
                       then within (line-1, col-1)
                       else onLine (line-1)
         OK splits <- getSplits (anyAt find) name
             | SplitFail err => pure (EditError (show err))
         lines <- updateCase splits (line-1) (col-1)
         pure $ DisplayEdit lines
processEdit (AddClause line name)
    = do Just c <- getClause line name
             | Nothing => pure (EditError (show name ++ " not defined here"))
         pure $ DisplayEdit [c]
processEdit (ExprSearch line name hints all)
    = do defs <- get Ctxt
         syn <- get Syn
         let brack = elemBy (\x, y => dropNS x == dropNS y) name (bracketholes syn)
         case !(lookupDefName name (gamma defs)) of
              [(n, nidx, Hole locs _)] =>
                  do tms <- exprSearch replFC name []
                     defs <- get Ctxt
                     restms <- traverse (normaliseHoles defs []) tms
                     itms <- the (Core (List PTerm))
                               (traverse (\tm =>
                                           do let (_ ** (env, tm')) = dropLams locs [] tm
                                              resugar env tm') restms)
                     if all
                        then pure $ DisplayEdit (map show itms)
                        else case itms of
                                  [] => pure $ EditError "No search results"
                                  (x :: xs) => pure $ DisplayEdit
                                                      [show (if brack
                                                            then addBracket replFC x
                                                            else x)]
              [] => pure $ EditError $ "Unknown name " ++ show name
              _ => pure $ EditError "Not a searchable hole"
  where
    dropLams : Nat -> Env Term vars -> Term vars ->
               (vars' ** (Env Term vars', Term vars'))
    dropLams Z env tm = (_ ** (env, tm))
    dropLams (S k) env (Bind _ _ b sc) = dropLams k (b :: env) sc
    dropLams _ env tm = (_ ** (env, tm))
processEdit (GenerateDef line name)
    = do defs <- get Ctxt
         Just (_, n', _, _) <- findTyDeclAt (\p, n => onLine line p)
             | Nothing => pure (EditError ("Can't find declaration for " ++ show name ++ " on line " ++ show line))
         case !(lookupDefExact n' (gamma defs)) of
              Just None =>
                  catch
                    (do Just (fc, cs) <- makeDef (\p, n => onLine line p) n'
                           | Nothing => processEdit (AddClause line name)
                        ls <- traverse (printClause (cast (snd (startPos fc)))) cs
                        pure $ DisplayEdit ls)
                    (\err => pure $ EditError $ "Can't find a definition for " ++ show n')
              Just _ => pure $ EditError "Already defined"
              Nothing => pure $ EditError $ "Can't find declaration for " ++ show name
processEdit (MakeLemma line name)
    = do defs <- get Ctxt
         syn <- get Syn
         let brack = elemBy (\x, y => dropNS x == dropNS y) name (bracketholes syn)
         case !(lookupDefTyName name (gamma defs)) of
              [(n, nidx, Hole locs _, ty)] =>
                  do (lty, lapp) <- makeLemma replFC name locs ty
                     pty <- pterm lty
                     papp <- pterm lapp
                     opts <- get ROpts
                     let pappstr = show (if brack
                                            then addBracket replFC papp
                                            else papp)
                     pure $ MadeLemma name pty pappstr
              _ => pure $ EditError "Can't make lifted definition"
processEdit (MakeCase line name)
    = pure $ EditError "Not implemented yet"
processEdit (MakeWith line name)
    = do Just l <- getSourceLine line
              | Nothing => pure (EditError "Source line not available")
         pure $ DisplayEdit [makeWith name l]

public export
data MissedResult : Type where
  CasesMissing : Name -> List String  -> MissedResult
  CallsNonCovering : Name -> List a -> MissedResult
  AllCasesCovered : Name -> MissedResult

public export
data REPLResult : Type where
  Done : REPLResult
  REPLError : String -> REPLResult
  Executed : PTerm -> REPLResult
  Evaluated : PTerm -> (Maybe PTerm) -> REPLResult
  Printed : List String -> REPLResult
  TermChecked : PTerm -> PTerm -> REPLResult
  FileLoaded : String -> REPLResult
  ErrorsLoadingFile : String -> List a -> REPLResult
  NoFileLoaded : REPLResult
  ChangedDirectory : String -> REPLResult
  CompilationFailed: REPLResult
  Compiled : String -> REPLResult
  ProofFound : PTerm -> REPLResult
  Missed : List MissedResult -> REPLResult
  CheckedTotal : List (Name, Totality) -> REPLResult
  FoundHoles : List Name -> REPLResult
  LogLevelSet : Nat -> REPLResult
  VersionIs : Version -> REPLResult
  Exited : REPLResult
  Edited : EditResult -> REPLResult

export
execExp : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref MD Metadata} ->
          PTerm -> Core REPLResult
execExp ctm
    = do ttimp <- desugar AnyExpr [] (PApp replFC (PRef replFC (UN "unsafePerformIO")) ctm)
         inidx <- resolveName (UN "[input]")
         (tm, ty) <- elabTerm inidx InExpr [] (MkNested [])
                                 [] ttimp Nothing
         tm_erased <- linearCheck replFC Rig1 True [] tm
         execute !findCG tm_erased
         pure $ Executed ctm


export
compileExp : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto m : Ref MD Metadata} ->
             {auto o : Ref ROpts REPLOpts} ->
             PTerm -> String -> Core REPLResult
compileExp ctm outfile
    = do inidx <- resolveName (UN "[input]")
         ttimp <- desugar AnyExpr [] (PApp replFC (PRef replFC (UN "unsafePerformIO")) ctm)
         (tm, gty) <- elabTerm inidx InExpr [] (MkNested [])
                               [] ttimp Nothing
         tm_erased <- linearCheck replFC Rig1 True [] tm
         ok <- compile !findCG tm_erased outfile
         maybe (pure CompilationFailed)
               (pure . Compiled)
               ok

export
loadMainFile : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref MD Metadata} ->
               {auto o : Ref ROpts REPLOpts} ->
               String -> Core REPLResult
loadMainFile f
    = do resetContext
         Right res <- coreLift (readFile f)
            | Left err => do setSource ""
                             pure (ErrorsLoadingFile f [err])
         errs <- buildDeps f
         updateErrorLine errs
         setSource res
         case errs of
           [] => pure (FileLoaded f)
           _ => pure (ErrorsLoadingFile f errs)


||| Process a single `REPLCmd`
|||
||| Returns `REPLResult` for display by the higher level shell which
||| is invoking this interactive command processing.
export
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref MD Metadata} ->
          {auto o : Ref ROpts REPLOpts} ->
          REPLCmd -> Core REPLResult
process (Eval itm)
    = do opts <- get ROpts
         case evalMode opts of
            Execute => do execExp itm; pure (Executed itm)
            _ =>
              do ttimp <- desugar AnyExpr [] itm
                 inidx <- resolveName (UN "[input]")
                 (tm, gty) <- elabTerm inidx (emode (evalMode opts)) [] (MkNested [])
                                       [] ttimp Nothing
                 defs <- get Ctxt
                 opts <- get ROpts
                 let norm = nfun (evalMode opts)
                 itm <- resugar [] !(norm defs [] tm)
                 if showTypes opts
                    then do ty <- getTerm gty
                            ity <- resugar [] !(norm defs [] ty)
                            pure (Evaluated itm (Just ity))
                    else pure (Evaluated itm Nothing)
  where
    emode : REPLEval -> ElabMode
    emode EvalTC = InType
    emode _ = InExpr

    nfun : REPLEval -> Defs -> Env Term vs -> Term vs -> Core (Term vs)
    nfun NormaliseAll = normaliseAll
    nfun _ = normalise
process (Check (PRef fc fn))
    = do defs <- get Ctxt
         case !(lookupCtxtName fn (gamma defs)) of
              [] => throw (UndefinedName fc fn)
              ts => do tys <- traverse (displayType defs) ts
                       pure (Printed tys)
process (Check itm)
    = do inidx <- resolveName (UN "[input]")
         ttimp <- desugar AnyExpr [] itm
         (tm, gty) <- elabTerm inidx InExpr [] (MkNested [])
                                  [] ttimp Nothing
         defs <- get Ctxt
         itm <- resugar [] !(normaliseHoles defs [] tm)
         ty <- getTerm gty
         ity <- resugar [] !(normaliseScope defs [] ty)
         pure (TermChecked itm ity)
process (PrintDef fn)
    = do defs <- get Ctxt
         case !(lookupCtxtName fn (gamma defs)) of
              [] => throw (UndefinedName replFC fn)
              ts => do defs <- traverse (displayPats defs) ts
                       pure (Printed defs)
process Reload
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => pure NoFileLoaded
              Just f => loadMainFile f
process (Load f)
    = do opts <- get ROpts
         put ROpts (record { mainfile = Just f } opts)
         -- Clear the context and load again
         loadMainFile f
process (CD dir)
    = do setWorkingDir dir
         pure (ChangedDirectory dir)
process Edit
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => pure NoFileLoaded
              Just f =>
                do let line = maybe "" (\i => " +" ++ show (i + 1)) (errorLine opts)
                   coreLift $ system (editor opts ++ " " ++ f ++ line)
                   loadMainFile f
process (Compile ctm outfile)
    = compileExp ctm outfile
process (Exec ctm)
    = execExp ctm
process (ProofSearch n_in)
    = do defs <- get Ctxt
         [(n, i, ty)] <- lookupTyName n_in (gamma defs)
              | [] => throw (UndefinedName replFC n_in)
              | ns => throw (AmbiguousName replFC (map fst ns))
         tm <- search replFC RigW False 1000 n ty []
         itm <- resugar [] !(normaliseHoles defs [] tm)
         pure $ ProofFound itm
process (Missing n)
    = do defs <- get Ctxt
         case !(lookupCtxtName n (gamma defs)) of
              [] => throw (UndefinedName replFC n)
              ts => map Missed $ traverse (\fn =>
                                         do tot <- getTotality replFC fn
                                            the (Core MissedResult) $ case isCovering tot of
                                                 MissingCases cs =>
                                                    do tms <- traverse (displayPatTerm defs) cs
                                                       pure $ CasesMissing fn tms
                                                 NonCoveringCall ns_in =>
                                                   do ns <- traverse getFullName ns_in
                                                      pure $ CallsNonCovering fn ns
                                                 _ => pure $ AllCasesCovered fn)
                               (map fst ts)
process (Total n)
    = do defs <- get Ctxt
         case !(lookupCtxtName n (gamma defs)) of
              [] => throw (UndefinedName replFC n)
              ts => map CheckedTotal $
                    traverse (\fn =>
                          do checkTotal replFC fn
                             tot <- getTotality replFC fn
                             pure $ (fn, tot))
                               (map fst ts)
process (DebugInfo n)
    = do defs <- get Ctxt
         traverse_ showInfo !(lookupCtxtName n (gamma defs))
         pure Done
process (SetOpt opt)
    = do setOpt opt
         pure Done
process (SetLog lvl)
    = do setLogLevel lvl
         pure $ LogLevelSet lvl
process Metavars
    = do ms <- getUserHoles
         pure $ FoundHoles ms
process (Editing cmd)
    = do ppopts <- getPPrint
         -- Since we're working in a local environment, don't do the usual
         -- thing of printing out the full environment for parameterised
         -- calls or calls in where blocks
         setPPrint (record { showFullEnv = False } ppopts)
         res <- processEdit cmd
         setPPrint ppopts
         pure $ Edited res
process Quit
    = pure Exited
process NOP
    = pure Done
process ShowVersion
    = pure $ VersionIs  version

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref MD Metadata} ->
               {auto o : Ref ROpts REPLOpts} ->
               REPLCmd -> Core REPLResult
processCatch cmd
    = do c' <- branch
         u' <- get UST
         s' <- get Syn
         o' <- get ROpts
         catch (do ust <- get UST
                   r <- process cmd
                   commit
                   pure r)
               (\err => do put Ctxt c'
                           put UST u'
                           put Syn s'
                           put ROpts o'
                           pure $ REPLError !(display err)
                           )

parseEmptyCmd : EmptyRule (Maybe REPLCmd)
parseEmptyCmd = eoi *> (pure Nothing)

parseCmd : EmptyRule (Maybe REPLCmd)
parseCmd = do c <- command; eoi; pure $ Just c

parseRepl : String -> Either ParseError (Maybe REPLCmd)
parseRepl inp
    = case fnameCmd [(":load ", Load), (":l ", Load), (":cd ", CD)] inp of
           Nothing => runParser inp (parseEmptyCmd <|> parseCmd)
           Just cmd => Right $ Just cmd
  where
    -- a right load of hackery - we can't tokenise the filename using the
    -- ordinary parser. There's probably a better way...
    getLoad : Nat -> (String -> REPLCmd) -> String -> Maybe REPLCmd
    getLoad n cmd str = Just (cmd (trim (substr n (length str) str)))

    fnameCmd : List (String, String -> REPLCmd) -> String -> Maybe REPLCmd
    fnameCmd [] inp = Nothing
    fnameCmd ((pre, cmd) :: rest) inp
        = if isPrefixOf pre inp
             then getLoad (length pre) cmd inp
             else fnameCmd rest inp

export
interpret : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto m : Ref MD Metadata} ->
            {auto o : Ref ROpts REPLOpts} ->
            String -> Core REPLResult
interpret inp
    = case parseRepl inp of
           Left err => pure $ REPLError (show err)
           Right Nothing => pure Done
           Right (Just cmd) => processCatch cmd

export
repl : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST UState} ->
       {auto s : Ref Syn SyntaxInfo} ->
       {auto m : Ref MD Metadata} ->
       {auto o : Ref ROpts REPLOpts} ->
       Core ()
repl
    = do ns <- getNS
         opts <- get ROpts
         coreLift (putStr (prompt (evalMode opts) ++ showSep "." (reverse ns) ++ "> "))
         inp <- coreLift getLine
         repeat <- interpret inp
         end <- coreLift $ fEOF stdin
         if repeat && not end
           then repl
           else
             do iputStrLn "Bye for now!"
                pure ()

  where
    prompt : REPLEval -> String
    prompt EvalTC = "[tc] "
    prompt NormaliseAll = ""
    prompt Execute = "[exec] "
