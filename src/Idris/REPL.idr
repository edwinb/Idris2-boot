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
                              show (definition d))
         case compexpr d of
              Nothing => pure ()
              Just expr => coreLift $ putStrLn ("Compiled: " ++ show expr)
         coreLift $ putStrLn ("Refers to: " ++ 
                               show !(traverse getFullName (keys (refersTo d))))
         when (not (isNil (sizeChange d))) $ 
            let scinfo = map (\s => show (fnCall s) ++ ": " ++ 
                                    show (fnArgs s)) (sizeChange d) in
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
    = do ity <- resugar env !(normaliseHoles defs env (binderType b))
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
    = do ity <- resugar env !(normaliseHoles defs env ty)
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
           PMDef _ _ _ pats
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
           Nothing => coreLift $ putStrLn "No such code generator available"

findCG : {auto c : Ref Ctxt Defs} -> Core Codegen
findCG 
    = do defs <- get Ctxt
         case codegen (session (options defs)) of
              Chez => pure codegenChez
              Chicken => pure codegenChicken
              Racket => pure codegenRacket

export
execExp : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref MD Metadata} ->
          PTerm -> Core ()
execExp ctm
    = do ttimp <- desugar AnyExpr [] (PApp replFC (PRef replFC (UN "unsafePerformIO")) ctm)
         inidx <- resolveName (UN "[input]")
         (_, tm, ty) <- elabTerm inidx InExpr [] (MkNested [])
                                 [] ttimp Nothing
         execute !findCG tm
         
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

lookupDefTyName : Name -> Context GlobalDef -> 
                  Core (List (Name, Int, (Def, ClosedTerm)))
lookupDefTyName = lookupNameBy (\g => (definition g, type g))

processEdit : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto m : Ref MD Metadata} ->
              {auto o : Ref ROpts REPLOpts} ->
              EditCmd -> Core ()
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
                            else printResult res
         if res == ""
            then printResult !(showHole defs [] n num t)
            else printResult (res ++ "\n\n" ++ "Locally:\n" ++ 
                                     !(showHole defs [] n num t))
processEdit (CaseSplit line col name)
    = do let find = if col > 0
                       then within (line-1, col-1)
                       else onLine (line-1)
         OK splits <- getSplits (anyAt find) name
             | SplitFail err => printError (show err)
         lines <- updateCase splits (line-1) (col-1)
         printResult $ showSep "\n" lines ++ "\n"
processEdit (AddClause line name)
    = do Just c <- getClause line name
             | Nothing => printError (show name ++ " not defined here")
         printResult c
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
                        then printResult $ showSep "\n" (map show itms)
                        else case itms of
                                  [] => printError "No search results"
                                  (x :: xs) => printResult 
                                                  (show (if brack 
                                                            then addBracket replFC x
                                                            else x))
              [] => printError $ "Unknown name " ++ show name
              _ => printError "Not a searchable hole"
  where
    dropLams : Nat -> Env Term vars -> Term vars -> 
               (vars' ** (Env Term vars', Term vars'))
    dropLams Z env tm = (_ ** (env, tm))
    dropLams (S k) env (Bind _ _ b sc) = dropLams k (b :: env) sc 
    dropLams _ env tm = (_ ** (env, tm))
processEdit (GenerateDef line name)
    = do defs <- get Ctxt
         Just (_, n', _, _) <- findTyDeclAt (\p, n => onLine line p)
             | Nothing => printError ("Can't find declaration for " ++ show name ++ " on line " ++ show line)
         case !(lookupDefExact n' (gamma defs)) of
              Just None =>
                  catch 
                    (do Just (fc, cs) <- makeDef (\p, n => onLine line p) n'
                           | Nothing => processEdit (AddClause line name)
                        ls <- traverse (printClause (cast (snd (startPos fc)))) cs
                        printResult $ showSep "\n" ls)
                    (\err => printError $ "Can't find a definition for " ++ show n')
              Just _ => printError "Already defined"
              Nothing => printError $ "Can't find declaration for " ++ show name
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
                     case idemode opts of
                          REPL _ => printResult (show name ++ " : " ++ show pty ++ "\n" ++ pappstr)
                          IDEMode i _ f =>
                            send f (SExpList [SymbolAtom "return", 
                                    SExpList [SymbolAtom "ok",
                                      SExpList [SymbolAtom "metavariable-lemma",
                                        SExpList [SymbolAtom "replace-metavariable",
                                                  StringAtom pappstr],
                                        SExpList [SymbolAtom "definition-type",
                                                  StringAtom (show name ++ " : " ++ show pty)]]],
                                            toSExp i])
              _ => printError "Can't make lifted definition"
processEdit (MakeCase line name)
    = printError "Not implemented yet"
processEdit (MakeWith line name)
    = do Just l <- getSourceLine line
              | Nothing => printError "Source line not available"
         printResult (makeWith name l)

export
loadMainFile : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref MD Metadata} ->
               {auto o : Ref ROpts REPLOpts} ->
               String -> Core ()
loadMainFile f
    = do resetContext
         updateErrorLine !(buildDeps f)
         Right res <- coreLift (readFile f)
            | Left err => setSource ""
         setSource res

-- Returns 'True' if the REPL should continue
export
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref MD Metadata} ->
          {auto o : Ref ROpts REPLOpts} ->
          REPLCmd -> Core Bool
process (Eval itm)
    = do opts <- get ROpts
         case evalMode opts of
            Execute => do execExp itm; pure True
            _ => 
              do ttimp <- desugar AnyExpr [] itm
                 inidx <- resolveName (UN "[input]")
                 (tm, _, gty) <- elabTerm inidx InExpr [] (MkNested [])
                                          [] ttimp Nothing
                 defs <- get Ctxt
                 opts <- get ROpts
                 let norm = nfun (evalMode opts)
                 itm <- resugar [] !(norm defs [] tm)
                 if showTypes opts
                    then do ty <- getTerm gty
                            ity <- resugar [] !(norm defs [] ty)
                            coreLift (putStrLn (show itm ++ " : " ++ show ity))
                    else coreLift (putStrLn (show itm))
                 pure True
  where
    nfun : REPLEval -> Defs -> Env Term vs -> Term vs -> Core (Term vs)
    nfun NormaliseAll = normaliseAll
    nfun _ = normalise
process (Check (PRef fc fn))
    = do defs <- get Ctxt
         case !(lookupCtxtName fn (gamma defs)) of
              [] => throw (UndefinedName fc fn)
              ts => do tys <- traverse (displayType defs) ts
                       printResult (showSep "\n" tys)
                       pure True
process (Check itm)
    = do inidx <- resolveName (UN "[input]")
         ttimp <- desugar AnyExpr [] itm
         (tm, _, gty) <- elabTerm inidx InExpr [] (MkNested [])
                                  [] ttimp Nothing
         defs <- get Ctxt
         itm <- resugar [] !(normaliseHoles defs [] tm)
         ty <- getTerm gty
         ity <- resugar [] !(normaliseHoles defs [] ty)
         coreLift (putStrLn (show itm ++ " : " ++ show ity))
         pure True
process (PrintDef fn)
    = do defs <- get Ctxt
         case !(lookupCtxtName fn (gamma defs)) of
              [] => throw (UndefinedName replFC fn)
              ts => do defs <- traverse (displayPats defs) ts
                       printResult (showSep "\n" defs)
                       pure True
process Reload
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => do coreLift $ putStrLn "No file loaded"
                            pure True
              Just f => do loadMainFile f
                           pure True
process (Load f)
    = do opts <- get ROpts
         put ROpts (record { mainfile = Just f } opts)
         -- Clear the context and load again
         loadMainFile f
         pure True
process (CD dir)
    = do setWorkingDir dir
         pure True
process Edit
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => do coreLift $ putStrLn "No file loaded"
                            pure True
              Just f =>
                do let line = maybe "" (\i => " +" ++ show i) (errorLine opts)
                   coreLift $ system (editor opts ++ " " ++ f ++ line)
                   loadMainFile f
                   pure True
process (Compile ctm outfile)
    = do inidx <- resolveName (UN "[input]")
         ttimp <- desugar AnyExpr [] (PApp replFC (PRef replFC (UN "unsafePerformIO")) ctm)
         (_, tm, gty) <- elabTerm inidx InExpr [] (MkNested [])
                                  [] ttimp Nothing
         ok <- compile !findCG tm outfile
         maybe (pure ())
               (\fname => iputStrLn (outfile ++ " written"))
               ok
         pure True
process (Exec ctm)
    = do execExp ctm
         pure True
process (ProofSearch n_in)
    = do defs <- get Ctxt
         [(n, i, ty)] <- lookupTyName n_in (gamma defs)
              | [] => throw (UndefinedName replFC n_in)
              | ns => throw (AmbiguousName replFC (map fst ns))
         tm <- search replFC RigW False 1000 n ty []
         itm <- resugar [] !(normaliseHoles defs [] tm)
         coreLift (putStrLn (show itm))
         pure True
process (Missing n)
    = do defs <- get Ctxt 
         case !(lookupCtxtName n (gamma defs)) of
              [] => throw (UndefinedName replFC n)
              ts => do traverse (\fn =>
                          do tot <- getTotality replFC fn
                             the (Core ()) $ case isCovering tot of
                                  MissingCases cs => 
                                     do tms <- traverse (displayPatTerm defs) cs
                                        printResult (show fn ++ ":\n" ++
                                                        showSep "\n" tms)
                                  NonCoveringCall ns_in =>
                                    do ns <- traverse getFullName ns_in
                                       printResult 
                                         (show fn ++ ": Calls non covering function" 
                                           ++ case ns of
                                                   [fn] => " " ++ show fn
                                                   _ => "s: " ++ showSep ", " (map show ns))
                                  _ => iputStrLn (show fn ++ ": All cases covered")) 
                         (map fst ts)
                       pure True
process (Total n)
    = do defs <- get Ctxt
         case !(lookupCtxtName n (gamma defs)) of
              [] => throw (UndefinedName replFC n)
              ts => do traverse (\fn =>
                          do checkTotal replFC fn
                             tot <- getTotality replFC fn
                             iputStrLn (show fn ++ " is " ++ show tot)) 
                               (map fst ts)
                       pure True
process (DebugInfo n)
    = do defs <- get Ctxt
         traverse_ showInfo !(lookupCtxtName n (gamma defs))
         pure True
process (SetOpt opt)
    = do setOpt opt
         pure True
process (Editing cmd)
    = do ppopts <- getPPrint
         -- Since we're working in a local environment, don't do the usual
         -- thing of printing out the full environment for parameterised
         -- calls or calls in where blocks
         setPPrint (record { showFullEnv = False } ppopts)
         processEdit cmd
         setPPrint ppopts
         pure True
process Quit 
    = do iputStrLn "Bye for now!"
         pure False

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref MD Metadata} ->
               {auto o : Ref ROpts REPLOpts} ->
               REPLCmd -> Core Bool
processCatch cmd
    = do c' <- branch
         u' <- get UST
         s' <- get Syn
         o' <- get ROpts
         catch (do r <- process cmd
                   commit
                   pure r)
               (\err => do put Ctxt c'
                           put UST u'
                           put Syn s'
                           put ROpts o'
                           coreLift (putStrLn !(display err))
                           pure True)

parseRepl : String -> Either ParseError REPLCmd
parseRepl inp
    = case fnameCmd [(":load ", Load), (":l ", Load), (":cd ", CD)] inp of
           Nothing => runParser inp (do c <- command; eoi; pure c)
           Just cmd => Right cmd
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
            String -> Core Bool
interpret inp
    = case parseRepl inp of
           Left err => do printError (show err)
                          pure True
           Right cmd => processCatch cmd

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
         end <- coreLift $ fEOF stdin
         if end
            then iputStrLn "Bye for now!"
            else if !(interpret inp)
                    then repl
                    else pure ()

  where
    prompt : REPLEval -> String
    prompt EvalTC = "[tc] "
    prompt NormaliseAll = ""
    prompt Execute = "[exec] "
