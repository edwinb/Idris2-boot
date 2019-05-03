module Yaffle.REPL

import Core.AutoSearch
import Core.Context
import Core.Core
import Core.Env
import Core.FC
import Core.Normalise
import Core.TT
import Core.Unify
import Core.Value

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Parser
import TTImp.ProcessDecls
import TTImp.TTImp

import Parser.Support

import Control.Catchable

%default covering

showInfo : (Name, Int, Def) -> Core ()
showInfo (n, d) = coreLift $ putStrLn (show n ++ " ==> " ++ show d)

-- Returns 'True' if the REPL should continue
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          ImpREPL -> Core Bool
process (Eval ttimp)
    = do (tm, _) <- elabTerm (UN "[input]") InExpr [] ttimp Nothing
         defs <- get Ctxt
         tmnf <- normalise defs [] tm
         coreLift (printLn !(toFullNames tmnf))
         pure True
process (Check ttimp)
    = do (tm, gty) <- elabTerm (UN "[input]") InExpr [] ttimp Nothing
         defs <- get Ctxt
         tyh <- getTerm gty
         ty <- normaliseHoles defs [] tyh
         coreLift (printLn !(toFullNames ty))
         pure True
process (ProofSearch n_in)
    = do defs <- get Ctxt
         [(n, i, ty)] <- lookupTyName n_in (gamma defs)
              | [] => throw (UndefinedName toplevelFC n_in)
              | ns => throw (AmbiguousName toplevelFC (map fst ns))
         def <- search toplevelFC RigW False 1000 n ty []
         defs <- get Ctxt
         defnf <- normaliseHoles defs [] def
         coreLift (printLn !(toFullNames defnf))
         pure True
process (DebugInfo n)
    = do defs <- get Ctxt
         traverse showInfo !(lookupDefName n (gamma defs))
         pure True
process Quit 
    = do coreLift $ putStrLn "Bye for now!"
         pure False

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               ImpREPL -> Core Bool
processCatch cmd
    = catch (process cmd) 
            (\err => do coreLift (putStrLn (show err))
                        pure True)

export
repl : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST UState} ->
       Core ()
repl
    = do coreLift (putStr "Yaffle> ")
         inp <- coreLift getLine
         case runParser inp command of
              Left err => do coreLift (printLn err)
                             repl
              Right cmd =>
                  do if !(processCatch cmd)
                        then repl
                        else pure ()


