module Main

import Parser.Support

import Core.Binary
import Core.Context
import Core.Env
import Core.FC
import Core.Normalise
import Core.TT
import Core.UnifyState

import TTImp.TTImp
import TTImp.Parser
import TTImp.ProcessDecls

import System

coreMain : String -> Core ()
coreMain fname
    = do Right tti <- coreLift $ parseFile fname
                                (do decls <- prog fname
                                    eoi
                                    pure decls)
             | Left err => do coreLift $ printLn err
                              coreLift $ exitWith (ExitFailure 1)
         coreLift $ putStrLn "Parsed okay"
         
         defs <- initDefs
         c <- newRef Ctxt defs
         u <- newRef UST initUState
         processDecls [] tti
         coreLift $ putStrLn "Done"

         defs <- get Ctxt
         res <- normalise defs [] (Ref emptyFC Func (NS ["Main"] (UN "main")))
         coreLift $ printLn !(toFullNames res)

main : IO ()
main
    = do [_, fname] <- getArgs
             | _ => do putStrLn "Usage: yaffle [input file]"
                       exitWith (ExitFailure 1)
         coreRun defaultOpts (coreMain fname)
               (\err : Error => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())
