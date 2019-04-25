module Main

import Parser.Support

import Core.Binary
import Core.Context
import Core.Directory
import Core.Env
import Core.FC
import Core.Normalise
import Core.Options
import Core.TT
import Core.UnifyState

import TTImp.TTImp
import TTImp.Parser
import TTImp.ProcessDecls

import System

coreMain : String -> Core ()
coreMain fname
    = do defs <- initDefs 
         c <- newRef Ctxt defs
         u <- newRef UST initUState
         d <- getDirs
         case span (/= '.') fname of
              (_, ".ttc") => do coreLift $ putStrLn "Processing as TTC"
                                readFromTTC {extra = ()} emptyFC True fname [] []
                                coreLift $ putStrLn "Read TTC"
              _ => do coreLift $ putStrLn "Processing as TTImp"
                      ok <- processTTImpFile fname
                      when ok $
                         do makeBuildDirectory (pathToNS (working_dir d) fname)
                            writeToTTC () !(getTTCFileName fname ".ttc")
                            coreLift $ putStrLn "Written TTC"

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
