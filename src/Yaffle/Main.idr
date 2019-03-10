module Main

import Parser.Support

import Core.TT
import TTImp.TTImp
import TTImp.Parser

import System

main : IO ()
main
    = do [_, fname] <- getArgs
             | _ => do putStrLn "Usage: yaffle [input file]"
                       exitWith (ExitFailure 1)
         Right tti <- parseFile fname
                                (do decls <- prog fname
                                    eoi
                                    pure decls)
             | Left err => do printLn err
                              exitWith (ExitFailure 1)
         putStrLn "Parsed okay"
         putStrLn (showSep "\n" (map show tti))
