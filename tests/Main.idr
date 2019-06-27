module Main

import System

%default covering

ttimpTests : List String
ttimpTests 
    = ["basic001", "basic002", "basic003", "basic004", "basic005",
       "basic006",
       "coverage001", "coverage002",
       "dot001",
       "eta001", "eta002",
       "lazy001",
       "nest001", "nest002",
       "perf001", "perf002", "perf003",
       "record001", "record002",
       "rewrite001",
       "qtt001", "qtt002", "qtt003",
       "search001", "search002", "search003", "search004", "search005",
       "total001", "total002", "total003",
       "with001"]

idrisTests : List String
idrisTests
    = ["basic001", "basic002", "basic003", "basic004", "basic005",
       "basic006", "basic007", "basic008", "basic009", "basic010",
       "coverage001", "coverage002",
       "error001", "error002", "error003", "error004", "error005",
       "error006",
       "interactive001", "interactive002", "interactive003", "interactive004",
       "interactive005", "interactive006", "interactive007", "interactive008",
       "interactive009", "interactive010", "interactive011", "interactive012",
       "interface001", "interface002", "interface003", "interface004",
       "interface005",
       "import001", "import002",
       "lazy001",
       "linear001", "linear002", "linear003", "linear004", "linear005",
       "record001", "record002",
       "total001", "total002", "total003", "total004", "total005",
       "total006"]

chezTests : List String
chezTests
   = ["chez001", "chez002", "chez003", "chez004"]

chdir : String -> IO Bool
chdir dir 
    = do ok <- foreign FFI_C "chdir" (String -> IO Int) dir
         pure (ok == 0)

fail : String -> IO ()
fail err 
    = do putStrLn err
         exitWith (ExitFailure 1)

runTest : String -> String -> String -> IO Bool
runTest dir prog test
    = do chdir (dir ++ "/" ++ test)
         putStr $ dir ++ "/" ++ test ++ ": "
         system $ "sh ./run " ++ prog ++ " > output"
         Right out <- readFile "output"
               | Left err => do print err
                                pure False
         Right exp <- readFile "expected"
               | Left err => do print err
                                pure False
         if (out == exp)
            then putStrLn "success"
            else putStrLn "FAILURE"
         chdir "../.."
         pure (out == exp)

exists : String -> IO Bool
exists f
    = do Right ok <- openFile f Read
             | Left err => pure False
         closeFile ok
         pure True

firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

findChez : IO (Maybe String)
findChez
    = firstExists [p ++ x | p <- ["/usr/bin/", "/usr/local/bin/"],
                            x <- ["scheme", "chez", "chezscheme9.5"]]

main : IO ()
main
    = do [_, idris2] <- getArgs
              | _ => do putStrLn "Usage: runtests [ttimp path]"
         ttimps <- traverse (runTest "ttimp" idris2) ttimpTests
         idrs <- traverse (runTest "idris2" idris2) idrisTests
         chexec <- findChez
         chezs <- maybe (do putStrLn "Chez Scheme not found"
                            pure [])
                        (\c => do putStrLn $ "Found Chez Scheme at " ++ c
                                  traverse (runTest "chez" idris2) chezTests)
                        chexec
         if (any not (ttimps ++ idrs ++ chezs))
            then exitWith (ExitFailure 1)
            else exitWith ExitSuccess

