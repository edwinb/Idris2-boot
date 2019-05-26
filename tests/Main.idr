module Main

import System

%default covering

ttimpTests : List String
ttimpTests 
    = ["basic001", "basic002", "basic003", "basic004", "basic005",
       "basic006",
       "dot001",
       "eta001", "eta002",
       "lazy001",
       "nest001", "nest002",
       "perf001", "perf002", "perf003",
       "qtt001", "qtt002", "qtt003",
       "search001", "search002", "search003", "search004"]

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

main : IO ()
main
    = do [_, ttimp] <- getArgs
              | _ => do putStrLn "Usage: runtests [ttimp path]"
         ttimps <- traverse (runTest "ttimp" ttimp) ttimpTests
--          blods <- traverse (runTest "blodwen" blodwen) blodwenTests
         if (any not ttimps)
            then exitWith (ExitFailure 1)
            else exitWith ExitSuccess

