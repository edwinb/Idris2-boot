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
       "with001",  "with002" ]

idrisTests : List String
idrisTests
    = -- Fundamental language feturea
      ["basic001", "basic002", "basic003", "basic004", "basic005",
       "basic006", "basic007", "basic008", "basic009", "basic010",
       "basic011", "basic012", "basic013", "basic014", "basic015",
       "basic016", "basic017", "basic018", "basic019", "basic020",
       "basic021", "basic022", "basic023", "basic024", "basic025",
       "basic026", "basic027", "basic028", "basic029", "basic030",
       "basic031", "basic032", "basic033", "basic034", "basic035",
       -- Coverage checking
       "coverage001", "coverage002", "coverage003", "coverage004",
       -- Error messages
       "error001", "error002", "error003", "error004", "error005",
       "error006", "error007", "error008", "error009", "error010",
       -- Modules and imports
       "import001", "import002", "import003", "import004",
       -- Interactive editing support
       "interactive001", "interactive002", "interactive003", "interactive004",
       "interactive005", "interactive006", "interactive007", "interactive008",
       "interactive009", "interactive010", "interactive011", "interactive012",
       -- Interfaces
       "interface001", "interface002", "interface003", "interface004",
       "interface005", "interface006", "interface007", "interface008",
       "interface009", "interface010", "interface011", "interface012",
       "interface013", "interface014",
       -- Miscellaneous REPL
       "interpreter001",
       -- Implicit laziness, lazy evaluation
       "lazy001",
       -- QTT and linearity related
       "linear001", "linear002", "linear003", "linear004", "linear005",
       "linear006", "linear007", "linear008",
       -- Parameters blocks
       "params001",
       -- Performance: things which have been slow in the past, or which
       -- pose interesting challenges for the elaborator
       "perf001", "perf002", "perf003",
       -- Parse errors
       "perror001", "perror002", "perror003", "perror004", "perror005",
       "perror006",
       -- Packages and ipkg files
       "pkg001", "pkg002",
       -- Larger programs arising from real usage. Typically things with
       -- interesting interactions between features
       "real001", "real002",
       -- Records, access and dependent update
       "record001", "record002",
       -- Miscellaneous regressions
       "reg001", "reg002", "reg003", "reg004",
       -- Totality checking
       "total001", "total002", "total003", "total004", "total005",
       "total006",
       -- The 'with' rule
       "with001"]

typeddTests : List String
typeddTests
   = ["chapter01", "chapter02", "chapter03", "chapter04", "chapter05",
      "chapter06", "chapter07", "chapter08", "chapter09", "chapter10",
      "chapter11", "chapter12"]

chezTests : List String
chezTests
   = ["chez001", "chez002", "chez003", "chez004", "chez005", "chez006",
      "chez007", "chez008", "chez009", "chez010", "chez011", "chez012"]

ideModeTests : List String
ideModeTests
  =  [ "ideMode001", "ideMode002" ]

chdir : String -> IO Bool
chdir dir
    = do ok <- foreign FFI_C "chdir" (String -> IO Int) dir
         pure (ok == 0)

fail : String -> IO ()
fail err
    = do putStrLn err
         exitWith (ExitFailure 1)

runTest : String -> String -> IO Bool
runTest prog testPath
    = do chdir testPath
         isSuccess <- runTest'
         chdir "../.."
         pure isSuccess
    where
        runTest' : IO Bool
        runTest'
            = do putStr $ testPath ++ ": "
                 system $ "sh ./run " ++ prog ++ " | tr -d '\\r' > output"
                 Right out <- readFile "output"
                     | Left err => do print err
                                      pure False
                 Right exp <- readFile "expected"
                     | Left err => do print err
                                      pure False

                 if (out == exp)
                    then putStrLn "success"
                    else do
                      putStrLn "FAILURE"
                      putStrLn "Expected:"
                      printLn exp
                      putStrLn "Given:"
                      printLn out

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
    = do env <- getEnv "CHEZ"
         case env of
            Just n => pure $ Just n
            Nothing => firstExists [p ++ x | p <- ["/usr/bin/", "/usr/local/bin/"],
                                    x <- ["chez", "chezscheme9.5", "scheme"]]

runChezTests : String -> List String -> IO (List Bool)
runChezTests prog tests
    = do chexec <- findChez
         maybe (do putStrLn "Chez Scheme not found"
                   pure [])
               (\c => do putStrLn $ "Found Chez Scheme at " ++ c
                         traverse (runTest prog) tests)
               chexec

main : IO ()
main
    = do args <- getArgs
         let (_ :: idris2 :: _) = args
              | _ => do putStrLn "Usage: runtests <idris2 path> [--only <name>]"
         let filterTests = case drop 2 args of
              ("--only" :: onlyName :: _) => filter (\testName => isInfixOf onlyName testName)
              _ => id
         let filteredNonCGTests =
              filterTests $ concat [testPaths "ttimp" ttimpTests,
                                    testPaths "idris2" idrisTests,
                                    testPaths "typedd-book" typeddTests,
                                    testPaths "ideMode" ideModeTests]
         let filteredChezTests = filterTests (testPaths "chez" chezTests)
         nonCGTestRes <- traverse (runTest idris2) filteredNonCGTests
         chezTestRes <- if length filteredChezTests > 0
              then runChezTests idris2 filteredChezTests
              else pure []
         let res = nonCGTestRes ++ chezTestRes
         putStrLn (show (length (filter id res)) ++ "/" ++ show (length res)
                       ++ " tests successful")
         if (any not res)
            then exitWith (ExitFailure 1)
            else exitWith ExitSuccess
    where
         testPaths : String -> List String -> List String
         testPaths dir tests = map (\test => dir ++ "/" ++ test) tests
