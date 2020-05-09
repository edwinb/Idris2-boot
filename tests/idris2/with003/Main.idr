module Main

-- add some definition of (>>=) in another namespace
(>>=) : IO a -> IO b -> IO b
(>>=) f x = f *> x

main : IO ()
main = with Prelude.(>>=) do
  printLn $ "foo"
  printLn $ "moo"
  map (+1) $ with [Prelude.(>>=), Prelude.pure] do
    printLn $ "boo"
    -- pure 4  -- causes type error
  printLn $ "moo"
  printLn $ "moo"
  printLn $ "moo"
