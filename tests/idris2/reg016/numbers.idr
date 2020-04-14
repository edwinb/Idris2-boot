main : IO ()
main = do
  printLn $ 3
  printLn $ 4.2
  printLn $ "1.2"

  printLn $ cast {to = Int} 4.8
  printLn $ cast {to = Integer} 1.2
  printLn $ cast {to = String} 2.7

  printLn $ cast {to = Int} "1.2"
  printLn $ cast {to = Integer} "2.7"
  printLn $ cast {to = Double} "5.9"
