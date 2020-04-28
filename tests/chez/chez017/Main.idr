module Main

data Foo : Type where
  MkFoo : String -> Foo

data Bar : Type where
  [noNewtype]
  MkBar : String -> Bar


-- This code rely on the fact that `putStr` calls the Chez function `display`,
-- which allows any value to be printed. This will expose the internal
-- structure of each data type.
main : IO ()
main = do
  putStr (believe_me (MkFoo "foo"))
  putChar '\n'
  putStr (believe_me (MkBar "bar"))
  putChar '\n'
