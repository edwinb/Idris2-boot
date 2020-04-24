module Main

record Point where
  constructor MkPoint
  x : Double
  y : Double

-- a record creates two projections:
--
-- .x : Point -> Double
-- .y : Point -> Double
--
-- because %undotted_record_projections are on by default, we also get:
--
-- x : Point -> Double
-- y : Point -> Double

-- to prevent cluttering the ordinary name space with short identifiers
%undotted_record_projections off

record Rect where
  constructor MkRect
  topLeft : Point
  bottomRight : Point

-- .topLeft : Rect -> Point
-- .bottomRight : Rect -> Point
--
-- For Rect, we don't get the undotted projections:
--
-- Main> :t topLeft
-- (interactive):1:4--1:11:Undefined name topLeft
-- Main> :t .topLeft
-- \{rec:0} => .topLeft rec : ?_ -> Point


pt : Point
pt = MkPoint 4.2 6.6

rect : Rect
rect =
  MkRect
    (MkPoint 1.1 2.5)
    (MkPoint 4.3 6.3)

-- New lexical structure:
--
-- Foo.bar.baz with uppercase F is one lexeme: NSIdent ["baz", "bar", "Foo"]
-- foo.bar.baz with lowercase f is three lexemes: foo, .bar, .baz
-- .foo.bar.baz is three lexemes: .foo, .bar, .baz
--
-- If you want Constructor.field, you have to write (Constructor).field.
--
-- New syntax of simpleExpr:
--
-- Expressions binding tighter than application (simpleExpr),
-- such as variables or parenthesised expressions,
-- have been renamed to simplerExpr,
-- and an extra layer of syntax has been inserted.
-- 
--   simpleExpr ::= (.field)+               -- parses as PRecordProjection
--                | simplerExpr (.field)+   -- parses as PRecordFieldAccess
--                | simplerExpr             -- (parses as whatever it used to)
--
-- (.foo) is a name, so you can use it to e.g. define a function called .foo (see .squared below)
-- (.foo.bar) is a parenthesised expression
--
-- New desugaring rules
--
-- (.field1 .field2 .field3) desugars to (\x => .field3 (.field2 (.field1 x)))
-- (simpleExpr .field1 .field2 .field3) desugars to ((.field .field2 .field3) simpleExpr).
--
-- There are more details such as namespacing; see below.

-- user-defined projections work, too (should they?)
(.squared) : Double -> Double
(.squared) x = x * x

main : IO ()
main = do
  -- desugars to (.x pt)
  -- prints 4.2
  printLn $ pt.x

  -- prints 4.2, too
  -- maybe we want to make this a parse error?
  printLn $ pt .x

  -- prints 10.8
  printLn $ pt.x + pt.y

  -- works fine with namespacing
  -- prints 4.2
  printLn $ (Main.pt).x

  -- the LHS can be an arbitrary expression
  -- prints 4.2
  printLn $ (MkPoint pt.y pt.x).y

  -- user-defined projection
  -- prints 17.64
  printLn $ pt.x.squared

  -- prints [1.1, 4.2]
  printLn $ map (.x) [MkPoint 1.1 2.5, MkPoint 4.2 6.3]

  -- parses but does not typecheck
  -- parses as: map.x [MkPoint 1 2, MkPoint 3 4]
  -- maybe we should disallow spaces before dots?
  --
  -- printLn $ map .x [MkPoint 1 2, MkPoint 3 4]

  -- .topLeft.y desugars to (\x => .y (.topLeft x))
  -- prints [2.5, 2.5]
  printLn $ map (.topLeft.y) [rect, rect]

  -- desugars to (.topLeft.x rect + .bottomRight.y rect)
  -- prints 7.4
  printLn $ rect.topLeft.x + rect.bottomRight.y

  -- qualified names work, too
  -- all these print 4.2
  printLn $ Main.Point.(.x) pt
  printLn $ Point.(.x) pt
  printLn $ (.x) pt
  printLn $ .x pt

  -- haskell-style projections work, too
  printLn $ Main.Point.x pt
  printLn $ Point.x pt
  printLn $ (x) pt
  printLn $ x pt

  -- record update syntax uses dots now
  -- prints 3.0
  printLn $ (record { topLeft.x = 3 } rect).topLeft.x

  -- prints 2.1
  printLn $ (record { topLeft.x $= (+1) } rect).topLeft.x
