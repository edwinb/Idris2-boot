module Main

record Point where
  constructor MkPoint
  x : Double
  y : Double

Show Point where
  show p = "(" ++ show p.x ++ ", " ++ show p.y ++ ")"

-- a record creates two projections:
--
-- x : Point -> Double
-- y : Point -> Double

record Rect where
  constructor MkRect
  topLeft : Point
  bottomRight : Point

-- topLeft : Rect -> Point
-- bottomRight : Rect -> Point


pt : Point
pt = MkPoint 4.2 6.6

pts : List Point
pts = [pt, pt, pt]

rect : Rect
rect =
  MkRect
    (MkPoint 1.1 2.5)
    (MkPoint 4.3 6.3)

squared : Double -> Double
squared x = x * x
