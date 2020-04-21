module Using

interface MagmaT a where
  op: a -> a -> a

interface MagmaT a => SemigroupT a where
  assoc: (x, y, z: a) -> (x `op` y) `op` z = x `op` (y `op` z)

[NamedMagma] MagmaT Bool where
  False `op` False = False
  _     `op` _     = True

[NamedSemigroup] SemigroupT Bool using NamedMagma where
  assoc = ?hole
