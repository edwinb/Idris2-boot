module Unicode

infix 6 ≡, ≢

public export
interface UnicodeEq a where
    (≡) : a → a → Bool
    (≢) : a → a → Bool

