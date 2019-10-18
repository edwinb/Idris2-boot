test3ok : Nat
test3ok = case (the Nat 1, the Nat 2) of
               (x, y) => x + y

test3bad : Nat
test3bad = case (1, 2) of
             (x, y) => x + y

