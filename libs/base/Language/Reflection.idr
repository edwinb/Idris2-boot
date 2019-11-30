module Language.Reflection

import public Language.Reflection.TT
import public Language.Reflection.TTImp

public export
data TC : Type -> Type where
     Check : TTImp -> TC a
     Bind : TC a -> (a -> TC b) -> TC b

