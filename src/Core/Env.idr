module Core.Env

import Core.TT

-- Environment containing types and values of local variables
namespace Env
  public export
  data Env : (tm : List Name -> Type) -> List Name -> Type where
       Nil : Env tm []
       (::) : Binder (tm vars) -> Env tm vars -> Env tm (x :: vars)

  export
  extend : (x : Name) -> Binder (tm vars) -> Env tm vars -> Env tm (x :: vars)
  extend x = (::) {x} 

  export
  length : Env tm xs -> Nat
  length [] = 0
  length (x :: xs) = S (length xs)

export
bindEnv : FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
bindEnv loc [] tm = tm
bindEnv loc (b :: env) tm 
    = bindEnv loc env (Bind loc _ b tm)
