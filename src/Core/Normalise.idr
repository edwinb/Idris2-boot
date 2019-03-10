module Core.Evaluate

import Core.Context
import Core.Env
import Core.TT
import Core.Value

Stack : List Name -> Type
Stack vars = List (Closure vars)

evalWithOpts : Defs -> EvalOpts ->
               Env Term free -> LocalEnv free vars -> 
               Term (vars ++ free) -> Stack free -> Core (NF free)

parameters (defs : Defs, opts : EvalOpts)
  mutual
    eval : Env Term free -> LocalEnv free vars -> 
           Term (vars ++ free) -> Stack free -> Core (NF free)

evalWithOpts = eval
