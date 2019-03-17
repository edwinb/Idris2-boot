module Core.QUnify
-- Unification, but only simple terms in the current context

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

%default covering

solve : {vars : _} ->
        {auto c : Ref Ctxt Defs} ->
        {auto v : Ref UVars (UCtxt vars)} ->
        Env Term vars -> Int -> NF vars -> Core ()
solve env uvar tmnf
    = do defs <- get Ctxt
         empty <- clearDefs defs
         ucs <- get UVars
         tm <- quote empty ucs env tmnf
         setVar uvar tm

cantConvert : {auto c : Ref Ctxt Defs} ->
              {auto v : Ref UVars (UCtxt vars)} ->
              FC -> Env Term vars -> NF vars -> NF vars -> Core ()
cantConvert fc env x y
    = do defs <- get Ctxt
         ucs <- get UVars
         empty <- clearDefs defs
         throw (CantConvert fc env !(quote empty ucs env x)
                                   !(quote empty ucs env y))

mutual
  export
  qunifyArgs : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto v : Ref UVars (UCtxt vars)} ->
               FC -> Env Term vars -> 
               List (AppInfo, Closure vars) ->
               List (AppInfo, Closure vars) ->
               Core ()
  qunifyArgs fc env [] [] = pure ()
  qunifyArgs fc env ((_, x) :: xs) ((_, y) :: ys) 
      = do defs <- get Ctxt
           xnf <- evalClosure defs x
           ynf <- evalClosure defs y
           qunify fc env xnf ynf
           qunifyArgs fc env xs ys
  qunifyArgs fc env _ _ = throw (GenericMsg fc "Argument lists different lengths")

  export
  qunify : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto v : Ref UVars (UCtxt vars)} ->
           FC -> Env Term vars -> NF vars -> NF vars -> Core ()
  qunify fc env (NApp _ (NRef Bound (MV i)) []) tm = solve env i tm
  qunify fc env tm (NApp _ (NRef Bound (MV i)) []) = solve env i tm
  qunify fc env x@(NDCon _ _ tx ax argsx) y@(NDCon _ _ ty ay argsy)
      = if tx == ty && ax == ay
           then qunifyArgs fc env argsx argsy
           else cantConvert fc env x y
  qunify fc env x@(NTCon _ _ tx ax argsx) y@(NTCon _ _ ty ay argsy)
      = if tx == ty && ax == ay
           then qunifyArgs fc env argsx argsy
           else cantConvert fc env x y
  qunify fc env x@(NDelayed _ rx argx) y@(NDelayed _ ry argy)
      = if rx == ry
           then do defs <- get Ctxt
                   xtm <- evalClosure defs argx
                   ytm <- evalClosure defs argy
                   qunify fc env xtm ytm
            else cantConvert fc env x y
  qunify fc env x@(NDelay _ rx argx) y@(NDelay _ ry argy)
      = if rx == ry
           then do defs <- get Ctxt
                   xtm <- evalClosure defs argx
                   ytm <- evalClosure defs argy
                   qunify fc env xtm ytm
            else cantConvert fc env x y
  qunify fc env (NForce _ xtm) (NForce _ ytm)
      = qunify fc env xtm ytm
  qunify fc env x y 
      = do defs <- get Ctxt
           ucs <- get UVars
           if !(convert defs ucs env x y)
              then pure ()
              else cantConvert fc env x y 
