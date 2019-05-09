module TTImp.Elab.As

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.Elab.ImplicitBind
import TTImp.TTImp

import Data.NameMap

%default covering

export
checkAs : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto e : Ref EST (EState vars)} ->
          RigCount -> ElabInfo -> Env Term vars -> 
          FC -> Name -> RawImp -> Maybe (Glued vars) ->
          Core (Term vars, Glued vars)
checkAs rig elabinfo env fc n_in pat topexp 
    = do let elabmode = elabMode elabinfo
         let InLHS _ = elabmode
             | _ => throw (GenericMsg fc "@-patterns only allowed in pattern clauses")
         let str : String
             = case n_in of
                    UN x => x
                    _ => show n_in
         est <- get EST
         let n = PV (UN str) (defining est)
         noteLHSPatVar elabmode str
         notePatVar n
         case lookup n (boundNames est) of
              Nothing => 
                 do (pattm, patty) <- checkImp rig elabinfo env pat topexp
                    (tm, exp, bty) <- mkPatternHole fc rig n env
                                            (implicitMode elabinfo)
                                            topexp
                    log 5 $ "Added as pattern name " ++ show (n, (tm, exp, bty))
                    defs <- get Ctxt
                    est <- get EST
                    put EST
                        (record { boundNames $= ((n, AsBinding tm exp pattm) :: ),
                                  toBind $= ((n, AsBinding tm bty pattm) ::) }
                                est)
                   -- addNameType loc (UN str) env exp
                    (ntm, nty) <- checkExp rig elabinfo env fc tm (gnf env exp)
                                           (Just patty)
                    pure (As fc ntm pattm, patty)
              Just bty => throw (NonLinearPattern fc n_in) 
