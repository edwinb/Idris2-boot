module TTImp.ProcessTransform

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.UnifyState

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.ProcessDef -- for checking LHS
import TTImp.TTImp

export
processTransform : {auto c : Ref Ctxt Defs} ->
                   {auto m : Ref MD Metadata} ->
                   {auto u : Ref UST UState} ->
                   List ElabOpt -> NestedNames vars -> Env Term vars -> FC ->
                   Name -> RawImp -> RawImp -> Core ()
processTransform eopts nest env fc tn_in lhs rhs
    = do tn <- inCurrentNS tn_in
         tidx <- resolveName tn
         (_, (vars'  ** (sub', env', nest', lhstm, lhsty))) <-
             checkLHS True top True tidx eopts nest env fc lhs
         logTerm 3 "Transform LHS" lhstm
         rhstm <- wrapError (InRHS fc tn_in) $
                       checkTermSub tidx InExpr (InTrans :: eopts) nest' env' env sub' rhs (gnf env' lhsty)
         clearHoleLHS
         logTerm 3 "Transform RHS" rhstm
         addTransform fc (MkTransform tn env' lhstm rhstm)
