module TTImp.ProcessDef

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.UnifyState

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.TTImp

-- Check a pattern clause, returning the component of the 'Case' expression it
-- represents, or Nothing if it's an impossible clause
export
checkClause : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              (mult : RigCount) -> (hashit : Bool) ->
              Name -> Env Term vars ->
              ImpClause -> Core (Maybe (PatAlt vars))
checkClause mult hashit n env (ImpossibleClause fc lhs)
    = throw (InternalError "impossible not implemented yet")
checkClause mult hashit n env (PatClause fc lhs_in rhs)
    = do lhs <- lhsInCurrentNS lhs_in 
         (lhstm, lhsty) <- elabTerm n (InLHS mult) env 
                                (IBindHere fc PATTERN lhs) Nothing
         logTermNF 0 "LHS term" env lhstm
         logGlue 0 "LHS type" env lhsty
         ?checkPat

export
processDef : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             Env Term vars -> FC ->
             Name -> List ImpClause -> Core ()
processDef env fc n_in cs_in
    = do n <- inCurrentNS n_in
         defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (NoDeclaration fc n)
         let None = definition gdef
              | _ => throw (AlreadyDefined fc n)
         let ty = type gdef
         let hashit = visibility gdef == Public
         let mult = if multiplicity gdef == Rig0
                       then Rig0
                       else Rig1
         cs <- traverse (checkClause mult hashit n env) cs_in
         ?something
