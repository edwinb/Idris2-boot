module TTImp.Elab.App

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.TTImp

-- Make a metavariable for each given argument, returning a list
-- of arguments (if there is one given) and the metavariable it should
-- unify with.
export
collectArgs : RigCount -> Env Term vars ->
              (expargs : List RawImp) ->
              (impargs : List (Maybe Name, RawImp)) ->
              (fnty : NF vars) ->
              (expected : Maybe (NF vars)) ->
              Core (List (Maybe RawImp, Term vars))

export
checkAppWith : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto e : Ref EST (EState vars)} ->
               RigCount -> Env Term vars -> 
               FC -> Term vars -> NF vars ->
               (args : List (Maybe RawImp, Term vars)) ->
               (expected : Maybe (NF vars)) ->
               Core (Term vars, NF vars)

export
checkApp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> Env Term vars -> 
           FC -> (fn : RawImp) -> 
           (expargs : List RawImp) -> 
           (impargs : List (Maybe Name, RawImp)) ->
           Maybe (NF vars) ->
           Core (Term vars, NF vars)
checkApp rig env fc (IApp fc' fn arg) expargs impargs exp
   = checkApp rig env fc' fn (arg :: expargs) impargs exp
checkApp rig env fc (IImplicitApp fc' fn nm arg) expargs impargs exp
   = checkApp rig env fc' fn expargs ((nm, arg) :: impargs) exp
checkApp rig env fc fn expargs impargs exp
   = do (fntm, fnty) <- checkImp rig env fn Nothing
        argMetas <- collectArgs rig env expargs impargs fnty exp
        checkAppWith rig env fc fntm fnty argMetas exp


