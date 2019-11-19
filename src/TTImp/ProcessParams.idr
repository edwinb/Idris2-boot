module TTImp.ProcessParams

import Core.Context
import Core.Env
import Core.TT
import Core.Unify
import Core.Metadata
import Core.Normalise

import TTImp.BindImplicits
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.TTImp

%default covering

extend : Env Term extvs -> SubVars vs extvs ->
         NestedNames extvs ->
         Term extvs ->
         (vars' ** (SubVars vs vars', Env Term vars', NestedNames vars'))
extend env p nest (Bind fc n (Pi c e ty) sc)
    = extend (Pi c e ty :: env) (DropCons p) (weaken nest) sc
extend env p nest tm = (_ ** (p, env, nest))

export
processParams : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                NestedNames vars ->
                Env Term vars ->
                FC -> List (Name, RawImp) -> List ImpDecl ->
                Core ()
processParams {vars} {c} {m} {u} nest env fc ps ds
    = do -- Turn the parameters into a function type, (x : ps) -> Type,
         -- then read off the environment from the elaborated type. This way
         -- we'll get all the implicit names we need
         let pty_raw = mkParamTy ps
         pty_imp <- bindTypeNames vars (IBindHere fc (PI Rig0) pty_raw)
         log 10 $ "Checking " ++ show pty_imp
         pty <- checkTerm (-1) InType []
                          nest env pty_imp (gType fc)
         let (vs ** (prf, env', nest')) = extend env SubRefl nest pty

         -- Treat the names in the block as 'nested names' so that we expand
         -- the applications as we need to
         defs <- get Ctxt
         let defNames = definedInBlock (currentNS defs) ds
         names' <- traverse (applyEnv env') defNames
         let nestBlock = record { names $= (names' ++) } nest'
         traverse (processDecl [] nestBlock env') ds
         pure ()
  where
    mkParamTy : List (Name, RawImp) -> RawImp
    mkParamTy [] = IType fc
    mkParamTy ((n, ty) :: ps)
       = IPi fc RigW Explicit (Just n) ty (mkParamTy ps)

    applyEnv : Env Term vs -> Name ->
               Core (Name, (Maybe Name, FC -> NameType -> Term vs))
    applyEnv env n
          = do n' <- resolveName n -- it'll be Resolved by expandAmbigName
               pure (Resolved n', (Nothing,
                        \fc, nt => applyTo fc
                               (Ref fc nt (Resolved n')) env))
