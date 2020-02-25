module TTImp.ProcessRecord

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.UnifyState
import Core.Value

import TTImp.BindImplicits
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.TTImp
import TTImp.Unelab
import TTImp.Utils

mkDataTy : FC -> List (Name, RawImp) -> RawImp
mkDataTy fc [] = IType fc
mkDataTy fc ((n, ty) :: ps)
    = IPi fc RigW Explicit (Just n) ty (mkDataTy fc ps)

mkCon : Name -> Name
mkCon (NS ns (UN n)) = NS ns (DN n (MN ("__mk" ++ n) 0))
mkCon n = DN (show n) (MN ("__mk" ++ show n) 0)

elabRecord : {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             List ElabOpt -> FC -> Env Term vars ->
             NestedNames vars -> Visibility ->
             Name ->
             (params : List (Name, RawImp)) ->
             (conName : Maybe Name) ->
             List IField ->
             Core ()
elabRecord {vars} eopts fc env nest vis tn params rcon fields
    = do let conName_in = maybe (mkCon tn) id rcon
         conName <- inCurrentNS conName_in
         elabAsData conName
         defs <- get Ctxt
         Just conty <- lookupTyExact conName (gamma defs)
             | Nothing => throw (InternalError ("Adding " ++ show tn ++ "failed"))
         let recTy = apply (IVar fc tn) (map (IVar fc) (map fst params))
         elabGetters conName recTy 0 [] [] conty
  where
    jname : (Name, RawImp) -> (Maybe Name, RigCount, PiInfo RawImp, RawImp)
    jname (n, t) = (Just n, Rig0, Implicit, t)

    fname : IField -> Name
    fname (MkIField fc c p n ty) = n

    farg : IField ->
           (Maybe Name, RigCount, PiInfo RawImp, RawImp)
    farg (MkIField fc c p n ty) = (Just n, c, p, ty)

    mkTy : List (Maybe Name, RigCount, PiInfo RawImp, RawImp) ->
           RawImp -> RawImp
    mkTy [] ret = ret
    mkTy ((n, c, imp, argty) :: args) ret
        = IPi fc c imp n argty (mkTy args ret)

    elabAsData : Name -> Core ()
    elabAsData cname
        = do let retty = apply (IVar fc tn) (map (IVar fc) (map fst params))
             let conty = mkTy (map jname params) $
                         mkTy (map farg fields) retty
             let con = MkImpTy fc cname !(bindTypeNames [] (map fst params ++
                                           map fname fields ++ vars) conty)
             let dt = MkImpData fc tn !(bindTypeNames [] (map fst params ++
                                           map fname fields ++ vars)
                                         (mkDataTy fc params)) [] [con]
             log 5 $ "Record data type " ++ show dt
             processDecl [] nest env (IData fc vis dt)

    countExp : Term vs -> Nat
    countExp (Bind _ n (Pi c Explicit _) sc) = S (countExp sc)
    countExp (Bind _ n (Pi c _ _) sc) = countExp sc
    countExp _ = 0

    -- Generate getters from the elaborated record constructor type
    elabGetters : Name -> RawImp ->
                  (done : Nat) -> -- number of explicit fields processed
                  List (Name, RawImp) -> -- names to update in types
                    -- (for dependent records, where a field's type may depend
                    -- on an earlier projection)
                  Env Term vs -> Term vs ->
                  Core ()
    elabGetters con recTy done upds tyenv (Bind bfc n b@(Pi rc imp ty_chk) sc)
        = if n `elem` map fst params
             then elabGetters con recTy
                              (if imp == Explicit
                                  then S done else done)
                              upds (b :: tyenv) sc
             else
                do let fldName = n
                   gname <- inCurrentNS fldName
                   ty <- unelab tyenv ty_chk
                   let ty' = substNames vars upds ty
                   let rname = MN "rec" 0
                   gty <- bindTypeNames []
                                 (map fst params ++ map fname fields ++ vars) $
                                    mkTy (map jname params) $
                                      IPi fc RigW Explicit (Just rname) recTy ty'
                   log 5 $ "Projection " ++ show gname ++ " : " ++ show gty
                   let lhs_exp
                          = apply (IVar fc con)
                                    (replicate done (Implicit fc True) ++
                                       (if imp == Explicit
                                           then [IBindVar fc (nameRoot fldName)]
                                           else []) ++
                                    (replicate (countExp sc) (Implicit fc True)))
                   let lhs = IApp fc (IVar fc gname)
                                (if imp == Explicit
                                    then lhs_exp
                                    else IImplicitApp fc lhs_exp (Just n)
                                             (IBindVar fc (nameRoot fldName)))
                   processDecl [] nest env
                       (IClaim fc (if rc == Rig0
                                      then Rig0
                                      else RigW) vis [] (MkImpTy fc gname gty))
                   processDecl [] nest env
                       (IDef fc gname [PatClause fc lhs (IVar fc fldName)])
                   let upds' = (n, IApp fc (IVar fc gname) (IVar fc rname)) :: upds
                   elabGetters con recTy
                               (if imp == Explicit
                                   then S done else done)
                               upds' (b :: tyenv) sc
    elabGetters con recTy done upds _ _ = pure ()


export
processRecord : {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                List ElabOpt -> NestedNames vars ->
                Env Term vars -> Visibility ->
                ImpRecord -> Core ()
processRecord eopts nest env vis (MkImpRecord fc n ps cons fs)
    = elabRecord eopts fc env nest vis n ps cons fs

