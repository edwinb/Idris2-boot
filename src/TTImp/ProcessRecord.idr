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

elabRecord : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             List ElabOpt -> FC -> Env Term vars ->
             NestedNames vars -> Maybe String ->
             Visibility -> Name ->
             (params : List (Name, RawImp)) ->
             (conName : Name) ->
             List IField ->
             Core ()
elabRecord {vars} eopts fc env nest newns vis tn params conName_in fields
    = do conName <- inCurrentNS conName_in
         elabAsData conName
         defs <- get Ctxt
         Just conty <- lookupTyExact conName (gamma defs)
             | Nothing => throw (InternalError ("Adding " ++ show tn ++ "failed"))
         let recTy = apply (IVar fc tn) (map (IVar fc) (map fst params))
         addUndotted <- isUndottedRecordProjections
         -- Go into new namespace, if there is one, for getters
         case newns of
              Nothing =>
                   do elabGetters conName recTy 0 [] toRF [] conty -- make dotted projections
                      when addUndotted $
                        elabGetters conName recTy 0 [] id [] conty -- make undotted projections
              Just ns =>
                   do let cns = currentNS defs
                      let nns = nestedNS defs
                      extendNS [ns]
                      newns <- getNS
                      elabGetters conName recTy 0 [] toRF [] conty -- make dotted projections
                      when addUndotted $
                        elabGetters conName recTy 0 [] id [] conty -- make undotted projections
                      defs <- get Ctxt
                      -- Record that the current namespace is allowed to look
                      -- at private names in the nested namespace
                      put Ctxt (record { currentNS = cns,
                                         nestedNS = newns :: nns } defs)
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

    toRF : Name -> Name
    toRF (UN s) = RF s
    toRF n = n  -- should not happen

    -- Generate getters from the elaborated record constructor type
    elabGetters : {vs : _} ->
                  Name -> RawImp ->
                  (done : Nat) -> -- number of explicit fields processed
                  List (Name, RawImp) -> -- names to update in types
                    -- (for dependent records, where a field's type may depend
                    -- on an earlier projection)
                  (Name -> Name) ->
                  Env Term vs -> Term vs ->
                  Core ()
    elabGetters con recTy done upds mkProjName tyenv (Bind bfc n b@(Pi rc imp ty_chk) sc)
        = if (n `elem` map fst params) || (n `elem` vars)
             then elabGetters con recTy
                              (if imp == Explicit && not (n `elem` vars)
                                  then S done else done)
                              upds mkProjName (b :: tyenv) sc
             else
                do let fldName = n
                   gname <- inCurrentNS (mkProjName fldName)
                   ty <- unelab tyenv ty_chk
                   let ty' = substNames vars upds ty
                   log 5 $ "Field type: " ++ show ty'
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
                                           then [IBindVar fc (nameRoot gname)]
                                           else []) ++
                                    (replicate (countExp sc) (Implicit fc True)))
                   let lhs = IApp fc (IVar fc gname)
                                (if imp == Explicit
                                    then lhs_exp
                                    else IImplicitApp fc lhs_exp (Just n)
                                             (IBindVar fc (nameRoot gname)))
                   log 5 $ "Projection LHS " ++ show lhs
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
                               upds' mkProjName (b :: tyenv) sc
    elabGetters con recTy done upds _ _ _ = pure ()

export
processRecord : {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                List ElabOpt -> NestedNames vars ->
                Env Term vars -> Maybe String ->
                Visibility -> ImpRecord -> Core ()
processRecord eopts nest env newns vis (MkImpRecord fc n ps cons fs)
    = elabRecord eopts fc env nest newns vis n ps cons fs

