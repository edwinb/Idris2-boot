module Idris.Elab.Interface

import Core.Binary
import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.TT
import Core.Unify

import Idris.Resugar
import Idris.Syntax

import TTImp.BindImplicits
import TTImp.ProcessDecls
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Unelab
import TTImp.TTImp
import TTImp.Utils

import Data.ANameMap

-- TODO: Check all the parts of the body are legal
-- TODO: Deal with default superclass implementations

mkDataTy : FC -> List (Name, RawImp) -> RawImp
mkDataTy fc [] = IType fc
mkDataTy fc ((n, ty) :: ps)
    = IPi fc top Explicit (Just n) ty (mkDataTy fc ps)

mkIfaceData : {auto c : Ref Ctxt Defs} ->
              FC -> Visibility -> Env Term vars ->
              List (Maybe Name, RigCount, RawImp) ->
              Name -> Name -> List (Name, RawImp) ->
              List Name -> List (Name, RigCount, RawImp) -> Core ImpDecl
mkIfaceData {vars} fc vis env constraints n conName ps dets meths
    = let opts = if isNil dets
                    then [NoHints, UniqueSearch]
                    else [NoHints, UniqueSearch, SearchBy dets]
          retty = apply (IVar fc n) (map (IVar fc) (map fst ps))
          conty = mkTy Implicit (map jname ps) $
                  mkTy Explicit (map bhere constraints ++ map bname meths) retty
          con = MkImpTy fc conName !(bindTypeNames [] (map fst ps ++ map fst meths ++ vars) conty) in
          pure $ IData fc vis (MkImpData fc n
                                  !(bindTypeNames [] (map fst ps ++ map fst meths ++ vars)
                                                  (mkDataTy fc ps))
                                  opts [con])
  where
    jname : (Name, RawImp) -> (Maybe Name, RigCount, RawImp)
    jname (n, t) = (Just n, erased, t)

    bname : (Name, RigCount, RawImp) -> (Maybe Name, RigCount, RawImp)
    bname (n, c, t) = (Just n, c, IBindHere (getFC t) (PI erased) t)

    bhere : (Maybe Name, RigCount, RawImp) -> (Maybe Name, RigCount, RawImp)
    bhere (n, c, t) = (n, c, IBindHere (getFC t) (PI erased) t)

    mkTy : PiInfo RawImp ->
           List (Maybe Name, RigCount, RawImp) -> RawImp -> RawImp
    mkTy imp [] ret = ret
    mkTy imp ((n, c, argty) :: args) ret
        = IPi fc c imp n argty (mkTy imp args ret)

-- Give implicit Pi bindings explicit names, if they don't have one already,
-- because we need them to be consistent everywhere we refer to them
namePis : Int -> RawImp -> RawImp
namePis i (IPi fc r AutoImplicit Nothing ty sc)
    = IPi fc r AutoImplicit (Just (MN "i_con" i)) ty (namePis (i + 1) sc)
namePis i (IPi fc r Implicit Nothing ty sc)
    = IPi fc r Implicit (Just (MN "i_imp" i)) ty (namePis (i + 1) sc)
namePis i (IPi fc r p n ty sc)
    = IPi fc r p n ty (namePis i sc)
namePis i (IBindHere fc m ty) = IBindHere fc m (namePis i ty)
namePis i ty = ty

-- Get the implicit arguments for a method declaration or constraint hint
-- to allow us to build the data declaration
getMethDecl : {auto c : Ref Ctxt Defs} ->
              Env Term vars -> NestedNames vars ->
              (params : List (Name, RawImp)) ->
              (mnames : List Name) ->
              (FC, RigCount, List FnOpt, n, (Bool, RawImp)) ->
              Core (n, RigCount, RawImp)
getMethDecl {vars} env nest params mnames (fc, c, opts, n, (d, ty))
    = do ty_imp <- bindTypeNames [] (map fst params ++ mnames ++ vars) ty
         pure (n, c, stripParams (map fst params) ty_imp)
  where
    -- We don't want the parameters to explicitly appear in the method
    -- type in the record for the interface (they are parameters of the
    -- interface type), so remove it here
    stripParams : List Name -> RawImp -> RawImp
    stripParams ps (IPi fc r p mn arg ret)
        = if (maybe False (\n => n `elem` ps) mn)
             then stripParams ps ret
             else IPi fc r p mn arg (stripParams ps ret)
    stripParams ps ty = ty

-- bind the auto implicit for the interface - put it after all the other
-- implicits
bindIFace : FC -> RawImp -> RawImp -> RawImp
bindIFace _ ity (IPi fc rig Implicit n ty sc)
       = IPi fc rig Implicit n ty (bindIFace fc ity sc)
bindIFace _ ity (IPi fc rig AutoImplicit n ty sc)
       = IPi fc rig AutoImplicit n ty (bindIFace fc ity sc)
bindIFace fc ity sc = IPi fc top AutoImplicit (Just (UN "__con")) ity sc

-- Get the top level function for implementing a method
getMethToplevel : {auto c : Ref Ctxt Defs} ->
                  Env Term vars -> Visibility ->
                  Name -> Name ->
                  (constraints : List (Maybe Name)) ->
                  (allmeths : List Name) ->
                  (params : List (Name, RawImp)) ->
                  (FC, RigCount, List FnOpt, Name, (Bool, RawImp)) ->
                  Core (List ImpDecl)
getMethToplevel {vars} env vis iname cname constraints allmeths params
                (fc, c, opts, n, (d, ty))
    = do let ity = apply (IVar fc iname) (map (IVar fc) (map fst params))
         -- Make the constraint application explicit for any method names
         -- which appear in other method types
         let ty_constr =
             bindPs params $ substNames vars (map applyCon allmeths) ty
         ty_imp <- bindTypeNames [] vars (bindIFace fc ity ty_constr)
         cn <- inCurrentNS n
         let tydecl = IClaim fc c vis (if d then [Inline, Invertible]
                                            else [Inline])
                                      (MkImpTy fc cn ty_imp)
         let conapp = apply (IVar fc cname)
                         (map (const (Implicit fc True)) constraints ++
                          map (IBindVar fc) (map bindName allmeths))
         let argns = getExplicitArgs 0 ty
         -- eta expand the RHS so that we put implicits in the right place
         let fnclause = PatClause fc (IImplicitApp fc (IVar fc cn)
                                                   (Just (UN "__con"))
                                                   conapp)
                                  (mkLam argns
                                    (apply (IVar fc (methName n))
                                           (map (IVar fc) argns)))
         let fndef = IDef fc cn [fnclause]
         pure [tydecl, fndef]
  where
    -- Bind the type parameters given explicitly - there might be information
    -- in there that we can't infer after all
    bindPs : List (Name, RawImp) -> RawImp -> RawImp
    bindPs [] ty = ty
    bindPs ((n, pty) :: ps) ty
        = IPi (getFC pty) erased Implicit (Just n) pty (bindPs ps ty)

    applyCon : Name -> (Name, RawImp)
    applyCon n = (n, IImplicitApp fc (IVar fc n)
                             (Just (UN "__con")) (IVar fc (UN "__con")))

    getExplicitArgs : Int -> RawImp -> List Name
    getExplicitArgs i (IPi _ _ Explicit n _ sc)
        = MN "arg" i :: getExplicitArgs (i + 1) sc
    getExplicitArgs i (IPi _ _ _ n _ sc) = getExplicitArgs i sc
    getExplicitArgs i tm = []

    mkLam : List Name -> RawImp -> RawImp
    mkLam [] tm = tm
    mkLam (x :: xs) tm
       = ILam fc top Explicit (Just x) (Implicit fc False) (mkLam xs tm)

    bindName : Name -> String
    bindName (UN n) = "__bind_" ++ n
    bindName (NS _ n) = bindName n
    bindName n = show n

    methName : Name -> Name
    methName n = UN (bindName n)

-- Get the function for chasing a constraint. This is one of the
-- arguments to the record, appearing before the method arguments.
getConstraintHint : {auto c : Ref Ctxt Defs} ->
                    FC -> Env Term vars -> Visibility ->
                    Name -> Name ->
                    (constraints : List Name) ->
                    (allmeths : List Name) ->
                    (params : List Name) ->
                    (Name, RawImp) -> Core (Name, List ImpDecl)
getConstraintHint {vars} fc env vis iname cname constraints meths params (cn, con)
    = do let ity = apply (IVar fc iname) (map (IVar fc) params)
         let fty = IPi fc top Explicit Nothing ity con
         ty_imp <- bindTypeNames [] (meths ++ vars) fty
         let hintname = DN ("Constraint " ++ show con)
                          (UN ("__" ++ show iname ++ "_" ++ show con))
         let tydecl = IClaim fc top vis [Inline, Hint False]
                          (MkImpTy fc hintname ty_imp)
         let conapp = apply (IVar fc cname)
                        (map (IBindVar fc) (map bindName constraints) ++
                         map (const (Implicit fc True)) meths)
         let fnclause = PatClause fc (IApp fc (IVar fc hintname) conapp)
                                  (IVar fc (constName cn))
         let fndef = IDef fc hintname [fnclause]
         pure (hintname, [tydecl, fndef])
  where
    bindName : Name -> String
    bindName (UN n) = "__bind_" ++ n
    bindName (NS _ n) = bindName n
    bindName n = show n

    constName : Name -> Name
    constName n = UN (bindName n)

getSig : ImpDecl -> Maybe (FC, RigCount, List FnOpt, Name, (Bool, RawImp))
getSig (IClaim _ c _ opts (MkImpTy fc n ty))
    = Just (fc, c, opts, n, (False, namePis 0 ty))
getSig (IData _ _ (MkImpLater fc n ty))
    = Just (fc, erased, [Invertible], n, (True, namePis 0 ty))
getSig _ = Nothing

getDefault : ImpDecl -> Maybe (FC, List FnOpt, Name, List ImpClause)
getDefault (IDef fc n cs) = Just (fc, [], n, cs)
getDefault _ = Nothing

mkCon : FC -> Name -> Name
mkCon loc (NS ns (UN n))
   = NS ns (DN (n ++ " at " ++ show loc) (UN ("__mk" ++ n)))
mkCon loc n
   = DN (show n ++ " at " ++ show loc) (UN ("__mk" ++ show n))

updateIfaceSyn : {auto s : Ref Syn SyntaxInfo} ->
                 Name -> Name -> List Name -> List RawImp ->
                 List (Name, RigCount, (Bool, RawImp)) -> List (Name, List ImpClause) ->
                 Core ()
updateIfaceSyn iname cn ps cs ms ds
    = do syn <- get Syn
         let info = MkIFaceInfo cn ps cs ms ds
         put Syn (record { ifaces $= addName iname info } syn)

export
elabInterface : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto s : Ref Syn SyntaxInfo} ->
                {auto m : Ref MD Metadata} ->
                FC -> Visibility ->
                Env Term vars -> NestedNames vars ->
                (constraints : List (Maybe Name, RawImp)) ->
                Name ->
                (params : List (Name, RawImp)) ->
                (dets : List Name) ->
                (conName : Maybe Name) ->
                List ImpDecl ->
                Core ()
elabInterface {vars} fc vis env nest constraints iname params dets mcon body
    = do fullIName <- getFullName iname
         let conName_in = maybe (mkCon fc fullIName) id mcon
         -- Machine generated names need to be qualified when looking them up
         conName <- inCurrentNS conName_in
         let meth_sigs = mapMaybe getSig body -- (FC, RigCount, List FnOpt, Name, (Bool, RawImp))
         let meth_decls = map (\ (f, c, o, n, b, ty) => (n, c, b, ty)) meth_sigs
         let meth_names = map fst meth_decls
         let defaults = mapMaybe getDefault body

         elabAsData conName meth_names meth_sigs
         elabConstraintHints conName meth_names
         elabMethods conName meth_names meth_sigs
         ds <- traverse (elabDefault meth_decls) defaults

         ns_meths <- traverse (\mt => do n <- inCurrentNS (fst mt)
                                         pure (n, snd mt)) meth_decls
         ns_iname <- inCurrentNS fullIName
         updateIfaceSyn ns_iname conName
                        (map fst params) (map snd constraints)
                        ns_meths ds
  where
    nameCons : Int -> List (Maybe Name, RawImp) -> List (Name, RawImp)
    nameCons i [] = []
    nameCons i ((_, ty) :: rest)
        = (UN ("__con" ++ show i), ty) :: nameCons (i + 1) rest

    -- Elaborate the data declaration part of the interface
    elabAsData : (conName : Name) -> List Name ->
                 List (FC, RigCount, List FnOpt, Name, (Bool, RawImp)) ->
                 Core ()
    elabAsData conName meth_names meth_sigs
        = do -- set up the implicit arguments correctly in the method
             -- signatures and constraint hints
             meths <- traverse (getMethDecl env nest params meth_names) meth_sigs
             log 5 $ "Method declarations: " ++ show meths

             consts <- traverse (getMethDecl env nest params meth_names)
                                (map (\c => (fc, linear, [], c))
                                   (map notData constraints))
             log 5 $ "Constraints: " ++ show consts

             dt <- mkIfaceData fc vis env consts iname conName params
                                  dets meths
             log 10 $ "Methods: " ++ show meths
             log 5 $ "Making interface data type " ++ show dt
             processDecls nest env [dt]
             pure ()
      where
        notData : (n, t) -> (n, (Bool, t))
        notData (x, y) = (x, (False, y))

    elabMethods : (conName : Name) -> List Name ->
                  List (FC, RigCount, List FnOpt, Name, (Bool, RawImp)) ->
                  Core ()
    elabMethods conName meth_names meth_sigs
        = do -- Methods have same visibility as data declaration
             fnsm <- traverse (getMethToplevel env vis iname conName
                                               (map fst constraints)
                                               meth_names
                                               params) meth_sigs
             let fns = concat fnsm
             log 5 $ "Top level methods: " ++ show fns
             traverse (processDecl [] nest env) fns
             traverse_ (\n => do mn <- inCurrentNS n
                                 setFlag fc mn Inline
                                 setFlag fc mn TCInline
                                 setFlag fc mn Overloadable) meth_names

    -- Check that a default definition is correct. We just discard it here once
    -- we know it's okay, since we'll need to re-elaborate it for each
    -- instance, to specialise it
    elabDefault : List (Name, RigCount, (Bool, RawImp)) ->
                  (FC, List FnOpt, Name, List ImpClause) ->
                  Core (Name, List ImpClause)
    elabDefault tydecls (fc, opts, n, cs)
        = do -- orig <- branch
             let dn_in = UN ("Default implementation of " ++ show n)
             dn <- inCurrentNS dn_in

             (rig, dty) <-
                   the (Core (RigCount, RawImp)) $
                       case lookup n tydecls of
                          Just (r, (_, t)) => pure (r, t)
                          Nothing => throw (GenericMsg fc ("No method named " ++ show n ++ " in interface " ++ show iname))

             let ity = apply (IVar fc iname) (map (IVar fc) (map fst params))

             -- Substitute the method names with their top level function
             -- name, so they don't get implicitly bound in the name
             methNameMap <- traverse (\n =>
                                do cn <- inCurrentNS n
                                   pure (n, applyParams (IVar fc cn)
                                                     (map fst params)))
                               (map fst tydecls)
             let dty = substNames vars methNameMap dty

             dty_imp <- bindTypeNames [] (map fst tydecls ++ vars)
                                      (bindIFace fc ity dty)
             log 5 $ "Default method " ++ show dn ++ " : " ++ show dty_imp
             let dtydecl = IClaim fc rig vis [] (MkImpTy fc dn dty_imp)
             processDecl [] nest env dtydecl

             let cs' = map (changeName dn) cs
             log 5 $ "Default method body " ++ show cs'

             processDecl [] nest env (IDef fc dn cs')
             -- Reset the original context, we don't need to keep the definition
             -- Actually we do for the metadata and name map!
--              put Ctxt orig
             pure (n, cs)
      where
        applyParams : RawImp -> List Name -> RawImp
        applyParams tm [] = tm
        applyParams tm (UN n :: ns)
            = applyParams (IImplicitApp fc tm (Just (UN n)) (IBindVar fc n)) ns
        applyParams tm (_ :: ns) = applyParams tm ns

        changeNameTerm : Name -> RawImp -> RawImp
        changeNameTerm dn (IVar fc n')
            = if n == n' then IVar fc dn else IVar fc n'
        changeNameTerm dn (IApp fc f arg)
            = IApp fc (changeNameTerm dn f) arg
        changeNameTerm dn (IImplicitApp fc f x arg)
            = IImplicitApp fc (changeNameTerm dn f) x arg
        changeNameTerm dn tm = tm

        changeName : Name -> ImpClause -> ImpClause
        changeName dn (PatClause fc lhs rhs)
            = PatClause fc (changeNameTerm dn lhs) rhs
        changeName dn (ImpossibleClause fc lhs)
            = ImpossibleClause fc (changeNameTerm dn lhs)

    elabConstraintHints : (conName : Name) -> List Name ->
                          Core ()
    elabConstraintHints conName meth_names
        = do let nconstraints = nameCons 0 constraints
             chints <- traverse (getConstraintHint fc env vis iname conName
                                                 (map fst nconstraints)
                                                 meth_names
                                                 (map fst params)) nconstraints
             log 5 $ "Constraint hints from " ++ show constraints ++ ": " ++ show chints
             traverse (processDecl [] nest env) (concatMap snd chints)
             traverse_ (\n => do mn <- inCurrentNS n
                                 setFlag fc mn TCInline) (map fst chints)

