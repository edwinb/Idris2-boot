module TTImp.ProcessType

import Core.Context
import Core.Core
import Core.Env
import Core.Hash
import Core.Metadata
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value

import TTImp.BindImplicits
import TTImp.Elab.Check
import TTImp.Elab.Utils
import TTImp.Elab
import TTImp.TTImp

import Data.NameMap

%default covering

getRetTy : Defs -> NF [] -> Core Name
getRetTy defs (NBind fc _ (Pi _ _ _) sc)
    = getRetTy defs !(sc defs (toClosure defaultOpts [] (Erased fc False)))
getRetTy defs (NTCon _ n _ _ _) = pure n
getRetTy defs ty
    = throw (GenericMsg (getLoc ty)
             "Can only add hints for concrete return types")

processFnOpt : {auto c : Ref Ctxt Defs} ->
               FC -> Name -> FnOpt -> Core ()
processFnOpt fc ndef Inline
    = setFlag fc ndef Inline
processFnOpt fc ndef (Hint d)
    = do defs <- get Ctxt
         Just ty <- lookupTyExact ndef (gamma defs)
              | Nothing => throw (UndefinedName fc ndef)
         target <- getRetTy defs !(nf defs [] ty)
         addHintFor fc target ndef d False
processFnOpt fc ndef (GlobalHint a)
    = addGlobalHint ndef a
processFnOpt fc ndef ExternFn
    = setFlag fc ndef Inline -- if externally defined, inline when compiling
processFnOpt fc ndef (ForeignFn _)
    = setFlag fc ndef Inline -- if externally defined, inline when compiling
processFnOpt fc ndef Invertible
    = setFlag fc ndef Invertible
processFnOpt fc ndef (Totality tot)
    = setFlag fc ndef (SetTotal tot)
processFnOpt fc ndef Macro
    = setFlag fc ndef Macro
processFnOpt fc ndef (SpecArgs ns)
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact ndef (gamma defs)
              | Nothing => throw (UndefinedName fc ndef)
         nty <- nf defs [] (type gdef)
         ps <- getNamePos 0 nty
         specs <- collectSpec [] ps nty
         addDef ndef (record { specArgs = specs } gdef)
         pure ()
  where
    insertDeps : List Nat -> List (Name, Nat) -> List Name -> List Nat
    insertDeps acc ps [] = acc
    insertDeps acc ps (n :: ns)
        = case lookup n ps of
               Nothing => insertDeps acc ps ns
               Just pos => if pos `elem` acc
                              then insertDeps acc ps ns
                              else insertDeps (pos :: acc) ps ns

    collectSpec : List Nat -> List (Name, Nat) -> NF [] -> Core (List Nat)
    collectSpec acc ps (NBind tfc x (Pi _ _ nty) sc)
        = do defs <- get Ctxt
             empty <- clearDefs defs
             sc' <- sc defs (toClosure defaultOpts [] (Ref tfc Bound x))
             if x `elem` ns
                then do aty <- quote empty [] nty
                        let rs = getRefs (UN "_") aty
                        let acc' = insertDeps acc ps (x :: keys rs)
                        collectSpec acc' ps sc'
                else collectSpec acc ps sc'
    collectSpec acc ps _ = pure acc

    getNamePos : Nat -> NF [] -> Core (List (Name, Nat))
    getNamePos i (NBind tfc x (Pi _ _ _) sc)
        = do defs <- get Ctxt
             ns' <- getNamePos (1 + i) !(sc defs (toClosure defaultOpts [] (Erased tfc False)))
             pure ((x, i) :: ns')
    getNamePos _ _ = pure []

getFnString : {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              RawImp -> Core String
getFnString (IPrimVal _ (Str st)) = pure st
getFnString tm
    = do inidx <- resolveName (UN "[foreign]")
         let fc = getFC tm
         let gstr = gnf [] (PrimVal fc StringType)
         etm <- checkTerm inidx InExpr [] (MkNested []) [] tm gstr
         defs <- get Ctxt
         case !(nf defs [] etm) of
              NPrimVal fc (Str st) => pure st
              _ => throw (GenericMsg fc "%foreign calling convention must evaluate to a String")

-- If it's declared as externally defined, set the definition to
-- ExternFn <arity>, where the arity is assumed to be fixed (i.e.
-- not dependent on any of the arguments)
-- Similarly set foreign definitions. Possibly combine these?
initDef : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          Name -> Env Term vars -> Term vars -> List FnOpt -> Core Def
initDef n env ty []
    = do addUserHole n
         pure None
initDef n env ty (ExternFn :: opts)
    = do defs <- get Ctxt
         a <- getArity defs env ty
         pure (ExternDef a)
initDef n env ty (ForeignFn cs :: opts)
    = do defs <- get Ctxt
         a <- getArity defs env ty
         cs' <- traverse getFnString cs
         pure (ForeignDef a cs')
initDef n env ty (_ :: opts) = initDef n env ty opts

export
processType : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              List ElabOpt -> NestedNames vars -> Env Term vars ->
              FC -> RigCount -> Visibility ->
              List FnOpt -> ImpTy -> Core ()
processType {vars} eopts nest env fc rig vis opts (MkImpTy tfc n_in ty_raw)
    = do n <- inCurrentNS n_in

         log 1 $ "Processing " ++ show n
         log 5 $ "Checking type decl " ++ show n ++ " : " ++ show ty_raw
         idx <- resolveName n

         -- Check 'n' is undefined
         defs <- get Ctxt
         Nothing <- lookupCtxtExact (Resolved idx) (gamma defs)
              | Just _ => throw (AlreadyDefined fc n)

         ty <-
             wrapError (InType fc n) $
                   checkTerm idx InType (HolesOkay :: eopts) nest env
                             (IBindHere fc (PI erased) ty_raw)
                             (gType fc)
         logTermNF 3 ("Type of " ++ show n) [] (abstractEnvType tfc env ty)
         -- TODO: Check name visibility

         def <- initDef n env ty opts
         let fullty = abstractEnvType tfc env ty
         (erased, dterased) <- findErased fullty

         addDef (Resolved idx)
                (record { eraseArgs = erased,
                          safeErase = dterased }
                        (newDef fc n rig vars fullty vis def))
         -- Flag it as checked, because we're going to check the clauses
         -- from the top level.
         -- But, if it's a case block, it'll be checked as part of the top
         -- level check so don't set the flag.
         when (not (InCase `elem` eopts)) $ setLinearCheck idx True

         log 2 $ "Setting options for " ++ show n ++ ": " ++ show opts
         traverse (processFnOpt fc (Resolved idx)) opts

         -- Add to the interactive editing metadata
         addTyDecl fc (Resolved idx) env ty -- for definition generation
         addNameType fc (Resolved idx) env ty -- for looking up types

         traverse_ addToSave (keys (getMetas ty))
         addToSave n
         log 10 $ "Saving from " ++ show n ++ ": " ++ show (keys (getMetas ty))

         when (vis /= Private) $
              do addHash n
                 addHash ty
