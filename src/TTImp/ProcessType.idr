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
         ddeps <- collectDDeps nty
         specs <- collectSpec [] ddeps ps nty
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

    -- Collect the argument names which the dynamic args depend on
    collectDDeps : NF [] -> Core (List Name)
    collectDDeps (NBind tfc x (Pi _ _ nty) sc)
        = do defs <- get Ctxt
             empty <- clearDefs defs
             sc' <- sc defs (toClosure defaultOpts [] (Ref tfc Bound x))
             if x `elem` ns
                then collectDDeps sc'
                else do aty <- quote empty [] nty
                        -- Get names depended on by nty
                        let deps = keys (getRefs (UN "_") aty)
                        rest <- collectDDeps sc'
                        pure (rest ++ deps)
    collectDDeps _ = pure []

    -- Return names the type depends on, and whether it's a parameter
    mutual
      getDepsArgs : Bool -> List (NF []) -> NameMap Bool ->
                    Core (NameMap Bool)
      getDepsArgs inparam [] ns = pure ns
      getDepsArgs inparam (a :: as) ns
          = do ns' <- getDeps inparam a ns
               getDepsArgs inparam as ns'

      getDeps : Bool -> NF [] -> NameMap Bool ->
                Core (NameMap Bool)
      getDeps inparam (NBind _ x (Pi _ _ pty) sc) ns
          = do ns' <- getDeps inparam pty ns
               defs <- get Ctxt
               sc' <- sc defs (toClosure defaultOpts [] (Erased fc False))
               getDeps inparam sc' ns'
      getDeps inparam (NBind _ x b sc) ns
          = do ns' <- getDeps False (binderType b) ns
               defs <- get Ctxt
               sc' <- sc defs (toClosure defaultOpts [] (Erased fc False))
               getDeps False sc' ns
      getDeps inparam (NApp _ (NRef Bound n) args) ns
          = do defs <- get Ctxt
               ns' <- getDepsArgs False !(traverse (evalClosure defs) args) ns
               pure (insert n inparam ns')
      getDeps inparam (NDCon _ n t a args) ns
          = do defs <- get Ctxt
               getDepsArgs False !(traverse (evalClosure defs) args) ns
      getDeps inparam (NTCon _ n t a args) ns
          = do defs <- get Ctxt
               params <- case !(lookupDefExact n (gamma defs)) of
                              Just (TCon _ _ ps _ _ _ _ _) => pure ps
                              _ => pure []
               let (ps, ds) = splitPs 0 params args
               ns' <- getDepsArgs True !(traverse (evalClosure defs) ps) ns
               getDepsArgs False !(traverse (evalClosure defs) ds) ns'
        where
          -- Split into arguments in parameter position, and others
          splitPs : Nat -> List Nat -> List (Closure []) ->
                    (List (Closure []), List (Closure []))
          splitPs n params [] = ([], [])
          splitPs n params (x :: xs)
              = let (ps', ds') = splitPs (1 + n) params xs in
                    if n `elem` params
                       then (x :: ps', ds')
                       else (ps', x :: ds')
      getDeps inparam (NDelayed _ _ t) ns = getDeps inparam t ns
      getDeps inparams nf ns = pure ns

    -- If the name of an argument is in the list of specialisable arguments,
    -- record the position. Also record the position of anything the argument
    -- depends on which is only dependend on by declared static arguments.
    collectSpec : List Nat -> -- specialisable so far
                  List Name -> -- things depended on by dynamic args
                               -- We're assuming  it's a short list, so just use
                               -- List and don't worry about duplicates.
                  List (Name, Nat) -> NF [] -> Core (List Nat)
    collectSpec acc ddeps ps (NBind tfc x (Pi _ _ nty) sc)
        = do defs <- get Ctxt
             empty <- clearDefs defs
             sc' <- sc defs (toClosure defaultOpts [] (Ref tfc Bound x))
             if x `elem` ns
                then do deps <- getDeps True nty NameMap.empty
                        -- Get names depended on by nty
                        -- Keep the ones which are either:
                        --  * parameters
                        --  * not depended on by a dynamic argument (the ddeps)
                        let rs = filter (\x => snd x ||
                                               not (fst x `elem` ddeps))
                                        (toList deps)
                        let acc' = insertDeps acc ps (x :: map fst rs)
                        collectSpec acc' ddeps ps sc'
                else collectSpec acc ddeps ps sc'
    collectSpec acc ddeps ps _ = pure acc

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

-- Find the inferrable argument positions in a type. This is useful for
-- generalising partially evaluated definitions and (potentially) in interactive
-- editing
findInferrable : Defs -> NF [] -> Core (List Nat)
findInferrable defs ty = fi 0 0 [] [] ty
  where
    mutual
      -- Add to the inferrable arguments from the given type. An argument is
      -- inferrable if it's guarded by a constructor, or on its own
      findInf : List Nat -> List (Name, Nat) ->
                NF [] -> Core (List Nat)
      findInf acc pos (NApp _ (NRef Bound n) [])
          = case lookup n pos of
                 Nothing => pure acc
                 Just p => if p `elem` acc then pure acc else pure (p :: acc)
      findInf acc pos (NDCon _ _ _ _ args)
          = do args' <- traverse (evalClosure defs) args
               findInfs acc pos args'
      findInf acc pos (NTCon _ _ _ _ args)
          = do args' <- traverse (evalClosure defs) args
               findInfs acc pos args'
      findInf acc pos (NDelayed _ _ t) = findInf acc pos t
      findInf acc _ _ = pure acc

      findInfs : List Nat -> List (Name, Nat) -> List (NF []) -> Core (List Nat)
      findInfs acc pos [] = pure acc
      findInfs acc pos (n :: ns) = findInf !(findInfs acc pos ns) pos n

    fi : Nat -> Int -> List (Name, Nat) -> List Nat -> NF [] -> Core (List Nat)
    fi pos i args acc (NBind fc x (Pi _ _ aty) sc)
        = do let argn = MN "inf" i
             sc' <- sc defs (toClosure defaultOpts [] (Ref fc Bound argn))
             acc' <- findInf acc args aty
             rest <- fi (1 + pos) (1 + i) ((argn, pos) :: args) acc' sc'
             pure rest
    fi pos i args acc ret = findInf acc args ret

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
         defs <- get Ctxt
         empty <- clearDefs defs
         infargs <- findInferrable empty !(nf defs [] fullty)

         addDef (Resolved idx)
                (record { eraseArgs = erased,
                          safeErase = dterased,
                          inferrable = infargs }
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
