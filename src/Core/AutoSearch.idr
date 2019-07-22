module Core.AutoSearch

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Unify
import Core.Value

%default covering

SearchEnv : List Name -> Type
SearchEnv vars = List (NF vars, Closure vars)

searchType : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             FC -> RigCount ->
             (defaults : Bool) -> (trying : List (Term vars)) ->
             (depth : Nat) ->
             (defining : Name) -> 
             (checkDets : Bool) -> (topTy : ClosedTerm) ->
             Env Term vars -> (target : Term vars) -> Core (Term vars)

public export
record ArgInfo (vars : List Name) where
  constructor MkArgInfo
  holeID : Int
  argRig : RigCount
  plicit : PiInfo
  metaApp : Term vars
  argType : Term vars

export
mkArgs : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         FC -> RigCount ->
         Env Term vars -> NF vars -> 
         Core (List (ArgInfo vars), NF vars)
mkArgs fc rigc env (NBind nfc x (Pi c p ty) sc)
    = do defs <- get Ctxt
         empty <- clearDefs defs
         nm <- genName "sa"
         argTy <- quote empty env ty
         let argRig = rigMult rigc c
         (idx, arg) <- newMeta fc argRig env nm argTy 
                               (Hole (length env) False False) False
         setInvertible fc idx
         (rest, restTy) <- mkArgs fc rigc env 
                              !(sc defs (toClosure defaultOpts env arg))
         pure (MkArgInfo idx argRig p arg argTy :: rest, restTy)
mkArgs fc rigc env ty = pure ([], ty)

searchIfHole : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               FC -> 
               (defaults : Bool) -> List (Term vars) ->
               (ispair : Bool) -> (depth : Nat) ->
               (defining : Name) -> (topTy : ClosedTerm) -> Env Term vars -> 
               (arg : ArgInfo vars) -> 
               Core () 
searchIfHole fc defaults trying ispair Z def top env arg 
    = throw (CantSolveGoal fc [] top) -- possibly should say depth limit hit?
searchIfHole fc defaults trying ispair (S depth) def top env arg 
    = do let hole = holeID arg
         let rig = argRig arg

         defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved hole) (gamma defs)
              | Nothing => throw (CantSolveGoal fc [] top)
         let Hole _ _ inv = definition gdef
              | _ => pure () -- already solved
         top' <- if ispair 
                    then normaliseScope defs [] (type gdef)
                    else pure top

         argdef <- searchType fc rig defaults trying depth def False top' env 
                              !(normaliseScope defs env (argType arg))
         vs <- unify InTerm fc env (metaApp arg) argdef
         let [] = constraints vs
              | _ => throw (CantSolveGoal fc [] top)
         pure ()

successful : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             List (Core (Term vars)) ->
             Core (List (Either Error (Term vars, Defs, UState)))
successful [] = pure []
successful (elab :: elabs)
    = do ust <- get UST
         defs <- branch
         catch (do -- Run the elaborator 
                   res <- elab
                   -- Record post-elaborator state
                   ust' <- get UST
                   defs' <- get Ctxt
                   -- Reset to previous state and try the rest
                   put UST ust
                   put Ctxt defs
                   elabs' <- successful elabs
                   -- Record success, and the state we ended at
                   pure (Right (res, defs', ust') :: elabs'))
               (\err => do put UST ust
                           put Ctxt defs
                           elabs' <- successful elabs
                           pure (Left err :: elabs'))

anyOne : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         FC -> Env Term vars -> (topTy : ClosedTerm) ->
         List (Core (Term vars)) ->
         Core (Term vars)
anyOne fc env top [] = throw (CantSolveGoal fc [] top)
anyOne fc env top (elab :: elabs)
    = tryUnify elab (anyOne fc env top elabs)

exactlyOne : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             FC -> Env Term vars -> (topTy : ClosedTerm) ->
             List (Core (Term vars)) ->
             Core (Term vars)
exactlyOne fc env top [elab] 
    = catch elab
         (\err => case err of
                       CantSolveGoal _ _ _ => throw err
                       _ => throw (CantSolveGoal fc [] top))
exactlyOne {vars} fc env top all
    = do elabs <- successful all
         case rights elabs of
              [(res, defs, ust)] => 
                    do put UST ust
                       put Ctxt defs
                       commit
                       pure res
              [] => throw (CantSolveGoal fc [] top)
              rs => throw (AmbiguousSearch fc env 
                             !(traverse normRes rs))
  where
    normRes : (Term vars, Defs, UState) -> Core (Term vars)
    normRes (tm, defs, _) = normaliseHoles defs env tm

-- We can only resolve things which are at any multiplicity. Expression
-- search happens before linearity checking and we can't guarantee that just
-- because something is apparently available now, it will be available by the
-- time we get to linearity checking.
getAllEnv : FC -> (done : List Name) -> 
            Env Term vars -> List (Term (done ++ vars), Term (done ++ vars))
getAllEnv fc done [] = []
getAllEnv {vars = v :: vs} fc done (b :: env) 
   = let rest = getAllEnv fc (done ++ [v]) env in 
         if multiplicity b == RigW
            then let MkVar p = weakenVar {name=v} {inner=v :: vs} done First in
                     (Local fc Nothing _ p, 
                       rewrite appendAssociative done [v] vs in 
                          weakenNs (done ++ [v]) (binderType b)) :: 
                               rewrite appendAssociative done [v] vs in rest
            else rewrite appendAssociative done [v] vs in rest

-- A local is usable if it contains no holes in a determining argument position
usableLocal : {auto c : Ref Ctxt Defs} ->
              FC -> (defaults : Bool) -> 
              Env Term vars -> (locTy : NF vars) -> Core Bool
-- pattern variables count as concrete things!
usableLocal loc defaults env (NApp fc (NMeta (PV _ _) _ _) args)
    = pure True
usableLocal loc defaults env (NApp fc (NMeta _ _ _) args)
    = pure False
usableLocal {vars} loc defaults env (NTCon _ n _ _ args)
    = do sd <- getSearchData loc (not defaults) n
         usableLocalArg 0 (detArgs sd) args
  -- usable if none of the determining arguments of the local's type are
  -- holes
  where
    usableLocalArg : Nat -> List Nat -> List (Closure vars) -> Core Bool
    usableLocalArg i dets [] = pure True
    usableLocalArg i dets (c :: cs)
        = if i `elem` dets
             then do defs <- get Ctxt
                     u <- usableLocal loc defaults env !(evalClosure defs c) 
                     if u
                        then usableLocalArg (1 + i) dets cs
                        else pure False
             else usableLocalArg (1 + i) dets cs
usableLocal loc defaults env (NDCon _ n _ _ args)
    = do defs <- get Ctxt
         us <- traverse (usableLocal loc defaults env) 
                        !(traverse (evalClosure defs) args)
         pure (and (map Delay us))
usableLocal loc defaults env (NApp _ (NLocal _ _ _) args)
    = do defs <- get Ctxt
         us <- traverse (usableLocal loc defaults env) 
                        !(traverse (evalClosure defs) args)
         pure (and (map Delay us))
usableLocal loc defaults env (NBind fc x (Pi _ _ _) sc)
    = do defs <- get Ctxt
         usableLocal loc defaults env 
                !(sc defs (toClosure defaultOpts env (Erased fc)))
usableLocal loc _ _ _ = pure True

searchLocalWith : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  FC -> RigCount ->
                  (defaults : Bool) -> List (Term vars) ->
                  (depth : Nat) ->
                  (defining : Name) -> (topTy : ClosedTerm) ->
                  Env Term vars -> List (Term vars, Term vars) -> 
                  (target : NF vars) -> Core (Term vars)
searchLocalWith fc rigc defaults trying depth def top env [] target
    = throw (CantSolveGoal fc [] top)
searchLocalWith {vars} fc rigc defaults trying depth def top env ((prf, ty) :: rest) target
    = tryUnify 
         (do defs <- get Ctxt
             nty <- nf defs env ty
             findPos defs prf id nty target)
         (searchLocalWith fc rigc defaults trying depth def top env rest target)
  where
    clearEnvType : {idx : Nat} -> .(IsVar name idx vs) -> 
                   FC -> Env Term vs -> Env Term vs
    clearEnvType First fc (b :: env) 
        = Lam (multiplicity b) Explicit (Erased fc) :: env
    clearEnvType (Later p) fc (b :: env) = b :: clearEnvType p fc env

    clearEnv : Term vars -> Env Term vars -> Env Term vars
    clearEnv (Local fc _ idx p) env
        = clearEnvType p fc env
    clearEnv _ env = env

    findDirect : Defs -> Term vars -> 
                 (Term vars -> Term vars) ->
                 NF vars ->  -- local's type
                 (target : NF vars) -> 
                 Core (Term vars)
    findDirect defs prf f ty target
        = do (args, appTy) <- mkArgs fc rigc env ty
             logNF 10 "Trying" env ty
             logNF 10 "For target" env target
             ures <- unify InTerm fc env target appTy
             let [] = constraints ures
                 | _ => throw (CantSolveGoal fc [] top)
             -- We can only use the local if its type is not an unsolved hole
             if !(usableLocal fc defaults env ty)
                then do
                   let candidate = apply fc (f prf) (map metaApp args)
                   logTermNF 10 "Local var candidate " env candidate
                   -- Clear the local from the environment to avoid getting
                   -- into a loop repeatedly applying it
                   let env' = clearEnv prf env
                   -- Work right to left, because later arguments may solve
                   -- earlier ones by unification
                   traverse (searchIfHole fc defaults trying False depth def top env') 
                            (reverse args)
                   pure candidate
                else do logNF 10 "Can't use " env ty
                        throw (CantSolveGoal fc [] top)

    findPos : Defs -> Term vars -> 
              (Term vars -> Term vars) ->
              NF vars ->  -- local's type
              (target : NF vars) -> 
              Core (Term vars)
    findPos defs prf f nty@(NTCon pfc pn _ _ [xty, yty]) target
        = tryUnify (findDirect defs prf f nty target)
            (do fname <- maybe (throw (CantSolveGoal fc [] top))
                               pure
                               !fstName
                sname <- maybe (throw (CantSolveGoal fc [] top))
                               pure
                               !sndName
                if !(isPairType pn)
                   then do empty <- clearDefs defs
                           xtytm <- quote empty env xty
                           ytytm <- quote empty env yty
                           tryUnify
                             (do xtynf <- evalClosure defs xty
                                 findPos defs prf 
                                     (\arg => apply fc (Ref fc Func fname)
                                                        [xtytm,
                                                         ytytm,
                                                         f arg])
                                     xtynf target)
                             (do ytynf <- evalClosure defs yty
                                 findPos defs prf 
                                     (\arg => apply fc (Ref fc Func sname)
                                                        [xtytm,
                                                         ytytm,
                                                         f arg])
                                     ytynf target)
                   else throw (CantSolveGoal fc [] top))
    findPos defs prf f nty target
        = findDirect defs prf f nty target

searchLocal : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount ->
              (defaults : Bool) -> List (Term vars) ->
              (depth : Nat) ->
              (defining : Name) -> (topTy : ClosedTerm) ->
              Env Term vars -> 
              (target : NF vars) -> Core (Term vars)
searchLocal fc rig defaults trying depth def top env target
    = searchLocalWith fc rig defaults trying depth def top env (getAllEnv fc [] env) target

isPairNF : {auto c : Ref Ctxt Defs} ->
           Env Term vars -> NF vars -> Defs -> Core Bool
isPairNF env (NTCon _ n _ _ _) defs
    = isPairType n
isPairNF env (NBind fc b (Pi _ _ _) sc) defs
    = isPairNF env !(sc defs (toClosure defaultOpts env (Erased fc))) defs
isPairNF _ _ _ = pure False

searchName : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             FC -> RigCount ->
             (defaults : Bool) -> List (Term vars) ->
             (depth : Nat) ->
             (defining : Name) -> (topTy : ClosedTerm) ->
             Env Term vars -> (target : NF vars) -> 
             (Name, GlobalDef) -> 
             Core (Term vars)
searchName fc rigc defaults trying depth def top env target (n, ndef)
    = do defs <- get Ctxt
         when (not (visibleInAny (!getNS :: !getNestedNS) 
                                 (fullname ndef) (visibility ndef))) $
            throw (CantSolveGoal fc [] top)
         when (BlockedHint `elem` flags ndef) $
            throw (CantSolveGoal fc [] top)

         let ty = type ndef
         let namety : NameType
                 = case definition ndef of
                        DCon tag arity => DataCon tag arity
                        TCon tag arity _ _ _ _ => TyCon tag arity
                        _ => Func
         nty <- nf defs env (embed ty)
         logNF 10 ("Searching Name " ++ show n) env nty
         (args, appTy) <- mkArgs fc rigc env nty
         ures <- unify InTerm fc env target appTy
         let [] = constraints ures
             | _ => throw (CantSolveGoal fc [] top)
         ispair <- isPairNF env nty defs
         let candidate = apply fc (Ref fc namety n) (map metaApp args)
         logTermNF 10 "Candidate " env candidate
         -- Work right to left, because later arguments may solve earlier
         -- dependencies by unification
         traverse (searchIfHole fc defaults trying ispair depth def top env) 
                  (reverse args)
         pure candidate

searchNames : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount ->
              (defaults : Bool) -> List (Term vars) ->
              (depth : Nat) ->
              (defining : Name) -> (topTy : ClosedTerm) ->
              Env Term vars -> Bool -> List Name -> 
              (target : NF vars) -> Core (Term vars)
searchNames fc rigc defaults trying depth defining topty env ambig [] target
    = throw (CantSolveGoal fc [] topty)
searchNames fc rigc defaults trying depth defining topty env ambig (n :: ns) target
    = do defs <- get Ctxt
         visnsm <- traverse (visible (gamma defs) (currentNS defs :: nestedNS defs)) (n :: ns)
         let visns = mapMaybe id visnsm
         let elabs = map (searchName fc rigc defaults trying depth defining topty env target) visns
         if ambig
            then anyOne fc env topty elabs
            else exactlyOne fc env topty elabs
  where
    visible : Context -> 
              List (List String) -> Name -> Core (Maybe (Name, GlobalDef))
    visible gam nspace n
        = do Just def <- lookupCtxtExact n gam
                  | Nothing => pure Nothing
             if visibleInAny nspace n (visibility def)
                then pure $ Just (n, def)
                else pure $ Nothing

concreteDets : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               FC -> Bool ->
               Env Term vars -> (top : ClosedTerm) -> 
               (pos : Nat) -> (dets : List Nat) -> 
               (args : List (Closure vars)) ->
               Core ()
concreteDets fc defaults env top pos dets [] = pure ()
concreteDets {vars} fc defaults env top pos dets (arg :: args)
    = if not (pos `elem` dets)
         then concreteDets fc defaults env top (1 + pos) dets args
         else do defs <- get Ctxt
                 argnf <- evalClosure defs arg
                 concrete defs argnf True
                 concreteDets fc defaults env top (1 + pos) dets args
  where
    concrete : Defs -> NF vars -> (top : Bool) -> Core ()
    concrete defs (NBind nfc x b sc) top
        = do scnf <- sc defs (toClosure defaultOpts env (Erased nfc))
             concrete defs scnf False
    concrete defs (NTCon nfc n t a args) top
        = do traverse (\ parg => do argnf <- evalClosure defs parg
                                    concrete defs argnf False) args
             pure ()
    concrete defs (NDCon nfc n t a args) top
        = do traverse (\ parg => do argnf <- evalClosure defs parg
                                    concrete defs argnf False) args
             pure ()
    concrete defs (NApp _ (NMeta n i _) _) True
        = do Just (Hole _ True _) <- lookupDefExact n (gamma defs)
                  | _ => throw (DeterminingArg fc n i [] top)
             pure ()
    concrete defs (NApp _ (NMeta n i _) _) False
        = do Just (Hole _ True _) <- lookupDefExact n (gamma defs)
                  | def => throw (CantSolveGoal fc [] top)
             pure ()
    concrete defs tm top = pure ()

checkConcreteDets : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    FC -> Bool ->
                    Env Term vars -> (top : ClosedTerm) -> 
                    NF vars ->
                    Core ()
checkConcreteDets fc defaults env top (NTCon tfc tyn t a args) 
    = do defs <- get Ctxt
         if !(isPairType tyn)
            then case args of
                      [aty, bty] => 
                          do anf <- evalClosure defs aty
                             bnf <- evalClosure defs bty
                             checkConcreteDets fc defaults env top anf
                             checkConcreteDets fc defaults env top bnf
                      _ => do sd <- getSearchData fc defaults tyn
                              concreteDets fc defaults env top 0 (detArgs sd) args
            else 
              do sd <- getSearchData fc defaults tyn
                 concreteDets fc defaults env top 0 (detArgs sd) args
checkConcreteDets fc defaults env top _
    = pure ()

abandonIfCycle : {auto c : Ref Ctxt Defs} ->
                 Env Term vars -> Term vars -> List (Term vars) -> 
                 Core ()
abandonIfCycle env tm [] = pure ()
abandonIfCycle env tm (ty :: tys)
    = do defs <- get Ctxt
         if !(convert defs env tm ty)
            then throw (InternalError "Cycle in search")
            else abandonIfCycle env tm tys

-- Declared at the top
searchType fc rigc defaults trying depth def checkdets top env (Bind nfc x (Pi c p ty) sc)
    = pure (Bind nfc x (Lam c p ty)
             !(searchType fc rigc defaults [] depth def checkdets top
                          (Pi c p ty :: env) sc))
searchType fc rigc defaults trying depth def checkdets top env (Bind nfc x (Let c val ty) sc)
    = pure (Bind nfc x (Let c val ty)
             !(searchType fc rigc defaults [] depth def checkdets top
                          (Let c val ty :: env) sc))
searchType {vars} fc rigc defaults trying depth def checkdets top env target
    = do defs <- get Ctxt
         abandonIfCycle env target trying
         let trying' = target :: trying
         nty <- nf defs env target
         case nty of
              NTCon tfc tyn t a args =>
                  if a == length args
                     then do logNF 10 "Next target" env nty
                             sd <- getSearchData fc defaults tyn
                             -- Check determining arguments are okay for 'args' 
                             when checkdets $
                                 checkConcreteDets fc defaults env top
                                                   (NTCon tfc tyn t a args)
                             tryUnify
                               (searchLocal fc rigc defaults trying' depth def top env nty)
                               (tryGroups Nothing nty (hintGroups sd))
                     else throw (CantSolveGoal fc [] top)
              _ => do logNF 10 "Next target: " env nty
                      searchLocal fc rigc defaults trying' depth def top env nty
  where
    ambig : Error -> Bool
    ambig (AmbiguousSearch _ _ _) = True
    ambig _ = False
    
    -- Take the earliest error message (that's when we look inside pairs,
    -- typically, and it's best to be more precise)
    tryGroups : Maybe Error ->
                NF vars -> List (Bool, List Name) -> Core (Term vars)
    tryGroups (Just err) nty [] = throw err
    tryGroups Nothing nty [] = throw (CantSolveGoal fc [] top)
    tryGroups merr nty ((ambigok, g) :: gs)
        = handleUnify
             (do logC 5 (do gn <- traverse getFullName g
                            pure ("Search: Trying " ++ show (length gn) ++
                                           " names " ++ show gn))
                 logNF 5 "For target" env nty
                 searchNames fc rigc defaults (target :: trying) depth def top env ambigok g nty)
             (\err => if ambig err then throw err
                         else tryGroups (maybe (Just err) Just merr) nty gs)

-- Declared in Core.Unify as:
-- search : {auto c : Ref Ctxt Defs} ->
--          {auto u : Ref UST UState} ->
--          FC -> RigCount ->
--          (defaults : Bool) -> (depth : Nat) ->
--          (defining : Name) -> (topTy : Term vars) -> Env Term vars -> 
--          Core (Term vars)
Core.Unify.search fc rigc defaults depth def top env
    = do defs <- get Ctxt
         logTermNF 2 "Initial target: " env top
         log 2 $ "Running search with defaults " ++ show defaults
         tm <- searchType fc rigc defaults [] depth def 
                          True (abstractEnvType fc env top) env 
                          top
         logTerm 2 "Result" tm
         defs <- get Ctxt
         pure tm
