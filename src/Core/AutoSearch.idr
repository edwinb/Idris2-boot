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
             (defaults : Bool) -> (depth : Nat) ->
             (defining : Name) -> (topTy : ClosedTerm) ->
             Env Term vars -> (target : Term vars) -> Core (Term vars)

record ArgInfo (vars : List Name) where
  constructor MkArgInfo
  holeID : Int
  argRig : RigCount
  appInf : AppInfo
  metaApp : Term vars
  argType : Term vars

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
         (idx, arg) <- newMeta fc argRig env nm argTy False
         setInvertible fc idx
         (rest, restTy) <- mkArgs fc rigc env 
                              !(sc defs (toClosure defaultOpts env arg))
         pure (MkArgInfo idx argRig (appInf Nothing p) arg argTy :: rest, restTy)
mkArgs fc rigc env ty = pure ([], ty)

searchIfHole : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               FC -> 
               (defaults : Bool) -> (ispair : Bool) -> (depth : Nat) ->
               (defining : Name) -> (topTy : ClosedTerm) -> Env Term vars -> 
               (arg : ArgInfo vars) -> 
               Core () 
searchIfHole fc defaults ispair Z def top env arg 
    = throw (CantSolveGoal fc [] top) -- possibly should say depth limit hit?
searchIfHole fc defaults ispair (S depth) def top env arg 
    = do let hole = holeID arg
         let rig = argRig arg

         defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved hole) (gamma defs)
              | Nothing => throw (CantSolveGoal fc [] top)
         let Hole inv = definition gdef
              | _ => pure () -- already solved
         let top' = if ispair 
                       then type gdef
                       else top

         argdef <- searchType fc rig defaults depth def top' env 
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
exactlyOne fc env top all
    = do elabs <- successful all
         case rights elabs of
              [(res, defs, ust)] => 
                    do put UST ust
                       put Ctxt defs
                       commit
                       pure res
              [] => throw (CantSolveGoal fc [] top)
              rs => throw (AmbiguousSearch fc env (map fst rs))

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
usableLocal loc defaults env (NApp fc (NMeta _ _ _) args)
    = pure False
usableLocal {vars} loc defaults env (NTCon _ n _ _ args)
    = do sd <- getSearchData loc (not defaults) n
         usableLocalArg 0 (detArgs sd) (map snd args)
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
                        !(traverse (evalClosure defs) (map snd args))
         pure (and (map Delay us))
usableLocal loc defaults env (NApp _ (NLocal _ _ _) args)
    = do defs <- get Ctxt
         us <- traverse (usableLocal loc defaults env) 
                        !(traverse (evalClosure defs) (map snd args))
         pure (and (map Delay us))
usableLocal loc defaults env (NBind fc x (Pi _ _ _) sc)
    = do defs <- get Ctxt
         usableLocal loc defaults env 
                !(sc defs (toClosure defaultOpts env (Erased fc)))
usableLocal loc _ _ _ = pure True

searchLocalWith : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  FC -> RigCount ->
                  (defaults : Bool) -> (depth : Nat) ->
                  (defining : Name) -> (topTy : ClosedTerm) ->
                  Env Term vars -> List (Term vars, Term vars) -> 
                  (target : NF vars) -> Core (Term vars)
searchLocalWith fc rigc defaults depth def top env [] target
    = throw (CantSolveGoal fc [] top)
searchLocalWith {vars} fc rigc defaults depth def top env ((prf, ty) :: rest) target
    = tryUnify 
         (do defs <- get Ctxt
             nty <- nf defs env ty
             findPos defs prf id nty target)
         (searchLocalWith fc rigc defaults depth def top env rest target)
  where
    findDirect : Defs -> Term vars -> 
                 (Term vars -> Term vars) ->
                 NF vars ->  -- local's type
                 (target : NF vars) -> 
                 Core (Term vars)
    findDirect defs prf f ty target
        = do (args, appTy) <- mkArgs fc rigc env ty
             -- We can only use the local if its type is not an unsolved hole
             if !(usableLocal fc defaults env ty)
                then do
                   ures <- unify InTerm fc env target appTy
                   let [] = constraints ures
                       | _ => throw (CantSolveGoal fc [] top)
                   let candidate = applyInfo fc (f prf) 
                                       (map (\i => (appInf i, metaApp i)) args)
                   logTermNF 10 "Candidate " env candidate
                   traverse (searchIfHole fc defaults False depth def top env) args
                   pure candidate
                else throw (CantSolveGoal fc [] top)

    findPos : Defs -> Term vars -> 
              (Term vars -> Term vars) ->
              NF vars ->  -- local's type
              (target : NF vars) -> 
              Core (Term vars)
    findPos defs prf f nty@(NTCon pfc pn _ _ [(xp, xty), (yp, yty)]) target
        = tryUnify (findDirect defs prf f nty target)
            (do fname <- maybe (throw (CantSolveGoal fc [] top))
                               pure
                               (fstName defs)
                sname <- maybe (throw (CantSolveGoal fc [] top))
                               pure
                               (sndName defs)
                if isPairType pn defs
                   then do empty <- clearDefs defs
                           xtytm <- quote empty env xty
                           ytytm <- quote empty env yty
                           tryUnify
                             (do xtynf <- evalClosure defs xty
                                 findPos defs prf 
                                     (\arg => applyInfo fc (Ref fc Func fname)
                                                [(xp, xtytm),
                                                 (yp, ytytm),
                                                 (explApp Nothing, f arg)])
                                     xtynf target)
                             (do ytynf <- evalClosure defs yty
                                 findPos defs prf 
                                     (\arg => applyInfo fc (Ref fc Func sname)
                                                [(xp, xtytm),
                                                 (yp, ytytm),
                                                 (explApp Nothing, f arg)])
                                     ytynf target)
                   else throw (CantSolveGoal fc [] top))
    findPos defs prf f nty target
        = findDirect defs prf f nty target

searchLocal : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount ->
              (defaults : Bool) -> (depth : Nat) ->
              (defining : Name) -> (topTy : ClosedTerm) ->
              Env Term vars -> 
              (target : NF vars) -> Core (Term vars)
searchLocal fc rig defaults depth def top env target
    = searchLocalWith fc rig defaults depth def top env (getAllEnv fc [] env) target

isPairNF : Env Term vars -> NF vars -> Defs -> Core Bool
isPairNF env (NTCon _ n _ _ _) defs
    = pure $ isPairType n defs
isPairNF env (NBind fc b (Pi _ _ _) sc) defs
    = isPairNF env !(sc defs (toClosure defaultOpts env (Erased fc))) defs
isPairNF _ _ _ = pure False

searchName : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             FC -> RigCount ->
             (defaults : Bool) -> (depth : Nat) ->
             (defining : Name) -> (topTy : ClosedTerm) ->
             Env Term vars -> (target : NF vars) -> 
             (Name, GlobalDef) -> 
             Core (Term vars)
searchName fc rigc defaults depth def top env target (n, ndef)
    = do defs <- get Ctxt
         let ty = type ndef
         let namety : NameType
                 = case definition ndef of
                        DCon tag arity => DataCon tag arity
                        TCon tag arity _ _ _ _ => TyCon tag arity
                        _ => Func
         nty <- nf defs env (embed ty)
         (args, appTy) <- mkArgs fc rigc env nty
         ures <- unify InTerm fc env target appTy
         let [] = constraints ures
             | _ => throw (CantSolveGoal fc [] top)
         ispair <- isPairNF env nty defs
         let candidate = applyInfo fc (Ref fc namety n) 
                              (map (\i => (appInf i, metaApp i)) args)
         logTermNF 10 "Candidate " env candidate
         traverse (searchIfHole fc defaults ispair depth def top env) args
         pure candidate

searchNames : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount ->
              (defaults : Bool) -> (depth : Nat) ->
              (defining : Name) -> (topTy : ClosedTerm) ->
              Env Term vars -> List Name -> 
              (target : NF vars) -> Core (Term vars)
searchNames fc rigc defaults depth defining topty env [] target
    = throw (CantSolveGoal fc [] topty)
searchNames fc rigc defaults depth defining topty env (n :: ns) target
    = do defs <- get Ctxt
         visnsm <- traverse (visible (gamma defs) (currentNS defs)) (n :: ns)
         let visns = mapMaybe id visnsm
         exactlyOne fc env topty 
            (map (searchName fc rigc defaults depth defining topty env target) visns)
  where
    visible : Context GlobalDef -> 
              List String -> Name -> Core (Maybe (Name, GlobalDef))
    visible gam nspace n
        = do Just def <- lookupCtxtExact n gam
                  | Nothing => pure Nothing
             if visibleIn nspace n (visibility def)
                then pure $ Just (n, def)
                else pure $ Nothing

concreteDets : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               FC -> Bool ->
               Env Term vars -> (top : ClosedTerm) -> 
               (pos : Nat) -> (dets : List Nat) -> 
               (args : List (AppInfo, Closure vars)) ->
               Core ()
concreteDets fc defaults env top pos dets [] = pure ()
concreteDets {vars} fc defaults env top pos dets ((p, arg) :: args)
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
        = do traverse (\ parg => do argnf <- evalClosure defs (snd parg)
                                    concrete defs argnf False) args
             pure ()
    concrete defs (NApp _ (NMeta n i _) _) True
        = throw (DeterminingArg fc n i [] top)
    concrete defs (NApp _ (NMeta n i _) _) False
        = throw (CantSolveGoal fc [] top)
    concrete defs tm top = pure ()

-- Declared at the top
searchType fc rigc defaults depth def top env (Bind nfc x (Pi c p ty) sc)
    = pure (Bind nfc x (Lam c p ty)
             !(searchType fc rigc defaults depth def top
                          (Pi c p ty :: env) sc))
searchType {vars} fc rigc defaults depth def top env target
    = do defs <- get Ctxt
         nty <- nf defs env target
         case nty of
              NTCon tfc tyn t a args =>
                  if a == length args
                     then do logNF 10 "Next target: " env nty
                             sd <- getSearchData fc defaults tyn
                             -- Check determining arguments are okay for 'args' 
                             concreteDets fc defaults env top 0 (detArgs sd) args
                             tryGroups nty (hintGroups sd)
                     else throw (CantSolveGoal fc [] top)
              _ => do logNF 10 "Next target: " env nty
                      searchLocal fc rigc defaults depth def top env nty
  where
    ambig : Error -> Bool
    ambig (AmbiguousSearch _ _ _) = True
    ambig _ = False
    
    tryGroups : NF vars -> List (List Name) -> Core (Term vars)
    tryGroups nty [] = throw (CantSolveGoal fc [] top)
    tryGroups nty (g :: gs)
        = handleUnify
             (searchNames fc rigc defaults depth def top env g nty)
             (\err => if ambig err || isNil gs
                         then throw err
                         else tryGroups nty gs)

-- Declared in Core.Unify as:
-- search : {auto c : Ref Ctxt Defs} ->
--          {auto u : Ref UST UState} ->
--          FC -> RigCount ->
--          (defaults : Bool) -> (depth : Nat) ->
--          (defining : Name) -> (topTy : Term vars) -> Env Term vars -> 
--          Core (Term vars)
Core.Unify.search fc rigc defaults depth def top env
    = do defs <- get Ctxt
         logTerm 10 "Initial target: " top
         tm <- searchType fc rigc defaults depth def 
                          (abstractEnvType fc env top) env 
                          !(normaliseScope defs env top)
         defs <- get Ctxt
         quote defs env tm
