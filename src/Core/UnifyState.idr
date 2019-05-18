module Core.UnifyState

import Core.Context
import Core.Core
import Core.Env
import Core.FC
import Core.TT
import Core.TTC
import Utils.Binary

import Data.IntMap
import Data.NameMap

%default covering

public export
data Constraint : Type where
     -- An unsolved constraint, noting two terms which need to be convertible
     -- in a particular environment
     MkConstraint : {vars : _} ->
                    FC -> 
                    (env : Env Term vars) ->
                    (x : Term vars) -> (y : Term vars) -> 
                    Constraint
     -- An unsolved sequence of constraints, arising from arguments in an
     -- application where solving later constraints relies on solving earlier
     -- ones
     MkSeqConstraint : {vars : _} ->
                       FC ->
                       (env : Env Term vars) ->
                       (xs : List (Term vars)) ->
                       (ys : List (Term vars)) ->
                       Constraint
     -- A resolved constraint
     Resolved : Constraint

export
TTC Constraint where
  toBuf b (MkConstraint {vars} fc env x y) 
     = do tag 0; toBuf b vars; toBuf b fc; toBuf b env; toBuf b x; toBuf b y
  toBuf b (MkSeqConstraint {vars} fc env xs ys)
     = do tag 1; toBuf b vars; toBuf b fc; toBuf b env; toBuf b xs; toBuf b ys
  toBuf b Resolved = tag 2

  fromBuf r b 
      = case !getTag of
             0 => do vars <- fromBuf r b
                     fc <- fromBuf r b; env <- fromBuf r b
                     x <- fromBuf r b; y <- fromBuf r b
                     pure (MkConstraint {vars} fc env x y)
             1 => do vars <- fromBuf r b
                     fc <- fromBuf r b; env <- fromBuf r b
                     xs <- fromBuf r b; ys <- fromBuf r b
                     pure (MkSeqConstraint {vars} fc env xs ys)
             2 => pure Resolved
             _ => corrupt "Constraint"

public export
record UState where
  constructor MkUState
  holes : IntMap (FC, Name) -- All metavariables with no definition yet.
                            -- 'Int' is the 'Resolved' name
  guesses : IntMap (FC, Name) -- Names which will be defined when constraints solved
                              -- (also includes auto implicit searches)
  currentHoles : IntMap (FC, Name) -- Holes introduced this elaboration session
  delayedHoles : IntMap (FC, Name) -- Holes left unsolved after an elaboration,
                                   -- so we need to check again at the end whether
                                   -- they have been solved later. Doesn't include
                                   -- user defined hole names, which don't need
                                   -- to have been solved
  constraints : IntMap Constraint -- map for finding constraints by ID
  nextName : Int
  nextConstraint : Int
  delayedElab : List (Int, Core ClosedTerm)
                -- Elaborators which we need to try again later, because
                -- we didn't have enough type information to elaborate
                -- successfully yet.
                -- The 'Int' is the resolved name. Delays can't be nested,
                -- so we just process them in order.

export
initUState : UState
initUState = MkUState empty empty empty empty empty 0 0 []

export
data UST : Type where

-- Generate a global name based on the given root, in the current namespace
export
genName : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          String -> Core Name
genName str
    = do ust <- get UST
         put UST (record { nextName $= (+1) } ust)
         n <- inCurrentNS (MN str (nextName ust))
         pure n

-- Generate a global name based on the given name, in the current namespace
export
genMVName : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Name -> Core Name
genMVName (UN str) = genName str
genMVName n
    = do ust <- get UST
         put UST (record { nextName $= (+1) } ust)
         mn <- inCurrentNS (MN (show n) (nextName ust))
         pure mn

-- Generate a unique variable name based on the given root
export
genVarName : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             String -> Core Name
genVarName str
    = do ust <- get UST
         put UST (record { nextName $= (+1) } ust)
         pure (MN str (nextName ust))

-- Again, for case names
export
genCaseName : {auto u : Ref UST UState} ->
			     		Int -> Core Name
genCaseName root
    = do ust <- get UST
         put UST (record { nextName $= (+1) } ust)
         pure (CaseBlock root (nextName ust))

addHoleName : {auto u : Ref UST UState} ->
              FC -> Name -> Int -> Core ()
addHoleName fc n i
    = do ust <- get UST
         put UST (record { holes $= insert i (fc, n),
                           currentHoles $= insert i (fc, n) } ust)

addGuessName : {auto u : Ref UST UState} ->
               FC -> Name -> Int -> Core ()
addGuessName fc n i
    = do ust <- get UST
         put UST (record { guesses $= insert i (fc, n)  } ust)

export
removeHole : {auto u : Ref UST UState} ->
             Int -> Core ()
removeHole n
    = do ust <- get UST
         put UST (record { holes $= delete n,
                           currentHoles $= delete n,
                           delayedHoles $= delete n } ust)

export
removeHoleName : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 Name -> Core ()
removeHoleName n
    = do defs <- get Ctxt
         let Just i = getNameID n (gamma defs)
             | Nothing => pure ()
         removeHole i

export
saveHoles : {auto u : Ref UST UState} ->
            Core (IntMap (FC, Name))
saveHoles
    = do ust <- get UST
         put UST (record { currentHoles = empty } ust)
         pure (currentHoles ust)

export
restoreHoles : {auto u : Ref UST UState} ->
               IntMap (FC, Name) -> Core ()
restoreHoles hs
    = do ust <- get UST
         put UST (record { currentHoles = hs } ust)

export
removeGuess : {auto u : Ref UST UState} ->
              Int -> Core ()
removeGuess n
    = do ust <- get UST
         put UST (record { guesses $= delete n } ust)

-- Get all of the hole data
export
getHoles : {auto u : Ref UST UState} ->
           Core (IntMap (FC, Name))
getHoles
    = do ust <- get UST
         pure (holes ust)

-- Get all of the guess data
export
getGuesses : {auto u : Ref UST UState} ->
           Core (IntMap (FC, Name))
getGuesses
    = do ust <- get UST
         pure (guesses ust)

-- Get the hole data for holes in the current elaboration session
-- (i.e. since the last 'saveHoles')
export
getCurrentHoles : {auto u : Ref UST UState} ->
                  Core (IntMap (FC, Name))
getCurrentHoles
    = do ust <- get UST
         pure (currentHoles ust)

export
isHole : {auto u : Ref UST UState} ->
         Int -> Core Bool
isHole i
    = do ust <- get UST
         pure (maybe False (const True) (lookup i (holes ust)))

export
isCurrentHole : {auto u : Ref UST UState} ->
                Int -> Core Bool
isCurrentHole i
    = do ust <- get UST
         pure (maybe False (const True) (lookup i (currentHoles ust)))

export
setConstraint : {auto u : Ref UST UState} ->
                Int -> Constraint -> Core ()
setConstraint cid c
    = do ust <- get UST
         put UST (record { constraints $= insert cid c } ust)

export
deleteConstraint : {auto u : Ref UST UState} ->
                Int -> Core ()
deleteConstraint cid
    = do ust <- get UST
         put UST (record { constraints $= delete cid } ust)

export
addConstraint : {auto u : Ref UST UState} ->
                {auto c : Ref Ctxt Defs} ->
                Constraint -> Core Int
addConstraint constr
    = do ust <- get UST
         let cid = nextConstraint ust
         put UST (record { constraints $= insert cid constr,
                           nextConstraint = cid+1 } ust)
         pure cid

mkConstantAppArgs : Bool -> FC -> Env Term vars -> 
                    (wkns : List Name) ->
                    List (Term (wkns ++ (vars ++ done)))
mkConstantAppArgs lets fc [] wkns = []
mkConstantAppArgs {done} {vars = x :: xs} lets fc (b :: env) wkns
    = let rec = mkConstantAppArgs {done} lets fc env (wkns ++ [x]) in
          if lets || notLet b
             then Local fc Nothing (length wkns) (mkVar wkns) :: 
                  rewrite (appendAssociative wkns [x] (xs ++ done)) in rec
             else rewrite (appendAssociative wkns [x] (xs ++ done)) in rec
  where
    notLet : Binder (Term vars) -> Bool
    notLet (Let _ _ _) = False
    notLet _ = True

    mkVar : (wkns : List Name) ->
            IsVar name (length wkns) (wkns ++ name :: vars ++ done)
    mkVar [] = First
    mkVar (w :: ws) = Later (mkVar ws)

mkConstantAppArgsOthers : Bool -> FC -> Env Term vars ->
                          SubVars smaller vars ->
                          (wkns : List Name) ->
                          List (Term (wkns ++ (vars ++ done)))
mkConstantAppArgsOthers lets fc [] p wkns = []
mkConstantAppArgsOthers {done} {vars = x :: xs} 
                        lets fc (b :: env) SubRefl wkns
    = rewrite appendAssociative wkns [x] (xs ++ done) in
              mkConstantAppArgsOthers lets fc env SubRefl (wkns ++ [x])
mkConstantAppArgsOthers {done} {vars = x :: xs} 
                        lets fc (b :: env) (KeepCons p) wkns
    = rewrite appendAssociative wkns [x] (xs ++ done) in
              mkConstantAppArgsOthers lets fc env p (wkns ++ [x])
mkConstantAppArgsOthers {done} {vars = x :: xs} 
                        lets fc (b :: env) (DropCons p) wkns
    = let rec = mkConstantAppArgsOthers {done} lets fc env p (wkns ++ [x]) in
          if lets || notLet b
             then Local fc Nothing (length wkns) (mkVar wkns) :: 
                  rewrite appendAssociative wkns [x] (xs ++ done) in rec
             else rewrite appendAssociative wkns [x] (xs ++ done) in rec
  where
    notLet : Binder (Term vars) -> Bool
    notLet (Let _ _ _) = False
    notLet _ = True

    mkVar : (wkns : List Name) ->
            IsVar name (length wkns) (wkns ++ name :: vars ++ done)
    mkVar [] = First
    mkVar (w :: ws) = Later (mkVar ws)


export
applyTo : FC -> Term vars -> Env Term vars -> Term vars
applyTo {vars} fc tm env
  = let args = reverse (mkConstantAppArgs {done = []} False fc env []) in
        apply fc (explApp Nothing) tm (rewrite sym (appendNilRightNeutral vars) in args)

export
applyToFull : FC -> Term vars -> Env Term vars -> Term vars
applyToFull {vars} fc tm env
  = let args = reverse (mkConstantAppArgs {done = []} True fc env []) in
        apply fc (explApp Nothing) tm (rewrite sym (appendNilRightNeutral vars) in args)

export
applyToOthers : FC -> Term vars -> Env Term vars -> 
                SubVars smaller vars -> Term vars
applyToOthers {vars} fc tm env sub
  = let args = reverse (mkConstantAppArgsOthers {done = []} False fc env sub []) in
        apply fc (explApp Nothing) tm (rewrite sym (appendNilRightNeutral vars) in args)

-- Create a new metavariable with the given name and return type,
-- and return a term which is the metavariable applied to the environment
-- (and which has the given type)
export
newMeta : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          FC -> RigCount ->
          Env Term vars -> Name -> Term vars -> Bool -> Core (Int, Term vars)
newMeta {vars} fc rig env n ty nocyc
    = do let hty = abstractEnvType fc env ty
         let hole = record { noCycles = nocyc }
                           (newDef fc n rig hty Public (Hole False))
         log 5 $ "Adding new meta " ++ show (n, fc, rig)
         idx <- addDef n hole 
         addHoleName fc n idx
         pure (idx, Meta fc n idx envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} False fc env []) in
                  rewrite sym (appendNilRightNeutral vars) in args

mkConstant : FC -> Env Term vars -> Term vars -> ClosedTerm
mkConstant fc [] tm = tm
mkConstant {vars = x :: _} fc (Let c val ty :: env) tm
    = mkConstant fc env (Bind fc x (Let c val ty) tm)
mkConstant {vars = x :: _} fc (b :: env) tm 
    = let ty = binderType b in
          mkConstant fc env (Bind fc x (Lam (multiplicity b) Explicit ty) tm)

-- Given a term and a type, add a new guarded constant to the global context
-- by applying the term to the current environment
-- Return the replacement term (the name applied to the environment)
export
newConstant : {auto u : Ref UST UState} ->
              {auto c : Ref Ctxt Defs} ->
              FC -> RigCount -> Env Term vars -> 
              (tm : Term vars) -> (ty : Term vars) ->
              (constrs : List Int) ->
              Core (Term vars)
newConstant {vars} fc rig env tm ty constrs
    = do let def = mkConstant fc env tm
         let defty = abstractEnvType fc env ty
         cn <- genName "postpone"
         let guess = newDef fc cn rig defty Public (Guess def constrs)
         idx <- addDef cn guess
         addGuessName fc cn idx
         pure (Meta fc cn idx envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} False fc env []) in
                  rewrite sym (appendNilRightNeutral vars) in args

-- Create a new search with the given name and return type,
-- and return a term which is the name applied to the environment
-- (and which has the given type)
export
newSearch : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            FC -> RigCount -> Nat -> Name ->
            Env Term vars -> Name -> Term vars -> Core (Int, Term vars)
newSearch {vars} fc rig depth def env n ty
    = do let hty = abstractEnvType fc env ty
         let hole = newDef fc n rig hty Public (BySearch rig depth def)
         log 10 $ "Adding new search " ++ show n
         idx <- addDef n hole 
         addGuessName fc n idx
         pure (idx, Meta fc n idx envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} False fc env []) in
                  rewrite sym (appendNilRightNeutral vars) in args

-- Add a hole which stands for a delayed elaborator
export
newDelayed : {auto u : Ref UST UState} ->
             {auto c : Ref Ctxt Defs} ->       
             FC -> RigCount -> 
             Env Term vars -> Name ->
             (ty : Term vars) -> Core (Int, Term vars)
newDelayed {vars} fc rig env n ty
    = do let hty = abstractEnvType fc env ty
         let hole = newDef fc n rig hty Public Delayed
         idx <- addDef n hole
         log 10 $ "Added delayed elaborator " ++ show (n, idx)
         addHoleName fc n idx
         pure (idx, Meta fc n idx envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} False fc env []) in
                  rewrite sym (appendNilRightNeutral vars) in args

export
tryErrorUnify : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                Core a -> Core (Either Error a)
tryErrorUnify elab
    = do ust <- get UST
         defs <- branch
         catch (do res <- elab
                   commit
                   pure (Right res))
               (\err => do put UST ust
                           put Ctxt defs
                           pure (Left err))

export
tryUnify : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Core a -> Core a -> Core a
tryUnify elab1 elab2
    = do Right ok <- tryErrorUnify elab1
               | Left err => elab2
         pure ok

export
handleUnify : {auto c : Ref Ctxt Defs} -> 
              {auto u : Ref UST UState} ->
              Core a -> (Error -> Core a) -> Core a
handleUnify elab1 elab2
    = do Right ok <- tryErrorUnify elab1
               | Left err => elab2 err
         pure ok

-- Note that the given hole name arises from a type declaration, so needs
-- to be resolved later
export
addDelayedHoleName : {auto u : Ref UST UState} ->
                     (Int, (FC, Name)) -> Core ()
addDelayedHoleName (idx, h)
    = do ust <- get UST
         put UST (record { delayedHoles $= insert idx h } ust)

export
checkDelayedHoles : {auto u : Ref UST UState} ->
                    {auto c : Ref Ctxt Defs} ->
                    Core (Maybe Error)
checkDelayedHoles
    = do ust <- get UST
         let hs = toList (delayedHoles ust)
         if (not (isNil hs)) 
            then do pure (Just (UnsolvedHoles (map snd hs)))
            else pure Nothing

-- A hole is 'valid' - i.e. okay to leave unsolved for later - as long as it's
-- not guarded by a unification problem (in which case, report that the unification
-- problem is unsolved) and it doesn't depend on an implicit pattern variable
-- (in which case, perhaps suggest binding it explicitly)
export
checkValidHole : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 (Int, (FC, Name)) -> Core ()
checkValidHole (idx, (fc, n))
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved idx) (gamma defs)
              | Nothing => pure ()
         case definition gdef of
              Guess tm (con :: _) => 
                  do ust <- get UST
                     let Just c = lookup con (constraints ust)
                          | Nothing => pure ()
                     case c of
                          MkConstraint fc env x y =>
                             throw (CantSolveEq fc env x y)
                          MkSeqConstraint fc env (x :: _) (y :: _) =>
                             throw (CantSolveEq fc env x y)
                          _ => pure ()
              _ => do traverse checkRef (map fst (toList (getRefs (type gdef))))
                      pure ()
  where
    checkRef : Name -> Core ()
    checkRef (PV n f)
        = throw (GenericMsg fc 
                   ("Hole cannot depend on an unbound implicit " ++ show n))
    checkRef _ = pure ()

-- Bool flag says whether it's an error for there to have been holes left
-- in the last session. Usually we can leave them to the end, but it's not
-- valid for there to be holes remaining when checking a LHS.
-- Also throw an error if there are unresolved guarded constants
export
checkUserHoles : {auto u : Ref UST UState} ->
                 {auto c : Ref Ctxt Defs} ->
                 Bool -> Core ()
checkUserHoles now
    = do gs_map <- getGuesses
         let gs = toList gs_map
         log 10 $ "Unsolved guesses " ++ show gs
         traverse checkValidHole gs
         hs_map <- getCurrentHoles
         let hs = toList hs_map
         let hs' = if any isUserName (map (snd . snd) hs) 
                      then [] else hs
         when (now && not (isNil hs')) $ 
              throw (UnsolvedHoles (map snd (nubBy nameEq hs)))
         -- Note the hole names, to ensure they are resolved
         -- by the end of elaborating the current source file
         traverse addDelayedHoleName hs'
         pure ()
  where
    nameEq : (a, b, Name) -> (a, b, Name) -> Bool
    nameEq (_, _, x) (_, _, y) = x == y

export
checkNoGuards : {auto u : Ref UST UState} ->
                {auto c : Ref Ctxt Defs} ->
                Core ()
checkNoGuards = checkUserHoles False

