module Core.UnifyState

import Core.Context
import Core.Core
import Core.Env
import Core.FC
import Core.TT
import Core.TTC
import Utils.Binary

import Data.IntMap

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
  holes : IntMap (FC, Name) -- Metavariables with no definition yet.
                            -- 'Int' is the 'Resolved' name
  guesses : IntMap (FC, Name) -- Names which will be defined when constraints solved
  constraints : IntMap Constraint -- map for finding constraints by ID
  nextName : Int
  nextConstraint : Int
  updateLog : Maybe (List (Int, GlobalDef))
                 -- List of updates made to definitions in this branch of
                 -- elaboration, which we'll need to undo if we backtrack.
                 -- This will be a performance penalty in backtracking so
                 -- we should avoid it as far as we can!

export
initUState : UState
initUState = MkUState empty empty empty 0 0 Nothing

export
data UST : Type where

export
genName : {auto u : Ref UST UState} ->
          String -> Core Name
genName str
    = do ust <- get UST
         put UST (record { nextName $= (+1) } ust)
         pure (MN str (nextName ust))

export
genMVName : {auto u : Ref UST UState} ->
            Name -> Core Name
genMVName (UN str) = genName str
genMVName n
    = do ust <- get UST
         put UST (record { nextName $= (+1) } ust)
         pure (MN (show n) (nextName ust))

addHoleName : {auto u : Ref UST UState} ->
              FC -> Name -> Int -> Core ()
addHoleName fc n i
    = do ust <- get UST
         put UST (record { holes $= insert i (fc, n)  } ust)

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
         put UST (record { holes $= delete n } ust)

export
removeGuess : {auto u : Ref UST UState} ->
              Int -> Core ()
removeGuess n
    = do ust <- get UST
         put UST (record { guesses $= delete n } ust)

export
noteUpdate : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             Int -> Core ()
noteUpdate i
    = do ust <- get UST
         case updateLog ust of
              Nothing => pure ()
              Just ups =>
                 do defs <- get Ctxt
                    Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
                         | Nothing => pure ()
                    put UST (record { updateLog = Just ((i, gdef) :: ups) } 
                                    ust)

export
getHoles : {auto u : Ref UST UState} ->
           Core (IntMap (FC, Name))
getHoles
    = do ust <- get UST
         pure (holes ust)

export
setConstraint : {auto u : Ref UST UState} ->
                Int -> Constraint -> Core ()
setConstraint cid c
    = do ust <- get UST
         put UST (record { constraints $= insert cid c } ust)

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
          if not lets || notLet b
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

export
applyTo : FC -> Term vars -> Env Term vars -> Term vars
applyTo {vars} fc tm env
  = let args = reverse (mkConstantAppArgs {done = []} False fc env []) in
        apply fc (explApp Nothing) tm (rewrite sym (appendNilRightNeutral vars) in args)

-- Create a new metavariable with the given name and return type,
-- and return a term which is the metavariable applied to the environment
-- (and which has the given type)
export
newMeta : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          FC -> RigCount ->
          Env Term vars -> Name -> Term vars -> Core (Term vars)
newMeta {vars} fc rig env n ty
    = do let hty = abstractEnvType fc env ty
         let hole = newDef fc n rig hty Public (Hole False)
         idx <- addDef n hole 
         addHoleName fc n idx
         pure (Meta fc n idx envArgs)
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
newConstant fc rig env tm ty constrs
    = do let def = mkConstant fc env tm
         let defty = abstractEnvType fc env ty
         cn <- genName "p"
         let guess = newDef fc cn rig defty Public (Guess def constrs)
         idx <- addDef cn guess
         addGuessName fc cn idx
         pure (applyTo fc (Ref fc Func (Resolved idx)) env)

export
tryErrorUnify : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                Core a -> Core (Either Error a)
tryErrorUnify elab
    = do ust <- get UST
         next <- getNextEntry
         let btlog = updateLog ust
         put UST (record { updateLog = Just [] } ust)
         catch (do res <- elab
                   pure (Right res))
               (\err => do ust' <- get UST
                           maybe (pure ()) undoLog (updateLog ust')
                           put UST ust
                           setNextEntry next
                           pure (Left err))
  where
    undoLog : List (Int, GlobalDef) -> Core ()
    undoLog [] = pure ()
    undoLog ((i, d) :: rest)
        = do addDef (Resolved i) d
             undoLog rest

export
tryUnify : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Core a -> Core a -> Core a
tryUnify elab1 elab2
    = do Right ok <- tryErrorUnify elab1
               | Left err => elab2
         pure ok


