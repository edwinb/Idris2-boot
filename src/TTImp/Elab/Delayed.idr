module TTImp.Elab.Delayed

import Core.CaseTree
import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.TTImp

import Data.IntMap

%default covering

-- We run the elaborator in the given environment, but need to end up with a
-- closed term. 
mkClosedElab : FC -> Env Term vars -> 
               (Core (Term vars, Glued vars)) ->
               Core ClosedTerm
mkClosedElab fc [] elab 
    = do (tm, _) <- elab
         pure tm
mkClosedElab {vars = x :: vars} fc (b :: env) elab
    = mkClosedElab fc env 
          (do (sc', _) <- elab
              let b' = newBinder b
              pure (Bind fc x b' sc', gErased fc))
  where
    -- in 'abstractEnvType' we get a Pi binder (so we'll need a Lambda) for
    -- everything except 'Let', so make the appropriate corresponding binder
    -- here
    newBinder : Binder (Term vars) -> Binder (Term vars)
    newBinder (Let c val ty) = Let c val ty
    newBinder b = Lam (multiplicity b) Explicit (binderType b)

-- Try the given elaborator; if it fails, and the error matches the
-- predicate, make a hole and try it again later when more holes might
-- have been resolved
export
delayOnFailure : {auto c : Ref Ctxt Defs} -> 
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} -> 
                 FC -> RigCount -> Env Term vars ->
                 (expected : Glued vars) ->
                 (Error -> Bool) ->
                 (Bool -> Core (Term vars, Glued vars)) ->
                 Core (Term vars, Glued vars)
delayOnFailure fc rig env expected pred elab 
    = handle (elab False)
        (\err => 
            do est <- get EST
               if pred err && allowDelay est
                  then 
                    do nm <- genName "delayed"
                       (ci, dtm) <- newDelayed fc Rig1 env nm !(getTerm expected)
                       logGlueNF 5 ("Postponing elaborator " ++ show nm ++ 
                                    " for") env expected
                       log 10 ("Due to error " ++ show err)
                       ust <- get UST
                       put UST (record { delayedElab $= 
                               ((ci, mkClosedElab fc env 
                                         (do est <- get EST
                                             put EST (record { allowDelay = False } est)
                                             tm <- elab True
                                             put EST (record { allowDelay = True } est)
                                             pure tm)) :: ) } 
                                       ust)
                       pure (dtm, expected)
                  else throw err)

export
retryDelayed : {auto c : Ref Ctxt Defs} -> 
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} -> 
               List (Int, Core ClosedTerm) ->
               Core ()
retryDelayed [] = pure ()
retryDelayed ((i, elab) :: ds)
    = do tm <- elab
         updateDef (Resolved i) (const (Just 
              (PMDef [] (STerm tm) (STerm tm) [])))
         logTerm 5 ("Resolved delayed hole " ++ show i) tm
         removeHole i
         retryDelayed ds

