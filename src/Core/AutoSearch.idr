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
             (defining : Name) -> (topTy : Term vars) ->
             Env Term vars -> SearchEnv vars -> 
             (target : NF vars) -> Core (NF vars)

export
search : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         FC -> RigCount ->
         (defining : Name) -> (topTy : Term vars) -> Env Term vars -> 
         Core (Term vars)

record ArgInfo (vars : List Name) where
  constructor MkArgInfo
  holeID : Int
  argRig : RigCount
  appInf : AppInfo
  metaApp : Term vars
  argType : NF vars

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
         -- setInvertible fc argName
         (rest, restTy) <- mkArgs fc rigc env 
                              !(sc (toClosure defaultOpts env arg))
         pure (MkArgInfo idx argRig (appInf Nothing p) arg ty :: rest, restTy)
mkArgs fc rigc env ty = pure ([], ty)

closureApply : FC -> Closure vars -> List (ArgInfo vars) -> 
               Core (Term vars)
closureApply fc (MkClosure _ [] _ tm) args 
    = pure (applyInfo fc tm (map (\i => (appInf i, metaApp i)) args))
closureApply _ _ _ = throw (InternalError "Wrong argument form in AutoSearch")

searchIfHole : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               FC -> 
               (defining : Name) -> (topTy : Term vars) -> Env Term vars -> 
               SearchEnv vars ->
               (arg : ArgInfo vars) -> 
               Core () 
searchIfHole fc def top env locs arg 
    = do let hole = holeID arg
         let rig = argRig arg

         defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved hole) (gamma defs)
              | Nothing => throw (CantSolveGoal fc env top)
         let Hole inv = definition gdef
              | _ => pure () -- already solved
         argdef <- searchType fc rig def top env locs (argType arg)
         vs <- unify InTerm fc env !(nf defs env (metaApp arg)) argdef
         let [] = constraints vs
              | _ => throw (CantSolveGoal fc env top)
         pure ()

searchLocal : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount ->
              (defining : Name) -> (topTy : Term vars) ->
              Env Term vars -> SearchEnv vars -> SearchEnv vars -> 
              (target : NF vars) -> Core (NF vars)
searchLocal fc rigc def top env locs [] target
    = throw (CantSolveGoal fc env top)
searchLocal fc rigc def top env locs ((ty, c) :: rest) target
    = tryUnify 
         (do (args, appTy) <- mkArgs fc rigc env ty
             -- TODO: Can only use the local if it's not an unsolved hole
             ures <- unify InTerm fc env target appTy
             let [] = constraints ures
                 | _ => throw (CantSolveGoal fc env top)
             candidate <- closureApply fc c args
             traverse (searchIfHole fc def top env locs) args
             defs <- get Ctxt
             nf defs env candidate)
         (searchLocal fc rigc def top env locs rest target)

searchType fc rigc def top env locs (NBind nfc x (Pi c p ty) sc)
    = pure (NBind nfc x (Lam c p ty)
             (\arg => searchType fc rigc def top env ((ty, arg) :: locs) !(sc arg)))
searchType fc rigc def top env locs target
    = searchLocal fc rigc def top env locs locs target

-- Declared at the top
search fc rigc def top env
    = do defs <- get Ctxt
         tm <- searchType fc rigc def top env []
                          !(nf defs env top)
         empty <- clearDefs defs
         quote empty env tm

