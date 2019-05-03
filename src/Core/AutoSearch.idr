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
             (defining : Name) -> (topTy : Term vars) ->
             Env Term vars -> SearchEnv vars -> 
             (target : NF vars) -> Core (NF vars)

export
search : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         FC -> RigCount ->
         (defaults : Bool) -> (depth : Nat) ->
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
                              !(sc defs (toClosure defaultOpts env arg))
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
               (defaults : Bool) -> (depth : Nat) ->
               (defining : Name) -> (topTy : Term vars) -> Env Term vars -> 
               SearchEnv vars ->
               (arg : ArgInfo vars) -> 
               Core () 
searchIfHole fc defaults Z def top env locs arg 
    = throw (CantSolveGoal fc env top) -- possibly should say depth limit hit?
searchIfHole fc defaults (S depth) def top env locs arg 
    = do let hole = holeID arg
         let rig = argRig arg

         defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved hole) (gamma defs)
              | Nothing => throw (CantSolveGoal fc env top)
         let Hole inv = definition gdef
              | _ => pure () -- already solved
         argdef <- searchType fc rig defaults depth def top env locs (argType arg)
         vs <- unify InTerm fc env !(nf defs env (metaApp arg)) argdef
         let [] = constraints vs
              | _ => throw (CantSolveGoal fc env top)
         pure ()


searchLocal : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount ->
              (defaults : Bool) -> (depth : Nat) ->
              (defining : Name) -> (topTy : Term vars) ->
              Env Term vars -> SearchEnv vars -> SearchEnv vars -> 
              (target : NF vars) -> Core (NF vars)
searchLocal fc rigc defaults depth def top env locs [] target
    = throw (CantSolveGoal fc env top)
searchLocal fc rigc defaults depth def top env locs ((ty, c) :: rest) target
    = tryUnify 
         (do (args, appTy) <- mkArgs fc rigc env ty
             -- TODO: Can only use the local if it's not an unsolved hole
             ures <- unify InTerm fc env target appTy
             let [] = constraints ures
                 | _ => throw (CantSolveGoal fc env top)
             candidate <- closureApply fc c args
             traverse (searchIfHole fc defaults depth def top env locs) args
             defs <- get Ctxt
             nf defs env candidate)
         (searchLocal fc rigc defaults depth def top env locs rest target)

searchNames : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount ->
              (defaults : Bool) -> (depth : Nat) ->
              (defining : Name) -> (topTy : Term vars) ->
              Env Term vars -> List Name -> 
              (target : NF vars) -> Core (NF vars)

-- Declared at the top
searchType fc rigc defaults depth def top env locs (NBind nfc x (Pi c p ty) sc)
    = pure (NBind nfc x (Lam c p ty)
             (\defs, arg => searchType fc rigc defaults depth def top env 
                                   ((ty, arg) :: locs) !(sc defs arg)))
searchType {vars} fc rigc defaults depth def top env locs target@(NTCon tfc tyn t a args)
    = if a == length args
         then do sd <- getSearchData fc defaults tyn
                 -- TODO: Check determining arguments are okay for 'args' 
                 tryGroups (hintGroups sd)
         else throw (CantSolveGoal fc env top)
  where
    ambig : Error -> Bool
    ambig (AmbiguousSearch _ _ _) = True
    ambig _ = False
    
    tryGroups : List (List Name) -> Core (NF vars)
    tryGroups [] = throw (CantSolveGoal fc env top)
    tryGroups (g :: gs)
        = handleUnify
             (searchNames fc rigc defaults depth def top env g target)
             (\err => if ambig err || isNil gs
                         then throw err
                         else tryGroups gs)
searchType fc rigc defaults depth def top env locs target
    = searchLocal fc rigc defaults depth def top env locs locs target

-- Declared at the top
search fc rigc defaults depth def top env
    = do defs <- get Ctxt
         tm <- searchType fc rigc defaults depth def top env []
                          !(nf defs env top)
         empty <- clearDefs defs
         quote empty env tm

