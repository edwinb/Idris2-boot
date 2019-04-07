module Core.Context

import public Core.Core
import public Core.Name
import Core.Options
import public Core.TT
import Utils.Binary

import Data.IOArray
import Data.NameMap
import Data.StringMap

%default covering

-- Label for array references
data Arr : Type where

export
record Context a where
    constructor MkContext
    nextEntry : Int
    -- Map from full name to its position in the context
    resolvedAs : NameMap Int
    -- Map from strings to all the possible names in all namespaces
    possibles : StringMap (List (Name, Int))
    -- Reference to the actual content, indexed by Int
    content : Ref Arr (IOArray a)    

    -- Namespaces which are visible (i.e. have been imported)
    -- This only matters during evaluation and type checking, to control
    -- access in a program - in all other cases, we'll assume everything is
    -- visible
    visibleNS : List (List String)

export
TTC a => TTC (Context a) where
  toBuf = ?tocontext
  fromBuf = ?fromcontext

initSize : Int
initSize = 10000

Grow : Int
Grow = initSize

export
initCtxtS : Int -> Core (Context a)
initCtxtS s
    = do arr <- coreLift $ newArray s
         aref <- newRef Arr arr
         pure (MkContext 0 empty empty aref [])

export
initCtxt : Core (Context a)
initCtxt = initCtxtS initSize

addPossible : Name -> Int -> 
              StringMap (List (Name, Int)) -> StringMap (List (Name, Int))
addPossible n i ps
    = case userNameRoot n of
           Nothing => ps
           Just nr =>
              case lookup nr ps of
                   Nothing => insert nr [(n, i)] ps
                   Just nis => insert nr ((n, i) :: nis) ps

-- Get the position of the next entry in the context array, growing the
-- array if it's out of bounds.
-- Updates the context with the mapping from name to index
getPosition : Name -> Context a -> Core (Int, Context a)
getPosition (Resolved idx) ctxt = pure (idx, ctxt)
getPosition n ctxt
    = case lookup n (resolvedAs ctxt) of
           Just idx => 
              do log 10 $ "Found " ++ show n ++ " " ++ show idx
                 pure (idx, ctxt)
           Nothing => 
              do let idx = nextEntry ctxt + 1
                 let a = content ctxt
                 arr <- get Arr
                 when (idx >= max arr) $
                         do arr' <- coreLift $ newArrayCopy (max arr + Grow) arr
                            put Arr arr'
                 log 10 $ "Added " ++ show n ++ " " ++ show idx
                 pure (idx, record { nextEntry = idx,
                                     resolvedAs $= insert n idx,
                                     possibles $= addPossible n idx
                                   } ctxt)

-- Add the name to the context, or update the existing entry if it's already
-- there.
export
addCtxt : Name -> a -> Context a -> Core (Int, Context a)
addCtxt n val ctxt_in
    = do (idx, ctxt) <- getPosition n ctxt_in
         let a = content ctxt
         arr <- get Arr
         coreLift $ writeArray arr idx val
         pure (idx, ctxt)

export
lookupCtxtExactI : Name -> Context a -> Core (Maybe (Int, a))
lookupCtxtExactI (Resolved idx) ctxt
    = do let a = content ctxt
         arr <- get Arr
         Just def <- coreLift (readArray arr idx)
              | Nothing => pure Nothing
         pure (Just (idx, def))
lookupCtxtExactI n ctxt
    = do let Just idx = lookup n (resolvedAs ctxt)
                  | Nothing => pure Nothing
         let a = content ctxt
         arr <- get Arr
         Just def <- coreLift (readArray arr idx)
              | Nothing => pure Nothing
         pure (Just (idx, def))

export
lookupCtxtExact : Name -> Context a -> Core (Maybe a)
lookupCtxtExact (Resolved idx) ctxt
    = do let a = content ctxt
         arr <- get Arr
         coreLift (readArray arr idx)
lookupCtxtExact n ctxt
    = do Just (i, def) <- lookupCtxtExactI n ctxt
              | Nothing => pure Nothing
         pure (Just def)

export
lookupCtxtName : Name -> Context a -> Core (List (Name, Int, a))
lookupCtxtName n ctxt
    = case userNameRoot n of
           Nothing => do Just (i, res) <- lookupCtxtExactI n ctxt
                              | Nothing => pure []
                         pure [(n, i, res)]
           Just r =>
              do let Just ps = lookup r (possibles ctxt)
                      | Nothing => pure []
                 ps' <- the (Core (List (Maybe (Name, Int, a)))) $
                           traverse (\ (n, i) => 
                                    do Just res <- lookupCtxtExact (Resolved i) ctxt
                                            | pure Nothing
                                       pure (Just (n, i, res))) ps
                 getMatches ps'
  where
    matches : Name -> (Name, Int, a) -> Bool
    matches (NS ns _) (NS cns _, _, _) = ns `isPrefixOf` cns
    matches (NS _ _) _ = True -- no in library name, so root doesn't match
    matches _ _ = True -- no prefix, so root must match, so good
    
    getMatches : List (Maybe (Name, Int, a)) -> Core (List (Name, Int, a))
    getMatches [] = pure []
    getMatches (Nothing :: rs) = getMatches rs
    getMatches (Just r :: rs)
        = if matches n r
             then do rs' <- getMatches rs
                     pure (r :: rs')
             else getMatches rs

public export
data Def : Type where
    None : Def -- Not yet defined
    Fn : ClosedTerm -> Def -- Ordinary function definition
    DCon : (tag : Int) -> (arity : Nat) -> Def -- data constructor
    TCon : (tag : Int) -> (arity : Nat) ->
           (parampos : List Nat) -> -- parameters
           (detpos : List Nat) -> -- determining arguments
           (datacons : List Name) ->
           Def
    Hole : (invertible : Bool) -> Def
    -- Constraints are integer references into the current map of
    -- constraints in the UnifyState (see Core.UnifyState)
    Guess : (guess : ClosedTerm) -> (constraints : List Int) -> Def

export
Show Def where
  show None = "undefined"
  show (Fn tm) = show tm
  show (DCon t a) = "DataCon " ++ show t ++ " " ++ show a
  show (TCon t a ps ds cons) 
      = "TyCon " ++ show t ++ " " ++ show a ++ " " ++ show cons
  show (Hole inv) = "Hole"
  show (Guess tm cs) = "Guess " ++ show tm ++ " when " ++ show cs

public export
record Constructor where
  constructor MkCon
  loc : FC
  name : Name
  arity : Nat
  type : ClosedTerm

public export
data DataDef : Type where
     MkData : (tycon : Constructor) -> (datacons : List Constructor) ->
              DataDef

public export
record GlobalDef where
  constructor MkGlobalDef
  location : FC
  type : ClosedTerm
  multiplicity : RigCount
  visibility : Visibility
  definition : Def

export
newDef : FC -> RigCount -> ClosedTerm -> Visibility -> Def -> GlobalDef
newDef fc rig ty vis def = MkGlobalDef fc ty rig vis def

public export
record Defs where
  constructor MkDefs
  gamma : Context GlobalDef
  currentNS : List String -- namespace for current definitions
  options : Options
--   toSave : SortedSet
  nextTag : Int
  ifaceHash : Int

export
clearDefs : Defs -> Core Defs
clearDefs defs
    = do gam <- initCtxtS 1
         pure (record { gamma = gam } defs)

export
initDefs : Core Defs
initDefs 
    = do gam <- initCtxt
         pure (MkDefs gam ["Main"] defaults 100 5381)
      
export
TTC Defs where
  toBuf = ?todefs
  fromBuf = ?fromdefs

-- Label for context references
export
data Ctxt : Type where

export
addDef : {auto c : Ref Ctxt Defs} -> 
         Name -> GlobalDef -> Core Int
addDef n def
    = do defs <- get Ctxt
         (idx, gam') <- addCtxt n def (gamma defs)
         put Ctxt (record { gamma = gam' } defs)
         pure idx

getNextTypeTag : {auto c : Ref Ctxt Defs} ->
                 Core Int
getNextTypeTag
    = do defs <- get Ctxt
         put Ctxt (record { nextTag $= (+1) } defs)
         pure (nextTag defs)

paramPos : Name -> (dcons : List ClosedTerm) -> List Nat
paramPos _ _ = [] -- TODO

export
addData : {auto c : Ref Ctxt Defs} ->
					Visibility -> DataDef -> Core Int
addData vis (MkData (MkCon dfc tyn arity tycon) datacons)
    = do defs <- get Ctxt 
         tag <- getNextTypeTag 
         let tydef = newDef dfc RigW tycon vis 
                            (TCon tag arity 
                                  (paramPos tyn (map type datacons))
                                  (allDet arity)
                                  (map name datacons))
         (idx, gam') <- addCtxt tyn tydef (gamma defs)
         gam'' <- addDataConstructors 0 datacons gam'
         put Ctxt (record { gamma = gam'' } defs)
         pure idx
  where
    allDet : Nat -> List Nat
    allDet Z = []
    allDet (S k) = [0..k]

    conVisibility : Visibility -> Visibility
    conVisibility Export = Private
    conVisibility x = x

    addDataConstructors : (tag : Int) -> List Constructor -> 
                          Context GlobalDef -> Core (Context GlobalDef)
    addDataConstructors tag [] gam = pure gam
    addDataConstructors tag (MkCon fc n a ty :: cs) gam
        = do let condef = newDef fc RigW ty (conVisibility vis) (DCon tag a)
             (idx, gam') <- addCtxt n condef gam
             addDataConstructors (tag + 1) cs gam'

-- Get the name as it would be defined in the current namespace
-- i.e. if it doesn't have an explicit namespace already, add it,
-- otherwise leave it alone
export
inCurrentNS : {auto c : Ref Ctxt Defs} ->
              Name -> Core Name
inCurrentNS (UN n)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) (UN n))
inCurrentNS n@(MN _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n = pure n

export
lookupTypeExact : Name -> Context GlobalDef -> Core (Maybe ClosedTerm)
lookupTypeExact n ctxt
    = do Just gdef <- lookupCtxtExact n ctxt
              | Nothing => pure Nothing
         pure (Just (type gdef))

