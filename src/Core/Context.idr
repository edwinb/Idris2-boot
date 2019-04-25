module Core.Context

import Core.CaseTree
import public Core.Core
import Core.Env
import public Core.Name
import Core.Options
import public Core.TT
import Core.TTC
import Core.Value

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
    firstEntry : Int -- First entry in the current source file
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

-- Make an array which is a mapping from IDs to the names they represent
-- (the reverse of 'resolvedAs') which we use when serialising to record which
-- name each ID refers to. Then when we read references in terms, we'll know
-- which name it really is and can update appropriately for the new context.
export
getNameRefs : Context a -> Core NameRefs
getNameRefs gam
    = do arr <- coreLift $ newArray (nextEntry gam)
         traverse (addToMap arr) (toList (resolvedAs gam))
         pure arr
  where
    addToMap : NameRefs -> (Name, Int) -> Core ()
    addToMap arr (n, i)
        = coreLift $ writeArray arr i (n, Nothing)


initSize : Int
initSize = 10000

Grow : Int
Grow = initSize

export
initCtxtS : Int -> Core (Context a)
initCtxtS s
    = do arr <- coreLift $ newArray s
         aref <- newRef Arr arr
         pure (MkContext 0 0 empty empty aref [])

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
export
getPosition : Name -> Context a -> Core (Int, Context a)
getPosition (Resolved idx) ctxt = pure (idx, ctxt)
getPosition n ctxt
    = case lookup n (resolvedAs ctxt) of
           Just idx => 
              do log 10 $ "Found " ++ show n ++ " " ++ show idx
                 pure (idx, ctxt)
           Nothing => 
              do let idx = nextEntry ctxt
                 let a = content ctxt
                 arr <- get Arr
                 when (idx >= max arr) $
                         do arr' <- coreLift $ newArrayCopy (max arr + Grow) arr
                            put Arr arr'
                 log 10 $ "Added " ++ show n ++ " " ++ show idx
                 pure (idx, record { nextEntry = idx + 1,
                                     resolvedAs $= insert n idx,
                                     possibles $= addPossible n idx
                                   } ctxt)

export
getNameID : Name -> Context a -> Maybe Int
getNameID n ctxt = lookup n (resolvedAs ctxt)

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
    PMDef : (args : List Name) ->
            (treeCT : CaseTree args) ->
            (treeRT : CaseTree args) ->
            (pats : List (vs ** (Env Term vs, Term vs, Term vs))) ->
                -- original checked patterns (LHS/RHS) with the names in
                -- the environment. Used for display purposes, and for helping
                -- find size changes in termination checking
            Def -- Ordinary function definition
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
    ImpBind : Def -- global name temporarily standing for an implicitly bound name

export
Show Def where
  show None = "undefined"
  show (PMDef args ct rt pats) 
      = show args ++ "; " ++ show ct
  show (DCon t a) = "DataCon " ++ show t ++ " " ++ show a
  show (TCon t a ps ds cons) 
      = "TyCon " ++ show t ++ " " ++ show a ++ " " ++ show cons
  show (Hole inv) = "Hole"
  show (Guess tm cs) = "Guess " ++ show tm ++ " when " ++ show cs
  show ImpBind = "Implicitly bound"

export
TTC Def where
  toBuf b None = tag 0
  toBuf b (PMDef args ct rt pats) 
      = do tag 1; toBuf b args; toBuf b ct; toBuf b rt; toBuf b pats
  toBuf b (DCon t arity) = do tag 2; toBuf b t; toBuf b arity
  toBuf b (TCon t arity parampos detpos datacons) 
      = do tag 3; toBuf b t; toBuf b arity; toBuf b parampos
           toBuf b detpos; toBuf b datacons
  toBuf b (Hole invertible) = do tag 4; toBuf b invertible
  toBuf b (Guess guess constraints) = do tag 5; toBuf b guess; toBuf b constraints
  toBuf b ImpBind = tag 6

  fromBuf r b 
      = case !getTag of
             0 => pure None
             1 => do args <- fromBuf r b 
                     ct <- fromBuf r b
                     rt <- fromBuf r b
                     pats <- fromBuf r b
                     pure (PMDef args ct rt pats)
             2 => do t <- fromBuf r b; a <- fromBuf r b
                     pure (DCon t a)
             3 => do t <- fromBuf r b; a <- fromBuf r b
                     ps <- fromBuf r b; dets <- fromBuf r b; cs <- fromBuf r b
                     pure (TCon t a ps dets cs)
             4 => do i <- fromBuf r b;
                     pure (Hole i)
             5 => do g <- fromBuf r b; cs <- fromBuf r b
                     pure (Guess g cs)
             6 => pure ImpBind
             _ => corrupt "Def"

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
data Clause : Type where
     MkClause : (env : Env Term vars) ->
                (lhs : Term vars) -> (rhs : Term vars) -> Clause

public export
data TotalReq = Total | CoveringOnly | PartialOK

public export
data DefFlag 
    = TypeHint Name Bool -- True == direct hint
    | GlobalHint Bool -- True == always search (not a default hint)
    | Inline
    | Invertible -- assume safe to cancel arguments in unification
    | Overloadable -- allow ad-hoc overloads
    | TCInline -- always inline before totality checking
         -- (in practice, this means it's reduced in 'normaliseHoles')
         -- This means the function gets inlined when calculating the size
         -- change graph, but otherwise not. It's only safe if the function
         -- being inlined is terminating no matter what, and is really a bit
         -- of a hack to make sure interface dictionaries are properly inlined
         -- (otherwise they look potentially non terminating) so use with
         -- care!
    | SetTotal TotalReq

export
Eq TotalReq where
    (==) Total Total = True
    (==) CoveringOnly CoveringOnly = True
    (==) PartialOK PartialOK = True
    (==) _ _ = False

export
Eq DefFlag where
    (==) (TypeHint ty x) (TypeHint ty' y) = ty == ty' && x == y
    (==) (GlobalHint x) (GlobalHint y) = x == y
    (==) Inline Inline = True
    (==) Invertible Invertible = True
    (==) Overloadable Overloadable = True
    (==) TCInline TCInline = True
    (==) (SetTotal x) (SetTotal y) = x == y
    (==) _ _ = False

TTC TotalReq where
  toBuf b Total = tag 0
  toBuf b CoveringOnly = tag 1
  toBuf b PartialOK = tag 2

  fromBuf s b
      = case !getTag of
             0 => pure Total
             1 => pure CoveringOnly
             2 => pure PartialOK
             _ => corrupt "TotalReq"

TTC DefFlag where
  toBuf b (TypeHint x y) = do tag 0; toBuf b x; toBuf b y
  toBuf b (GlobalHint t) = do tag 1; toBuf b t
  toBuf b Inline = tag 2
  toBuf b Invertible = tag 3
  toBuf b Overloadable = tag 4
  toBuf b TCInline = tag 5
  toBuf b (SetTotal x) = do tag 6; toBuf b x

  fromBuf s b
      = case !getTag of
             0 => do x <- fromBuf s b; y <- fromBuf s b; pure (TypeHint x y)
             1 => do t <- fromBuf s b; pure (GlobalHint t)
             2 => pure Inline
             3 => pure Invertible
             4 => pure Overloadable
             5 => pure TCInline
             6 => do x <- fromBuf s b; pure (SetTotal x)
             _ => corrupt "DefFlag"

public export
record GlobalDef where
  constructor MkGlobalDef
  location : FC
  fullname : Name -- original unresolved name
  type : ClosedTerm
  multiplicity : RigCount
  visibility : Visibility
  flags : List DefFlag
  definition : Def

export
TTC GlobalDef where
  toBuf b gdef 
      -- Only write full details for user specified names. The others will
      -- be holes where all we will ever need after loading is the definition
      = do toBuf b (fullname gdef)
           toBuf b (definition gdef)
           when (isUserName (fullname gdef)) $
              do toBuf b (location gdef)
                 toBuf b (type gdef)
                 toBuf b (multiplicity gdef)
                 toBuf b (visibility gdef)
                 toBuf b (flags gdef)

  fromBuf r b 
      = do name <- fromBuf r b
           def <- fromBuf r b
           if isUserName name
              then do loc <- fromBuf r b; 
                      ty <- fromBuf r b; mul <- fromBuf r b
                      vis <- fromBuf r b; fl <- fromBuf r b
                      pure (MkGlobalDef loc name ty mul vis fl def)
              else do let fc = emptyFC
                      pure (MkGlobalDef fc name (Erased fc)
                                        RigW Public [] def)

export
newDef : FC -> Name -> RigCount -> ClosedTerm -> Visibility -> Def -> GlobalDef
newDef fc n rig ty vis def = MkGlobalDef fc n ty rig vis [] def

public export
record Defs where
  constructor MkDefs
  gamma : Context GlobalDef
  currentNS : List String -- namespace for current definitions
  options : Options
  toSave : NameMap ()
  nextTag : Int
  ifaceHash : Int
  -- interface hashes of imported modules
  importHashes : List (List String, Int)
  -- imported modules, whether to rexport, as namespace
  imported : List (List String, Bool, List String)
  -- all imported filenames/namespaces, just to avoid loading something
  -- twice unnecessarily (this is a record of all the things we've
  -- called 'readFromTTC' with, in practice)
  allImported : List (String, List String)

export
clearDefs : Defs -> Core Defs
clearDefs defs
    = do gam <- initCtxtS 1
         pure (record { gamma = gam } defs)

export
initDefs : Core Defs
initDefs 
    = do gam <- initCtxt
         pure (MkDefs gam ["Main"] defaults empty 100 5381 [] [] [])
      
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

export
updateDef : {auto c : Ref Ctxt Defs} -> 
            Name -> (Def -> Maybe Def) -> Core ()
updateDef n fdef
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
             | Nothing => pure ()
         case fdef (definition gdef) of
              Nothing => pure ()
              Just def' => do addDef n (record { definition = def' } gdef)
                              pure ()

export
setCtxt : {auto c : Ref Ctxt Defs} -> Context GlobalDef -> Core ()
setCtxt gam
    = do defs <- get Ctxt
         put Ctxt (record { gamma = gam } defs)

-- Get the names to save. These are the ones explicitly noted, and the
-- ones between firstEntry and nextEntry (which are the names introduced in
-- the current source file)
export
getSave : {auto c : Ref Ctxt Defs} -> Core (List Name)
getSave 
    = do defs <- get Ctxt
         let gam = gamma defs
         let ns = toSave defs
         let a = content gam
         arr <- get Arr
         ns' <- coreLift $ addAll (firstEntry gam) (nextEntry gam) ns arr
         pure (map fst (toList ns'))
  where
    addAll : Int -> Int -> NameMap () -> IOArray GlobalDef -> IO (NameMap ())
    addAll first last ns arr
        = if first == last 
             then pure ns
             else do Just d <- readArray arr first
                         | Nothing => addAll (first + 1) last ns arr
                     case fullname d of
                          PV _ _ => addAll (first + 1) last ns arr
                          _ => addAll (first + 1) last 
                                      (insert (Resolved first) () ns) arr

-- Explicitly note that the name should be saved when writing out a .ttc
export
addToSave : {auto c : Ref Ctxt Defs} ->
            Name -> Core ()
addToSave n
    = do defs <- get Ctxt
         put Ctxt (record { toSave $= insert n () } defs)

-- Specific lookup functions
export
lookupDefExact : Name -> Context GlobalDef -> Core (Maybe Def)
lookupDefExact n gam
    = do Just gdef <- lookupCtxtExact n gam
              | Nothing => pure Nothing
         pure (Just (definition gdef))

export
lookupTyExact : Name -> Context GlobalDef -> Core (Maybe ClosedTerm)
lookupTyExact n gam
    = do Just gdef <- lookupCtxtExact n gam
              | Nothing => pure Nothing
         pure (Just (type gdef))

-- Set the default namespace for new definitions
export
setNS : {auto c : Ref Ctxt Defs} ->
        List String -> Core ()
setNS ns
    = do defs <- get Ctxt
         put Ctxt (record { currentNS = ns } defs)

-- Get the default namespace for new definitions
export
getNS : {auto c : Ref Ctxt Defs} ->
        Core (List String)
getNS
    = do defs <- get Ctxt
         pure (currentNS defs)

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
         let tydef = newDef dfc tyn RigW tycon vis 
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
        = do let condef = newDef fc n RigW ty (conVisibility vis) (DCon tag a)
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

-- Get the next entry id in the context (this is for recording where to go
-- back to when backtracking in the elaborator)
export
getNextEntry : {auto c : Ref Ctxt Defs} ->
               Core Int
getNextEntry
    = do defs <- get Ctxt
         pure (nextEntry (gamma defs))

export
setNextEntry : {auto c : Ref Ctxt Defs} ->
               Int -> Core ()
setNextEntry i
    = do defs <- get Ctxt
         put Ctxt (record { gamma->nextEntry = i } defs)

-- Set the 'first entry' index (i.e. the first entry in the current file)
-- to the place we currently are in the context
export
resetFirstEntry : {auto c : Ref Ctxt Defs} ->
                  Core ()
resetFirstEntry
    = do defs <- get Ctxt
         put Ctxt (record { gamma->firstEntry = nextEntry (gamma defs) } defs)

export
toFullNames : {auto c : Ref Ctxt Defs} ->
              Term vars -> Core (Term vars)
toFullNames tm
    = do defs <- get Ctxt
         full (gamma defs) tm
  where
    full : Context GlobalDef -> Term vars -> Core (Term vars)
    full gam (Ref fc x (Resolved i)) 
        = do let a = content gam
             arr <- get Arr
             Just gdef <- coreLift (readArray arr i)
                  | Nothing => pure (Ref fc x (Resolved i))
             pure (Ref fc x (fullname gdef))
    full gam (Meta fc x y xs) 
        = pure (Meta fc x y !(traverse (full gam) xs))
    full gam (Bind fc x b scope) 
        = pure (Bind fc x !(traverse (full gam) b) !(full gam scope))
    full gam (App fc fn p arg) 
        = pure (App fc !(full gam fn) p !(full gam arg))
    full gam (TDelayed fc x y) 
        = pure (TDelayed fc x !(full gam y))
    full gam (TDelay fc x y)
        = pure (TDelay fc x !(full gam y))
    full gam (TForce fc x)
        = pure (TForce fc !(full gam x))
    full gam tm = pure tm

-- Getting and setting various options

export
getPPrint : {auto c : Ref Ctxt Defs} ->
            Core PPrinter
getPPrint
    = do defs <- get Ctxt
         pure (printing (options defs))

export
getDirs : {auto c : Ref Ctxt Defs} -> Core Dirs
getDirs
    = do defs <- get Ctxt
         pure (dirs (options defs))

export
addExtraDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
addExtraDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->extra_dirs $= (++ [dir]) } defs)

export
addDataDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
addDataDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->data_dirs $= (++ [dir]) } defs)

export
setBuildDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
setBuildDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->build_dir = dir } defs)

export
setWorkingDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
setWorkingDir dir
    = do defs <- get Ctxt
         coreLift $ changeDir dir
         cdir <- coreLift $ currentDir
         put Ctxt (record { options->dirs->working_dir = cdir } defs)

export
setPrefix : {auto c : Ref Ctxt Defs} -> String -> Core ()
setPrefix dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->dir_prefix = dir } defs)

-- Log message with a term, translating back to human readable names first
export
logTerm : {auto c : Ref Ctxt Defs} ->
          Nat -> Lazy String -> Term vars -> Core ()
logTerm lvl msg tm
    = do opts <- getOpts
         if logLevel opts >= lvl
            then do tm' <- toFullNames tm
                    coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg 
                                          ++ ": " ++ show tm'
            else pure ()

