module Core.Context

import        Core.CaseTree
import public Core.Core
import        Core.Env
import        Core.Hash
import public Core.Name
import        Core.Options
import public Core.TT
import        Core.TTC

import Utils.Binary

import Data.IOArray
import Data.NameMap
import Data.StringMap
import Data.IntMap

import System

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
    -- Branching depth, in a backtracking elaborator. 0 is top level; at lower
    -- levels we need to stage updates rather than add directly to the
    -- 'content' store
    branchDepth : Nat
    -- Things which we're going to add, if this branch succeeds
    staging : IntMap a

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
         traverse_ (addToMap arr) (toList (resolvedAs gam))
         pure arr
  where
    addToMap : NameRefs -> (Name, Int) -> Core ()
--     addToMap arr (PV _ _, i)
--         = coreLift $ putStrLn ("Skipping " ++ show i) -- pure () -- These won't appear in terms
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
         pure (MkContext 0 0 empty empty aref 0 empty [])

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
              do pure (idx, ctxt)
           Nothing => 
              do let idx = nextEntry ctxt
                 let a = content ctxt
                 arr <- get Arr
                 when (idx >= max arr) $
                         do arr' <- coreLift $ newArrayCopy (max arr + Grow) arr
                            put Arr arr'
                 pure (idx, record { nextEntry = idx + 1,
                                     resolvedAs $= insert n idx,
                                     possibles $= addPossible n idx
                                   } ctxt)

export
getNameID : Name -> Context a -> Maybe Int
getNameID (Resolved idx) ctxt = Just idx
getNameID n ctxt = lookup n (resolvedAs ctxt)

-- Add the name to the context, or update the existing entry if it's already
-- there.
-- If we're not at the top level, add it to the staging area
export
addCtxt : Name -> a -> Context a -> Core (Int, Context a)
addCtxt n val ctxt_in
    = if branchDepth ctxt_in == 0
         then do (idx, ctxt) <- getPosition n ctxt_in
                 let a = content ctxt
                 arr <- get Arr
                 coreLift $ writeArray arr idx val
                 pure (idx, ctxt)
         else do (idx, ctxt) <- getPosition n ctxt_in
                 pure (idx, record { staging $= insert idx val } ctxt)

export
lookupCtxtExactI : Name -> Context a -> Core (Maybe (Int, a))
lookupCtxtExactI (Resolved idx) ctxt
    = case lookup idx (staging ctxt) of
           Just val => pure (Just (idx, val))
           Nothing =>
              do let a = content ctxt
                 arr <- get Arr
                 Just def <- coreLift (readArray arr idx)
                      | Nothing => pure Nothing
                 pure (Just (idx, def))
lookupCtxtExactI n ctxt
    = do let Just idx = lookup n (resolvedAs ctxt)
                  | Nothing => pure Nothing
         lookupCtxtExactI (Resolved idx) ctxt

export
lookupCtxtExact : Name -> Context a -> Core (Maybe a)
lookupCtxtExact (Resolved idx) ctxt
    = case lookup idx (staging ctxt) of
           Just res => pure (Just res)
           Nothing =>
              do let a = content ctxt
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

branchCtxt : Context a -> Core (Context a)
branchCtxt ctxt = pure (record { branchDepth $= S } ctxt)

commitCtxt : Context a -> Core (Context a) 
commitCtxt ctxt
    = case branchDepth ctxt of
           Z => pure ctxt
           S Z => -- add all the things from 'staging' to the real array
                  do let a = content ctxt
                     arr <- get Arr
                     coreLift $ commitStaged (toList (staging ctxt)) arr
                     pure (record { staging = empty,
                                 branchDepth = Z } ctxt)
           S k => pure (record { branchDepth = k } ctxt)
  where
    -- We know the array must be big enough, because it will have been resized
    -- if necessary in the branch to fit the index we've been given here
    commitStaged : List (Int, a) -> IOArray a -> IO ()
    commitStaged [] arr = pure ()
    commitStaged ((idx, val) :: rest) arr
        = do writeArray arr idx val
             commitStaged rest arr

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
    ExternDef : (arity : Nat) -> Def
    Builtin : {arity : Nat} -> PrimFn arity -> Def
    DCon : (tag : Int) -> (arity : Nat) -> Def -- data constructor
    TCon : (tag : Int) -> (arity : Nat) ->
           (parampos : List Nat) -> -- parameters
           (detpos : List Nat) -> -- determining arguments
           (datacons : List Name) ->
           (typehints : List (Name, Bool)) ->
           Def
    Hole : (invertible : Bool) -> Def
    BySearch : RigCount -> (maxdepth : Nat) -> (defining : Name) -> Def
    -- Constraints are integer references into the current map of
    -- constraints in the UnifyState (see Core.UnifyState)
    Guess : (guess : ClosedTerm) -> (constraints : List Int) -> Def
    ImpBind : Def -- global name temporarily standing for an implicitly bound name
    -- A delayed elaboration. The elaborators themselves are stored in the
    -- unifiation state
    Delayed : Def

export
Show Def where
  show None = "undefined"
  show (PMDef args ct rt pats) 
      = show args ++ "; " ++ show ct
  show (DCon t a) = "DataCon " ++ show t ++ " " ++ show a
  show (TCon t a ps ds cons hints) 
      = "TyCon " ++ show t ++ " " ++ show a ++ " " ++ show cons
  show (ExternDef arity) = "<external def with arith " ++ show arity ++ ">"
  show (Builtin {arity} _) = "<builtin with arith " ++ show arity ++ ">"
  show (Hole inv) = "Hole"
  show (BySearch c depth def) = "Search in " ++ show def
  show (Guess tm cs) = "Guess " ++ show tm ++ " when " ++ show cs
  show ImpBind = "Bound name"
  show Delayed = "Delayed"

export
TTC Def where
  toBuf b None = tag 0
  toBuf b (PMDef args ct rt pats) 
      = do tag 1; toBuf b args; toBuf b ct; toBuf b rt; toBuf b pats
  toBuf b (ExternDef a)
      = do tag 2; toBuf b a
  toBuf b (Builtin a)
      = throw (InternalError "Trying to serialise a Builtin")
  toBuf b (DCon t arity) = do tag 3; toBuf b t; toBuf b arity
  toBuf b (TCon t arity parampos detpos datacons _) 
      = do tag 4; toBuf b t; toBuf b arity; toBuf b parampos
           toBuf b detpos; toBuf b datacons
  toBuf b (Hole invertible) = do tag 5; toBuf b invertible
  toBuf b (BySearch c depth def) 
      = do tag 6; toBuf b c; toBuf b depth; toBuf b def
  toBuf b (Guess guess constraints) = do tag 7; toBuf b guess; toBuf b constraints
  toBuf b ImpBind = tag 8
  toBuf b Delayed = tag 9

  fromBuf r b 
      = case !getTag of
             0 => pure None
             1 => do args <- fromBuf r b 
                     ct <- fromBuf r b
                     rt <- fromBuf r b
                     pats <- fromBuf r b
                     pure (PMDef args ct rt pats)
             2 => do a <- fromBuf r b
                     pure (ExternDef a)
             3 => do t <- fromBuf r b; a <- fromBuf r b
                     pure (DCon t a)
             4 => do t <- fromBuf r b; a <- fromBuf r b
                     ps <- fromBuf r b; dets <- fromBuf r b; cs <- fromBuf r b
                     pure (TCon t a ps dets cs [])
             5 => do i <- fromBuf r b
                     pure (Hole i)
             6 => do c <- fromBuf r b; depth <- fromBuf r b
                     def <- fromBuf r b
                     pure (BySearch c depth def)
             7 => do g <- fromBuf r b; cs <- fromBuf r b
                     pure (Guess g cs)
             8 => pure ImpBind
             9 => pure Context.Delayed
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
    = Inline
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
  toBuf b Inline = tag 2
  toBuf b Invertible = tag 3
  toBuf b Overloadable = tag 4
  toBuf b TCInline = tag 5
  toBuf b (SetTotal x) = do tag 6; toBuf b x

  fromBuf s b
      = case !getTag of
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
  vars : List Name -- environment name is defined in
  visibility : Visibility
  totality : Totality
  flags : List DefFlag
  refersTo : NameMap () 
  noCycles : Bool -- for metavariables, whether they can be cyclic (this
                  -- would only be allowed when using a metavariable as a 
                  -- placeholder for a yet to be elaborated arguments, but
                  -- not for implicits because that'd indicate failing the
                  -- occurs check)
  linearChecked : Bool -- Flag whether we've already checked its linearity
  definition : Def

export
TTC GlobalDef where
  toBuf b gdef 
      = -- Only write full details for user specified names. The others will
        -- be holes where all we will ever need after loading is the definition
        do toBuf b (fullname gdef)
           toBuf b (definition gdef)
           when (isUserName (fullname gdef)) $
              do toBuf b (location gdef)
                 toBuf b (type gdef)
                 toBuf b (multiplicity gdef)
                 toBuf b (vars gdef)
                 toBuf b (visibility gdef)
                 toBuf b (totality gdef)
                 toBuf b (flags gdef)
                 toBuf b (map fst (toList (refersTo gdef)))
                 toBuf b (noCycles gdef)

  fromBuf r b 
      = do name <- fromBuf r b
           def <- fromBuf r b
           if isUserName name
              then do loc <- fromBuf r b; 
                      ty <- fromBuf r b; mul <- fromBuf r b
                      vars <- fromBuf r b
                      vis <- fromBuf r b; tot <- fromBuf r b
                      fl <- fromBuf r b
                      refsList <- fromBuf r b; 
                      let refs = fromList (map (\x => (x, ())) refsList)
                      c <- fromBuf r b
                      pure (MkGlobalDef loc name ty mul vars vis 
                                        tot fl refs c True def)
              else do let fc = emptyFC
                      pure (MkGlobalDef fc name (Erased fc)
                                        RigW [] Public unchecked [] empty
                                        False True def)

export
newDef : FC -> Name -> RigCount -> List Name -> 
         ClosedTerm -> Visibility -> Def -> GlobalDef
newDef fc n rig vars ty vis def 
    = MkGlobalDef fc n ty rig vars vis unchecked [] empty False False def

public export
record Defs where
  constructor MkDefs
  gamma : Context GlobalDef
  currentNS : List String -- namespace for current definitions
  options : Options
  toSave : NameMap ()
  nextTag : Int
  autoHints : NameMap Bool
     -- ^ global search hints. A mapping from the hint name, to whether it is
     -- a "default hint". A default hint is used only if all other attempts 
     -- to search fail (this flag is really only intended as a mechanism 
     -- for defaulting of literals)
  openHints : NameMap ()
     -- ^ currently open global hints; just for the rest of this module (not exported)
     -- and prioritised
  saveTypeHints : List (Name, Name, Bool)
     -- ^ a mapping from type names to hints (and a flag setting whether it's 
     -- a "direct" hint). Direct hints are searched first (as part of a group)
     -- the indirect hints. Indirect hints, in practice, are used to find
     -- instances of parent interfaces, and we don't search these until we've
     -- tried to find a direct result via a constructor or a top level hint.
     -- We don't look up anything in here, it's merely for saving out to TTC.
     -- We save the hints in the 'GlobalDef' itself for faster lookup.
  saveAutoHints : List (Name, Bool)
  ifaceHash : Int
  importHashes : List (List String, Int)
     -- ^ interface hashes of imported modules
  imported : List (List String, Bool, List String)
     -- ^ imported modules, whether to rexport, as namespace
  allImported : List (String, List String)
     -- ^ all imported filenames/namespaces, just to avoid loading something
     -- twice unnecessarily (this is a record of all the things we've
     -- called 'readFromTTC' with, in practice)
  cgdirectives : List (CG, String)
     -- ^ Code generator directives, which are free form text and thus to 
     -- be interpreted however the specific code generator requires

export
clearDefs : Defs -> Core Defs
clearDefs defs
    = do gam <- initCtxtS 1
         pure (record { gamma = gam } defs)

export
initDefs : Core Defs
initDefs 
    = do gam <- initCtxt
         pure (MkDefs gam ["Main"] defaults empty 100 
                      empty empty [] [] 5381 [] [] [] [])
      
-- Label for context references
export
data Ctxt : Type where

export
addHash : {auto c : Ref Ctxt Defs} ->
          Hashable a => a -> Core ()
addHash x
    = do defs <- get Ctxt
         put Ctxt (record { ifaceHash = hashWithSalt (ifaceHash defs) x } defs)

export
initHash : {auto c : Ref Ctxt Defs} -> 
           Core ()
initHash
    = do defs <- get Ctxt
         put Ctxt (record { ifaceHash = 5381 } defs)

export
addDef : {auto c : Ref Ctxt Defs} -> 
         Name -> GlobalDef -> Core Int
addDef n def
    = do defs <- get Ctxt
         (idx, gam') <- addCtxt n def (gamma defs)
         put Ctxt (record { gamma = gam' } defs)
         pure idx

export
addBuiltin : {auto x : Ref Ctxt Defs} ->
             Name -> ClosedTerm -> Totality ->
             PrimFn arity -> Core ()
addBuiltin n ty tot op 
    = do addDef n (MkGlobalDef emptyFC n ty RigW [] Public tot 
                               [Inline] empty False True (Builtin op)) 
         pure ()

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
updateTy : {auto c : Ref Ctxt Defs} ->
           Int -> ClosedTerm -> Core ()
updateTy i ty
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
              | Nothing => pure ()
         addDef (Resolved i) (record { type = ty } gdef)
         pure ()

-- Record that the name has been linearity checked so we don't need to do
-- it again
export
setLinearCheck : {auto c : Ref Ctxt Defs} ->
                 Int -> Bool -> Core ()
setLinearCheck i chk
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
              | Nothing => pure ()
         addDef (Resolved i) (record { linearChecked = chk } gdef)
         pure ()

export
setCtxt : {auto c : Ref Ctxt Defs} -> Context GlobalDef -> Core ()
setCtxt gam
    = do defs <- get Ctxt
         put Ctxt (record { gamma = gam } defs)

export
resolveName : {auto c : Ref Ctxt Defs} ->
              Name -> Core Int
resolveName (Resolved idx) = pure idx
resolveName n
    = do defs <- get Ctxt
         (i, gam') <- getPosition n (gamma defs)
         setCtxt gam'
         pure i

-- Call this before trying alternative elaborations, so that updates to the
-- context are put in the staging area rather than writing over the mutable
-- array of definitions.
-- Returns the old context (the one we'll go back to if the branch fails)
export
branch : {auto c : Ref Ctxt Defs} ->
         Core Defs
branch
    = do ctxt <- get Ctxt
         gam' <- branchCtxt (gamma ctxt)
         setCtxt gam'
         pure ctxt

-- Call this after trying an elaboration to commit any changes to the mutable
-- array of definitions once we know they're correct. Only actually commits
-- when we're right back at the top level
export
commit : {auto c : Ref Ctxt Defs} ->
         Core ()
commit
    = do ctxt <- get Ctxt
         gam' <- commitCtxt (gamma ctxt)
         setCtxt gam'


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
lookupExactBy : (GlobalDef -> a) -> Name -> Context GlobalDef -> 
                Core (Maybe a)
lookupExactBy fn n gam
    = do Just gdef <- lookupCtxtExact n gam
              | Nothing => pure Nothing
         pure (Just (fn gdef))

export
lookupNameBy : (GlobalDef -> a) -> Name -> Context GlobalDef -> 
               Core (List (Name, Int, a))
lookupNameBy fn n gam
    = do gdef <- lookupCtxtName n gam
         pure (map (\ (n, i, gd) => (n, i, fn gd)) gdef)

export
lookupDefExact : Name -> Context GlobalDef -> Core (Maybe Def)
lookupDefExact = lookupExactBy definition

export
lookupDefName : Name -> Context GlobalDef -> Core (List (Name, Int, Def))
lookupDefName = lookupNameBy definition 

export
lookupTyExact : Name -> Context GlobalDef -> Core (Maybe ClosedTerm)
lookupTyExact = lookupExactBy type 

export
lookupTyName : Name -> Context GlobalDef -> Core (List (Name, Int, ClosedTerm))
lookupTyName = lookupNameBy type 

-- private names are only visible in this namespace if their namespace
-- is the current namespace (or an outer one)
-- that is: given that most recent namespace is first in the list,
-- the namespace of 'n' is a suffix of nspace
export
visibleIn : (nspace : List String) -> Name -> Visibility -> Bool
visibleIn nspace (NS ns n) Private = isSuffixOf ns nspace
-- Public and Export names are always visible
visibleIn nspace n _ = True

export
setFlag : {auto c : Ref Ctxt Defs} ->
					FC -> Name -> DefFlag -> Core ()
setFlag fc n fl
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName fc n)
         let flags' = fl :: filter (/= fl) (flags def)
         addDef n (record { flags = flags' } def)
         pure ()

export
setNameFlag : {auto c : Ref Ctxt Defs} ->
			    		FC -> Name -> DefFlag -> Core ()
setNameFlag fc n fl
    = do defs <- get Ctxt
         [(n', i, def)] <- lookupCtxtName n (gamma defs)
              | [] => throw (UndefinedName fc n)
              | res => throw (AmbiguousName fc (map fst res))
         let flags' = fl :: filter (/= fl) (flags def)
         addDef (Resolved i) (record { flags = flags' } def)
         pure ()

export
unsetFlag : {auto c : Ref Ctxt Defs} ->
            FC -> Name -> DefFlag -> Core ()
unsetFlag fc n fl
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName fc n)
         let flags' = filter (/= fl) (flags def)
         addDef n (record { flags = flags' } def)
         pure ()

export
hasFlag : {auto c : Ref Ctxt Defs} ->
          FC -> Name -> DefFlag -> Core Bool
hasFlag fc n fl
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName fc n)
         pure (fl `elem` flags def)

export
setVisibility : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Visibility -> Core ()
setVisibility fc n vis
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName fc n)
         addDef n (record { visibility = vis } def)
         pure ()

-- Set a name as Private that was previously visible (and, if 'everywhere' is
-- set, hide in any modules imported by this one)
export
hide : {auto c : Ref Ctxt Defs} ->
       FC -> Name -> Core ()
hide fc n
    = do defs <- get Ctxt
         [(nsn, _)] <- lookupCtxtName n (gamma defs)
              | [] => throw (UndefinedName fc n)
              | res => throw (AmbiguousName fc (map fst res))
         setVisibility fc nsn Private

export
getVisibility : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core Visibility
getVisibility fc n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName fc n)
         pure $ visibility def

public export
record SearchData where
  constructor MkSearchData
  detArgs : List Nat -- determining argument positions
  hintGroups : List (List Name) -- names of functions to use as hints.
    {- In proof search, for every group of names
        * If exactly one succeeds, use it
        * If more than one succeeds, report an ambiguity error
        * If none succeed, move on to the next group

       This allows us to prioritise some names (e.g. to declare 'open' hints,
       which we might us to open an implementation working as a module, or to
       declare a named implementation to be used globally), and to have names
       which are only used if all else fails (e.g. as a defaulting mechanism),
       while the proof search mechanism doesn't need to know about any of the
       details.
    -}

-- Get the auto search data for a name.
export
getSearchData : {auto c : Ref Ctxt Defs} ->
                FC -> (defaults : Bool) -> Name ->
                Core SearchData
getSearchData fc defaults target
    = do defs <- get Ctxt
         Just (TCon _ _ _ dets cons hs) <- lookupDefExact target (gamma defs)
              | _ => throw (UndefinedName fc target)
         if defaults
            then let defaults = map fst (filter isDefault
                                             (toList (autoHints defs))) in
                     pure (MkSearchData [] [defaults])
            else let opens = map fst (toList (openHints defs))
                     autos = map fst (filter (not . isDefault) 
                                             (toList (autoHints defs)))
                     tyhs = map fst (filter direct hs) 
                     chasers = map fst (filter (not . direct) hs) in
                     pure (MkSearchData dets (filter isCons 
                               [opens, autos, tyhs, chasers]))
  where
    isDefault : (Name, Bool) -> Bool
    isDefault = snd

    direct : (Name, Bool) -> Bool
    direct = snd

export
setDetermining : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> List Name -> Core ()
setDetermining fc tyn args
    = do defs <- get Ctxt
         Just g <- lookupCtxtExact tyn (gamma defs) 
              | _ => throw (UndefinedName fc tyn)
         let TCon t a ps _ cons hs = definition g
              | _ => throw (GenericMsg fc (show (fullname g) ++ " is not a type constructor"))
         apos <- getPos 0 args (type g)
         updateDef tyn (const (Just (TCon t a ps apos cons hs)))
  where
    -- Type isn't normalised, but the argument names refer to those given
    -- explicitly in the type, so there's no need.
    getPos : Nat -> List Name -> Term vs -> Core (List Nat)
    getPos i ns (Bind _ x (Pi _ _ _) sc)
        = if x `elem` ns
             then do rest <- getPos (1 + i) (filter (/=x) ns) sc
                     pure $ i :: rest
             else getPos (1 + i) ns sc
    getPos _ [] _ = pure []
    getPos _ ns ty = throw (GenericMsg fc ("Unknown determining arguments: "
                           ++ showSep ", " (map show ns)))


export
addHintFor : {auto c : Ref Ctxt Defs} ->
					   FC -> Name -> Name -> Bool -> Core ()
addHintFor fc tyn hintn_in direct
    = do defs <- get Ctxt
         let hintn : Name
             = case hintn_in of
                    Resolved i => hintn_in
                    _ => case getNameID hintn_in (gamma defs) of
                              Nothing => hintn_in
                              Just idx => Resolved idx
         Just (TCon t a ps dets cons hs) <- lookupDefExact tyn (gamma defs)
              | _ => throw (GenericMsg fc (show tyn ++ " is not a type constructor"))
         updateDef tyn (const (Just (TCon t a ps dets cons ((hintn, direct) :: hs))))
         defs <- get Ctxt
         put Ctxt (record { saveTypeHints $= ((tyn, hintn, direct) :: )
                          } defs)

export
addGlobalHint : {auto c : Ref Ctxt Defs} ->
					      Name -> Bool -> Core ()
addGlobalHint hintn_in isdef
    = do defs <- get Ctxt
         let hintn : Name
             = case hintn_in of
                    Resolved i => hintn_in
                    _ => case getNameID hintn_in (gamma defs) of
                              Nothing => hintn_in
                              Just idx => Resolved idx
         put Ctxt (record { autoHints $= insert hintn isdef,
                            saveAutoHints $= ((hintn, isdef) ::) } defs)

export
addOpenHint : {auto c : Ref Ctxt Defs} -> Name -> Core ()
addOpenHint hintn_in
    = do defs <- get Ctxt
         let hintn : Name
             = case hintn_in of
                    Resolved i => hintn_in
                    _ => case getNameID hintn_in (gamma defs) of
                              Nothing => hintn_in
                              Just idx => Resolved idx
         put Ctxt (record { openHints $= insert hintn () } defs)

export
clearSavedHints : {auto c : Ref Ctxt Defs} -> Core ()
clearSavedHints
    = do defs <- get Ctxt
         put Ctxt (record { saveTypeHints = [],
                            saveAutoHints = [] } defs)

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

-- Add the module name, and namespace, of an imported module
-- (i.e. for "import X as Y", it's (X, Y)
-- "import public X" is, when rexported, the same as
-- "import X as [current namespace]")
export
addImported : {auto c : Ref Ctxt Defs} ->
              (List String, Bool, List String) -> Core ()
addImported mod
    = do defs <- get Ctxt
         put Ctxt (record { imported $= (mod ::) } defs)

export
getImported : {auto c : Ref Ctxt Defs} ->
              Core (List (List String, Bool, List String))
getImported
    = do defs <- get Ctxt
         pure (imported defs)

export
addDirective : {auto c : Ref Ctxt Defs} ->
               String -> String -> Core ()
addDirective c str
    = do defs <- get Ctxt
         case getCG c of
              Nothing => -- warn, rather than fail, because the CG may exist
                         -- but be unknown to this particular instance
                         coreLift $ putStrLn $ "Unknown code generator " ++ c
              Just cg => put Ctxt (record { cgdirectives $= ((cg, str) ::) } defs)

export
getDirectives : {auto c : Ref Ctxt Defs} ->
                CG -> Core (List String)
getDirectives cg
    = do defs <- get Ctxt
         pure (mapMaybe getDir (cgdirectives defs))
  where
    getDir : (CG, String) -> Maybe String
    getDir (x', str) = if cg == x' then Just str else Nothing

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
					List Name -> Visibility -> DataDef -> Core Int
addData vars vis (MkData (MkCon dfc tyn arity tycon) datacons)
    = do defs <- get Ctxt 
         tag <- getNextTypeTag 
         let tydef = newDef dfc tyn RigW vars tycon vis 
                            (TCon tag arity 
                                  (paramPos tyn (map type datacons))
                                  (allDet arity)
                                  (map name datacons) [])
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
        = do let condef = newDef fc n RigW vars ty (conVisibility vis) (DCon tag a)
             (idx, gam') <- addCtxt n condef gam
             addDataConstructors (tag + 1) cs gam'

-- Add a new nested namespace to the current namespace for new definitions
-- e.g. extendNS ["Data"] when namespace is "Prelude.List" leads to
-- current namespace of "Prelude.List.Data"
-- Inner namespaces go first, for ease of name lookup
export
extendNS : {auto c : Ref Ctxt Defs} ->
           List String -> Core ()
extendNS ns
    = do defs <- get Ctxt
         put Ctxt (record { currentNS $= ((reverse ns) ++) } defs)

-- Get the name as it would be defined in the current namespace
-- i.e. if it doesn't have an explicit namespace already, add it,
-- otherwise leave it alone
export
inCurrentNS : {auto c : Ref Ctxt Defs} ->
              Name -> Core Name
inCurrentNS (UN n)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) (UN n))
inCurrentNS n@(CaseBlock _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n@(WithBlock _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n@(MN _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n@(DN _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n = pure n

export
setVisible : {auto c : Ref Ctxt Defs} ->
             (nspace : List String) -> Core ()
setVisible nspace
    = do defs <- get Ctxt
         put Ctxt (record { gamma->visibleNS $= (nspace ::) } defs)

-- Return True if the given namespace is visible in the context (meaning
-- the namespace itself, and any namespace it's nested inside)
export
isVisible : {auto c : Ref Ctxt Defs} ->
            (nspace : List String) -> Core Bool
isVisible nspace
    = do defs <- get Ctxt
         pure (any visible (allParents (currentNS defs) ++ visibleNS (gamma defs)))
  where
    allParents : List String -> List (List String)
    allParents [] = []
    allParents (n :: ns) = (n :: ns) :: allParents ns

    -- Visible if any visible namespace is a suffix of the namespace we're
    -- asking about
    visible : List String -> Bool
    visible visns = isSuffixOf visns nspace

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
getFullName : {auto c : Ref Ctxt Defs} ->
              Name -> Core Name
getFullName (Resolved i)
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
              | Nothing => pure (Resolved i)
         pure (fullname gdef)
getFullName n = pure n

export
toFullNames : {auto c : Ref Ctxt Defs} ->
              Term vars -> Core (Term vars)
toFullNames tm
    = do defs <- get Ctxt
         full (gamma defs) tm
  where
    full : Context GlobalDef -> Term vars -> Core (Term vars)
    full gam (Ref fc x (Resolved i)) 
        = do Just gdef <- lookupCtxtExact (Resolved i) gam
                  | Nothing => pure (Ref fc x (Resolved i))
             pure (Ref fc x (fullname gdef))
    full gam (Meta fc x y xs) 
        = pure (Meta fc x y !(traverse (full gam) xs))
    full gam (Bind fc x b scope) 
        = pure (Bind fc x !(traverse (full gam) b) !(full gam scope))
    full gam (App fc fn p arg) 
        = pure (App fc !(full gam fn) p !(full gam arg))
    full gam (As fc p tm)
        = pure (As fc !(full gam p) !(full gam tm))
    full gam (TDelayed fc x y) 
        = pure (TDelayed fc x !(full gam y))
    full gam (TDelay fc x t y)
        = pure (TDelay fc x !(full gam t) !(full gam y))
    full gam (TForce fc y)
        = pure (TForce fc !(full gam y))
    full gam tm = pure tm

-- Getting and setting various options

export
getPPrint : {auto c : Ref Ctxt Defs} ->
            Core PPrinter
getPPrint
    = do defs <- get Ctxt
         pure (printing (options defs))

export
setPPrint : {auto c : Ref Ctxt Defs} ->
            PPrinter -> Core ()
setPPrint ppopts
    = do defs <- get Ctxt
         put Ctxt (record { options->printing = ppopts } defs)

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

export
setExtension : {auto c : Ref Ctxt Defs} -> LangExt -> Core ()
setExtension e
    = do defs <- get Ctxt
         put Ctxt (record { options $= setExtension e } defs)

export
isExtension : LangExt -> Defs -> Bool
isExtension e defs = isExtension e (options defs)

export
checkUnambig : {auto c : Ref Ctxt Defs} ->
               FC -> Name -> Core Name
checkUnambig fc n
    = do defs <- get Ctxt
         case !(lookupDefName n (gamma defs)) of
              [] => throw (UndefinedName fc n)
              [(fulln, i, _)] => pure (Resolved i)
              ns => throw (AmbiguousName fc (map fst ns))

export
lazyActive : {auto c : Ref Ctxt Defs} ->
             Bool -> Core ()
lazyActive a
    = do defs <- get Ctxt
         put Ctxt (record { options->elabDirectives->lazyActive = a } defs)

export
autoImplicits : {auto c : Ref Ctxt Defs} ->
                Bool -> Core ()
autoImplicits a
    = do defs <- get Ctxt
         put Ctxt (record { options->elabDirectives->autoImplicits = a } defs)

export
isLazyActive : {auto c : Ref Ctxt Defs} ->
               Core Bool
isLazyActive
    = do defs <- get Ctxt
         pure (lazyActive (elabDirectives (options defs)))

export
isAutoImplicits : {auto c : Ref Ctxt Defs} ->
                  Core Bool
isAutoImplicits
    = do defs <- get Ctxt
         pure (autoImplicits (elabDirectives (options defs)))

export
setPair : {auto c : Ref Ctxt Defs} ->
          FC -> (pairType : Name) -> (fstn : Name) -> (sndn : Name) ->
          Core ()
setPair fc ty f s
    = do defs <- get Ctxt
         ty' <- checkUnambig fc ty
         f' <- checkUnambig fc f
         s' <- checkUnambig fc s
         put Ctxt (record { options $= setPair ty' f' s' } defs)

export
setRewrite : {auto c : Ref Ctxt Defs} ->
             FC -> (eq : Name) -> (rwlemma : Name) -> Core ()
setRewrite fc eq rw
    = do defs <- get Ctxt
         rw' <- checkUnambig fc rw
         eq' <- checkUnambig fc eq
         put Ctxt (record { options $= setRewrite eq' rw' } defs)

-- Don't check for ambiguity here; they're all meant to be overloadable
export
setFromInteger : {auto c : Ref Ctxt Defs} ->
                 Name -> Core ()
setFromInteger n
    = do defs <- get Ctxt
         put Ctxt (record { options $= setFromInteger n } defs)

export
setFromString : {auto c : Ref Ctxt Defs} ->
                Name -> Core ()
setFromString n
    = do defs <- get Ctxt
         put Ctxt (record { options $= setFromString n } defs)

export
setFromChar : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
setFromChar n
    = do defs <- get Ctxt
         put Ctxt (record { options $= setFromChar n } defs)

export
addNameDirective : {auto c : Ref Ctxt Defs} ->
                   FC -> Name -> List String -> Core ()
addNameDirective fc n ns
    = do defs <- get Ctxt
         n' <- checkUnambig fc n
         put Ctxt (record { options $= addNameDirective (n', ns) } defs)

-- Checking special names from Options

export
isPairType : Name -> Defs -> Bool
isPairType n defs
    = case pairnames (options defs) of
           Nothing => False
           Just l => n == pairType l

export
fstName : Defs -> Maybe Name
fstName defs
    = do l <- pairnames (options defs)
         pure (fstName l)

export
sndName : Defs -> Maybe Name
sndName defs
    = do l <- pairnames (options defs)
         pure (sndName l)

export
getRewrite : Defs -> Maybe Name
getRewrite defs
    = do r <- rewritenames (options defs)
         pure (rewriteName r)

export
isEqualTy : Name -> Defs -> Bool
isEqualTy n defs
    = case rewritenames (options defs) of
           Nothing => False
           Just r => n == equalType r

export
fromIntegerName : Defs -> Maybe Name
fromIntegerName defs
    = fromIntegerName (primnames (options defs))

export
fromStringName : Defs -> Maybe Name
fromStringName defs
    = fromStringName (primnames (options defs))

export
fromCharName : Defs -> Maybe Name
fromCharName defs
    = fromCharName (primnames (options defs))

export
setLogLevel : {auto c : Ref Ctxt Defs} ->
              Nat -> Core ()
setLogLevel l
    = do defs <- get Ctxt
         put Ctxt (record { options->session->logLevel = l } defs)

export
setLogTimings : {auto c : Ref Ctxt Defs} ->
                Bool -> Core ()
setLogTimings b
    = do defs <- get Ctxt
         put Ctxt (record { options->session->logTimings = b } defs)

export
getSession : {auto c : Ref Ctxt Defs} ->
             Core Session
getSession
    = do defs <- get Ctxt
         pure (session (options defs))

-- Log message with a term, translating back to human readable names first
export
logTerm : {auto c : Ref Ctxt Defs} ->
          Nat -> Lazy String -> Term vars -> Core ()
logTerm lvl msg tm
    = do opts <- getSession
         if logLevel opts >= lvl
            then do tm' <- toFullNames tm
                    coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg 
                                          ++ ": " ++ show tm'
            else pure ()

export
log : {auto c : Ref Ctxt Defs} ->
      Nat -> Lazy String -> Core ()
log lvl msg
    = do opts <- getSession
         if logLevel opts >= lvl
            then coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg
            else pure ()

export
logC : {auto c : Ref Ctxt Defs} ->
       Nat -> Core String -> Core ()
logC lvl cmsg
    = do opts <- getSession
         if logLevel opts >= lvl
            then do msg <- cmsg
                    coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg
            else pure ()


export
logTime : {auto c : Ref Ctxt Defs} ->
          Lazy String -> Core a -> Core a
logTime str act
    = do opts <- getSession
         if logTimings opts
            then do clock <- coreLift clockTime
                    let nano = 1000000000
                    let t = seconds clock * nano + nanoseconds clock
                    res <- act
                    clock <- coreLift clockTime
                    let t' = seconds clock * nano + nanoseconds clock
                    let time = t' - t
                    assert_total $ -- We're not dividing by 0
                       coreLift $ putStrLn $ "TIMING " ++ str ++ ": " ++
                                show (time `div` nano) ++ "." ++ 
                                addZeros (unpack (show ((time `mod` nano) `div` 1000000))) ++
                                "s"
                    pure res
            else act
  where
    addZeros : List Char -> String
    addZeros [] = "000"
    addZeros [x] = "00" ++ cast x
    addZeros [x,y] = "0" ++ cast x ++ cast y
    addZeros str = pack str

