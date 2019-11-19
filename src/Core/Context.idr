module Core.Context

import        Core.CaseTree
import        Core.CompileExpr
import public Core.Core
import        Core.Env
import        Core.Hash
import public Core.Name
import        Core.Options
import public Core.TT

import Utils.Binary

import Data.IOArray
import Data.NameMap
import Data.StringMap
import Data.IntMap

import System

%default covering

public export
data Def : Type where
    None : Def -- Not yet defined
    PMDef : (alwaysReduce : Bool) -> -- always reduce, even when quoting etc
                 -- typically for inlinable metavariable solutions
            (args : List Name) ->
            (treeCT : CaseTree args) ->
            (treeRT : CaseTree args) ->
            (pats : List (vs ** (Env Term vs, Term vs, Term vs))) ->
                -- original checked patterns (LHS/RHS) with the names in
                -- the environment. Used for display purposes, and for helping
                -- find size changes in termination checking
            Def -- Ordinary function definition
    ExternDef : (arity : Nat) -> Def
    ForeignDef : (arity : Nat) ->
                 List String -> -- supported calling conventions,
                                -- e.g "C:printf,libc,stdlib.h", "scheme:display", ...
                 Def
    Builtin : {arity : Nat} -> PrimFn arity -> Def
    DCon : (tag : Int) -> (arity : Nat) -> Def -- data constructor
    TCon : (tag : Int) -> (arity : Nat) ->
           (parampos : List Nat) -> -- parameters
           (detpos : List Nat) -> -- determining arguments
           (mutwith : List Name) ->
           (datacons : List Name) ->
           Def
    Hole : (numlocs : Nat) -> -- Number of locals in scope at binding point
                              -- (mostly to help display)
           (implbind : Bool) -> -- Does this stand for an implicitly bound name
           Def
    BySearch : RigCount -> (maxdepth : Nat) -> (defining : Name) -> Def
    -- Constraints are integer references into the current map of
    -- constraints in the UnifyState (see Core.UnifyState)
    Guess : (guess : ClosedTerm) ->
            (envbind : Nat) -> -- Number of things in the environment when
                               -- we guessed the term
            (constraints : List Int) -> Def
    ImpBind : Def -- global name temporarily standing for an implicitly bound name
    -- A delayed elaboration. The elaborators themselves are stored in the
    -- unifiation state
    Delayed : Def

export
Show Def where
  show None = "undefined"
  show (PMDef _ args ct rt pats)
      = show args ++ "; " ++ show ct
  show (DCon t a) = "DataCon " ++ show t ++ " " ++ show a
  show (TCon t a ps ds ms cons)
      = "TyCon " ++ show t ++ " " ++ show a ++ " params: " ++ show ps ++
        " constructors: " ++ show cons ++
        " mutual with: " ++ show ms
  show (ExternDef arity) = "<external def with arity " ++ show arity ++ ">"
  show (ForeignDef a cs) = "<foreign def with arity " ++ show a ++
                           " " ++ show cs ++">"
  show (Builtin {arity} _) = "<builtin with arith " ++ show arity ++ ">"
  show (Hole _ p) = "Hole" ++ if p then " [impl]" else ""
  show (BySearch c depth def) = "Search in " ++ show def
  show (Guess tm _ cs) = "Guess " ++ show tm ++ " when " ++ show cs
  show ImpBind = "Bound name"
  show Delayed = "Delayed"

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
    | BlockedHint -- a hint, but blocked for the moment (so don't use)

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
    (==) BlockedHint BlockedHint = True
    (==) _ _ = False

public export
data SizeChange = Smaller | Same | Unknown

export
Show SizeChange where
  show Smaller = "Smaller"
  show Same = "Same"
  show Unknown = "Unknown"

public export
record SCCall where
     constructor MkSCCall
     fnCall : Name -- Function called
     fnArgs : List (Maybe (Nat, SizeChange))
        -- relationship to arguments of calling function; argument position
        -- (in the calling function), and how its size changed in the call.
        -- 'Nothing' if it's not related to any of the calling function's
        -- arguments

export
Show SCCall where
  show c = show (fnCall c) ++ ": " ++ show (fnArgs c)

public export
record GlobalDef where
  constructor MkGlobalDef
  location : FC
  fullname : Name -- original unresolved name
  type : ClosedTerm
  eraseArgs : List Nat -- which argument positions to erase at runtime
  multiplicity : RigCount
  vars : List Name -- environment name is defined in
  visibility : Visibility
  totality : Totality
  flags : List DefFlag
  refersToM : Maybe (NameMap Bool)
  invertible : Bool -- for an ordinary definition, is it invertible in unification
  noCycles : Bool -- for metavariables, whether they can be cyclic (this
                  -- would only be allowed when using a metavariable as a
                  -- placeholder for a yet to be elaborated arguments, but
                  -- not for implicits because that'd indicate failing the
                  -- occurs check)
  linearChecked : Bool -- Flag whether we've already checked its linearity
  definition : Def
  compexpr : Maybe CDef
  sizeChange : List SCCall

export
refersTo : GlobalDef -> NameMap Bool
refersTo def = maybe empty id (refersToM def)

-- Label for array references
export
data Arr : Type where

-- A context entry. If it's never been looked up, we haven't decoded the
-- binary blod yet, so decode it first time
public export
data ContextEntry : Type where
     Coded : Binary -> ContextEntry
     Decoded : GlobalDef -> ContextEntry

-- All the GlobalDefs. We can only have one context, because name references
-- point at locations in here, and if we have more than one the indices won't
-- match up. So, this isn't polymorphic.
export
record Context where
    constructor MkContext
    firstEntry : Int -- First entry in the current source file
    nextEntry : Int
    -- Map from full name to its position in the context
    resolvedAs : NameMap Int
    -- Map from strings to all the possible names in all namespaces
    possibles : StringMap (List (Name, Int))
    -- Reference to the actual content, indexed by Int
    content : Ref Arr (IOArray ContextEntry)
    -- Branching depth, in a backtracking elaborator. 0 is top level; at lower
    -- levels we need to stage updates rather than add directly to the
    -- 'content' store
    branchDepth : Nat
    -- Things which we're going to add, if this branch succeeds
    staging : IntMap ContextEntry

    -- Namespaces which are visible (i.e. have been imported)
    -- This only matters during evaluation and type checking, to control
    -- access in a program - in all other cases, we'll assume everything is
    -- visible
    visibleNS : List (List String)
    inlineOnly : Bool -- only return things with the 'alwaysReduce' flag

export
getContent : Context -> Ref Arr (IOArray ContextEntry)
getContent = content

-- Implemented later, once we can convert to and from full names
-- Defined in Core.TTC
export
decode : Context -> Int -> ContextEntry -> Core GlobalDef

initSize : Int
initSize = 10000

Grow : Int
Grow = initSize

export
initCtxtS : Int -> Core Context
initCtxtS s
    = do arr <- coreLift $ newArray s
         aref <- newRef Arr arr
         pure (MkContext 0 0 empty empty aref 0 empty [] False)

export
initCtxt : Core Context
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

export
newEntry : Name -> Context -> Core (Int, Context)
newEntry n ctxt
    = do let idx = nextEntry ctxt
         let a = content ctxt
         arr <- get Arr
         when (idx >= max arr) $
                 do arr' <- coreLift $ newArrayCopy (max arr + Grow) arr
                    put Arr arr'
         pure (idx, record { nextEntry = idx + 1,
                             resolvedAs $= insert n idx,
                             possibles $= addPossible n idx
                           } ctxt)

-- Get the position of the next entry in the context array, growing the
-- array if it's out of bounds.
-- Updates the context with the mapping from name to index
export
getPosition : Name -> Context -> Core (Int, Context)
getPosition (Resolved idx) ctxt = pure (idx, ctxt)
getPosition n ctxt
    = case lookup n (resolvedAs ctxt) of
           Just idx =>
              do pure (idx, ctxt)
           Nothing => newEntry n ctxt

export
getNameID : Name -> Context -> Maybe Int
getNameID (Resolved idx) ctxt = Just idx
getNameID n ctxt = lookup n (resolvedAs ctxt)

-- Add the name to the context, or update the existing entry if it's already
-- there.
-- If we're not at the top level, add it to the staging area
export
addCtxt : Name -> GlobalDef -> Context -> Core (Int, Context)
addCtxt n val ctxt_in
    = if branchDepth ctxt_in == 0
         then do (idx, ctxt) <- getPosition n ctxt_in
                 let a = content ctxt
                 arr <- get Arr
                 coreLift $ writeArray arr idx (Decoded val)
                 pure (idx, ctxt)
         else do (idx, ctxt) <- getPosition n ctxt_in
                 pure (idx, record { staging $= insert idx (Decoded val) } ctxt)

export
addEntry : Name -> ContextEntry -> Context -> Core (Int, Context)
addEntry n entry ctxt_in
    = if branchDepth ctxt_in == 0
         then do (idx, ctxt) <- getPosition n ctxt_in
                 let a = content ctxt
                 arr <- get Arr
                 coreLift $ writeArray arr idx entry
                 pure (idx, ctxt)
         else do (idx, ctxt) <- getPosition n ctxt_in
                 pure (idx, record { staging $= insert idx entry } ctxt)

returnDef : Bool -> Int -> GlobalDef -> Maybe (Int, GlobalDef)
returnDef False idx def = Just (idx, def)
returnDef True idx def
    = case definition def of
           PMDef True _ _ _ _ => Just (idx, def)
           _ => Nothing

export
lookupCtxtExactI : Name -> Context -> Core (Maybe (Int, GlobalDef))
lookupCtxtExactI (Resolved idx) ctxt
    = case lookup idx (staging ctxt) of
           Just val =>
                 pure $ returnDef (inlineOnly ctxt) idx !(decode ctxt idx val)
           Nothing =>
              do let a = content ctxt
                 arr <- get Arr
                 Just def <- coreLift (readArray arr idx)
                      | Nothing => pure Nothing
                 pure $ returnDef (inlineOnly ctxt) idx !(decode ctxt idx def)
lookupCtxtExactI n ctxt
    = do let Just idx = lookup n (resolvedAs ctxt)
                  | Nothing => pure Nothing
         lookupCtxtExactI (Resolved idx) ctxt

export
lookupCtxtExact : Name -> Context -> Core (Maybe GlobalDef)
lookupCtxtExact (Resolved idx) ctxt
    = case lookup idx (staging ctxt) of
           Just res =>
                do def <- decode ctxt idx res
                   case returnDef (inlineOnly ctxt) idx def of
                        Nothing => pure Nothing
                        Just (_, def) => pure (Just def)
           Nothing =>
              do let a = content ctxt
                 arr <- get Arr
                 Just res <- coreLift (readArray arr idx)
                      | Nothing => pure Nothing
                 def <- decode ctxt idx res
                 case returnDef (inlineOnly ctxt) idx def of
                      Nothing => pure Nothing
                      Just (_, def) => pure (Just def)
lookupCtxtExact n ctxt
    = do Just (i, def) <- lookupCtxtExactI n ctxt
              | Nothing => pure Nothing
         pure (Just def)

export
lookupCtxtName : Name -> Context -> Core (List (Name, Int, GlobalDef))
lookupCtxtName n ctxt
    = case userNameRoot n of
           Nothing => do Just (i, res) <- lookupCtxtExactI n ctxt
                              | Nothing => pure []
                         pure [(n, i, res)]
           Just r =>
              do let Just ps = lookup r (possibles ctxt)
                      | Nothing => pure []
                 ps' <- the (Core (List (Maybe (Name, Int, GlobalDef)))) $
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

    getMatches : List (Maybe (Name, Int, GlobalDef)) ->
                 Core (List (Name, Int, GlobalDef))
    getMatches [] = pure []
    getMatches (Nothing :: rs) = getMatches rs
    getMatches (Just r :: rs)
        = if matches n r
             then do rs' <- getMatches rs
                     pure (r :: rs')
             else getMatches rs

branchCtxt : Context -> Core Context
branchCtxt ctxt = pure (record { branchDepth $= S } ctxt)

commitCtxt : Context -> Core Context
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
    commitStaged : List (Int, ContextEntry) -> IOArray ContextEntry -> IO ()
    commitStaged [] arr = pure ()
    commitStaged ((idx, val) :: rest) arr
        = do writeArray arr idx val
             commitStaged rest arr

export
newDef : FC -> Name -> RigCount -> List Name ->
         ClosedTerm -> Visibility -> Def -> GlobalDef
newDef fc n rig vars ty vis def
    = MkGlobalDef fc n ty [] rig vars vis unchecked [] empty False False False def
                  Nothing []

public export
interface HasNames a where
  full : Context -> a -> Core a
  resolved : Context -> a -> Core a

export
HasNames Name where
  full gam (Resolved i)
      = do Just gdef <- lookupCtxtExact (Resolved i) gam
                | Nothing => do coreLift $ putStrLn $ "Missing name! " ++ show i
                                pure (Resolved i)
           pure (fullname gdef)
  full gam n = pure n

  resolved gam (Resolved i)
      = pure (Resolved i)
  resolved gam n
      = do let Just i = getNameID n gam
                    | Nothing => pure n
           pure (Resolved i)

export
HasNames (Term vars) where
  full gam (Ref fc x (Resolved i))
      = do Just gdef <- lookupCtxtExact (Resolved i) gam
                | Nothing => do coreLift $ putStrLn $ "Missing name! " ++ show i
                                pure (Ref fc x (Resolved i))
           pure (Ref fc x (fullname gdef))
  full gam (Meta fc x y xs)
      = pure (Meta fc x y !(traverse (full gam) xs))
  full gam (Bind fc x b scope)
      = pure (Bind fc x !(traverse (full gam) b) !(full gam scope))
  full gam (App fc fn arg)
      = pure (App fc !(full gam fn) !(full gam arg))
  full gam (As fc p tm)
      = pure (As fc !(full gam p) !(full gam tm))
  full gam (TDelayed fc x y)
      = pure (TDelayed fc x !(full gam y))
  full gam (TDelay fc x t y)
      = pure (TDelay fc x !(full gam t) !(full gam y))
  full gam (TForce fc y)
      = pure (TForce fc !(full gam y))
  full gam tm = pure tm

  resolved gam (Ref fc x n)
      = do let Just i = getNameID n gam
                | Nothing => pure (Ref fc x n)
           pure (Ref fc x (Resolved i))
  resolved gam (Meta fc x y xs)
      = do xs' <- traverse (resolved gam) xs
           let Just i = getNameID x gam
               | Nothing => pure (Meta fc x y xs')
           pure (Meta fc x i xs')
  resolved gam (Bind fc x b scope)
      = pure (Bind fc x !(traverse (resolved gam) b) !(resolved gam scope))
  resolved gam (App fc fn arg)
      = pure (App fc !(resolved gam fn) !(resolved gam arg))
  resolved gam (As fc p tm)
      = pure (As fc !(resolved gam p) !(resolved gam tm))
  resolved gam (TDelayed fc x y)
      = pure (TDelayed fc x !(resolved gam y))
  resolved gam (TDelay fc x t y)
      = pure (TDelay fc x !(resolved gam t) !(resolved gam y))
  resolved gam (TForce fc y)
      = pure (TForce fc !(resolved gam y))
  resolved gam tm = pure tm

mutual
  export
  HasNames (CaseTree vars) where
    full gam (Case i v ty alts)
        = pure $ Case i v !(full gam ty) !(traverse (full gam) alts)
    full gam (STerm tm)
        = pure $ STerm !(full gam tm)
    full gam t = pure t

    resolved gam (Case i v ty alts)
        = pure $ Case i v !(resolved gam ty) !(traverse (resolved gam) alts)
    resolved gam (STerm tm)
        = pure $ STerm !(resolved gam tm)
    resolved gam t = pure t

  export
  HasNames (CaseAlt vars) where
    full gam (ConCase n t args sc)
        = do sc' <- full gam sc
             Just gdef <- lookupCtxtExact n gam
                | Nothing => pure (ConCase n t args sc')
             pure $ ConCase (fullname gdef) t args sc'
    full gam (DelayCase ty arg sc)
        = pure $ DelayCase ty arg !(full gam sc)
    full gam (ConstCase c sc)
        = pure $ ConstCase c !(full gam sc)
    full gam (DefaultCase sc)
        = pure $ DefaultCase !(full gam sc)

    resolved gam (ConCase n t args sc)
        = do sc' <- resolved gam sc
             let Just i = getNameID n gam
                | Nothing => pure (ConCase n t args sc')
             pure $ ConCase (Resolved i) t args sc'
    resolved gam (DelayCase ty arg sc)
        = pure $ DelayCase ty arg !(resolved gam sc)
    resolved gam (ConstCase c sc)
        = pure $ ConstCase c !(resolved gam sc)
    resolved gam (DefaultCase sc)
        = pure $ DefaultCase !(resolved gam sc)

export
HasNames (Env Term vars) where
  full gam [] = pure []
  full gam (b :: bs)
      = pure $ !(traverse (full gam) b) :: !(full gam bs)

  resolved gam [] = pure []
  resolved gam (b :: bs)
      = pure $ !(traverse (resolved gam) b) :: !(resolved gam bs)

export
HasNames Def where
  full gam (PMDef r args ct rt pats)
      = pure $ PMDef r args !(full gam ct) !(full gam rt)
                     !(traverse fullNamesPat pats)
    where
      fullNamesPat : (vs ** (Env Term vs, Term vs, Term vs)) ->
                     Core (vs ** (Env Term vs, Term vs, Term vs))
      fullNamesPat (_ ** (env, lhs, rhs))
          = pure $ (_ ** (!(full gam env),
                          !(full gam lhs), !(full gam rhs)))
  full gam (TCon t a ps ds ms cs)
      = pure $ TCon t a ps ds !(traverse (full gam) ms)
                              !(traverse (full gam) cs)
  full gam (BySearch c d def)
      = pure $ BySearch c d !(full gam def)
  full gam (Guess tm b cs)
      = pure $ Guess !(full gam tm) b cs
  full gam t = pure t

  resolved gam (PMDef r args ct rt pats)
      = pure $ PMDef r args !(resolved gam ct) !(resolved gam rt)
                     !(traverse resolvedNamesPat pats)
    where
      resolvedNamesPat : (vs ** (Env Term vs, Term vs, Term vs)) ->
                         Core (vs ** (Env Term vs, Term vs, Term vs))
      resolvedNamesPat (_ ** (env, lhs, rhs))
          = pure $ (_ ** (!(resolved gam env),
                          !(resolved gam lhs), !(resolved gam rhs)))
  resolved gam (TCon t a ps ds ms cs)
      = pure $ TCon t a ps ds !(traverse (resolved gam) ms)
                              !(traverse (resolved gam) cs)
  resolved gam (BySearch c d def)
      = pure $ BySearch c d !(resolved gam def)
  resolved gam (Guess tm b cs)
      = pure $ Guess !(resolved gam tm) b cs
  resolved gam t = pure t

HasNames (NameMap a) where
  full gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : NameMap a -> List (Name, a) -> Core (NameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (insert !(full gam k) v ms) ns

  resolved gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : NameMap a -> List (Name, a) -> Core (NameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (insert !(resolved gam k) v ms) ns

export
HasNames PartialReason where
  full gam NotStrictlyPositive = pure NotStrictlyPositive
  full gam (BadCall ns) = pure $ BadCall !(traverse (full gam) ns)
  full gam (RecPath ns) = pure $ RecPath !(traverse (full gam) ns)

  resolved gam NotStrictlyPositive = pure NotStrictlyPositive
  resolved gam (BadCall ns) = pure $ BadCall !(traverse (resolved gam) ns)
  resolved gam (RecPath ns) = pure $ RecPath !(traverse (resolved gam) ns)

export
HasNames Terminating where
  full gam (NotTerminating p) = pure $ NotTerminating !(full gam p)
  full gam t = pure t

  resolved gam (NotTerminating p) = pure $ NotTerminating !(resolved gam p)
  resolved gam t = pure t

export
HasNames Covering where
  full gam IsCovering = pure IsCovering
  full gam (MissingCases ts)
      = pure $ MissingCases !(traverse (full gam) ts)
  full gam (NonCoveringCall ns)
      = pure $ NonCoveringCall !(traverse (full gam) ns)

  resolved gam IsCovering = pure IsCovering
  resolved gam (MissingCases ts)
      = pure $ MissingCases !(traverse (resolved gam) ts)
  resolved gam (NonCoveringCall ns)
      = pure $ NonCoveringCall !(traverse (resolved gam) ns)

export
HasNames Totality where
  full gam (MkTotality t c) = pure $ MkTotality !(full gam t) !(full gam c)
  resolved gam (MkTotality t c) = pure $ MkTotality !(resolved gam t) !(resolved gam c)

export
HasNames SCCall where
  full gam sc = pure $ record { fnCall = !(full gam (fnCall sc)) } sc
  resolved gam sc = pure $ record { fnCall = !(resolved gam (fnCall sc)) } sc

export
HasNames a => HasNames (Maybe a) where
  full gam Nothing = pure Nothing
  full gam (Just x) = pure $ Just !(full gam x)
  resolved gam Nothing = pure Nothing
  resolved gam (Just x) = pure $ Just !(resolved gam x)

export
HasNames GlobalDef where
  full gam def
      = do
--            ts <- full gam (type def)
--            d <- full gam (definition def)
--            coreLift $ printLn (fullname def, ts)
--            coreLift $ printLn (fullname def, d)
           pure $ record { type = !(full gam (type def)),
                           definition = !(full gam (definition def)),
                           totality = !(full gam (totality def)),
                           refersToM = !(full gam (refersToM def)),
                           sizeChange = !(traverse (full gam) (sizeChange def))
                         } def
  resolved gam def
      = pure $ record { type = !(resolved gam (type def)),
                        definition = !(resolved gam (definition def)),
                        totality = !(resolved gam (totality def)),
                        refersToM = !(resolved gam (refersToM def)),
                        sizeChange = !(traverse (resolved gam) (sizeChange def))
                      } def

public export
record Defs where
  constructor MkDefs
  gamma : Context
  mutData : List Name -- Currently declared but undefined data types
  currentNS : List String -- namespace for current definitions
  nestedNS : List (List String) -- other nested namespaces we can look in
  options : Options
  toSave : NameMap ()
  nextTag : Int
  typeHints : NameMap (List (Name, Bool))
     -- ^ a mapping from type names to hints (and a flag setting whether it's
     -- a "direct" hint). Direct hints are searched first (as part of a group)
     -- the indirect hints. Indirect hints, in practice, are used to find
     -- instances of parent interfaces, and we don't search these until we've
     -- tried to find a direct result via a constructor or a top level hint.
  autoHints : NameMap Bool
     -- ^ global search hints. A mapping from the hint name, to whether it is
     -- a "default hint". A default hint is used only if all other attempts
     -- to search fail (this flag is really only intended as a mechanism
     -- for defaulting of literals)
  openHints : NameMap ()
     -- ^ currently open global hints; just for the rest of this module (not exported)
     -- and prioritised
  saveTypeHints : List (Name, Name, Bool)
     -- We don't look up anything in here, it's merely for saving out to TTC.
     -- We save the hints in the 'GlobalDef' itself for faster lookup.
  saveAutoHints : List (Name, Bool)
  namedirectives : List (Name, List String)
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
  toCompile : List Name
     -- ^ Names which need to be compiled to run time case trees
  userHoles : NameMap ()
     -- ^ Metavariables the user still has to fill in. In practice, that's
     -- everything with a user accessible name and a definition of Hole
  timings : StringMap Integer
     -- ^ record of timings from logTimeRecord

-- Label for context references
export
data Ctxt : Type where


export
clearDefs : Defs -> Core Defs
clearDefs defs
    = pure (record { gamma->inlineOnly = True } defs)

export
initDefs : Core Defs
initDefs
    = do gam <- initCtxt
         pure (MkDefs gam [] ["Main"] [] defaults empty 100
                      empty empty empty [] [] [] 5381 [] [] [] [] [] empty
                      empty)

-- Reset the context, except for the options
export
clearCtxt : {auto c : Ref Ctxt Defs} ->
            Core ()
clearCtxt
    = do defs <- get Ctxt
         put Ctxt (record { options = options defs,
                            timings = timings defs } !initDefs)

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
addUserHole : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
addUserHole n
    = do defs <- get Ctxt
         put Ctxt (record { userHoles $= insert n () } defs)

export
clearUserHole : {auto c : Ref Ctxt Defs} ->
                Name -> Core ()
clearUserHole n
    = do defs <- get Ctxt
         put Ctxt (record { userHoles $= delete n } defs)

export
getUserHoles : {auto c : Ref Ctxt Defs} ->
               Core (List Name)
getUserHoles
    = do defs <- get Ctxt
         let hs = sort (keys (userHoles defs))
         filterM (isHole defs) hs
  where
    -- If a hole is declared in one file and defined in another, its
    -- name won't have been cleared unless we've already looked up its
    -- definition (as addDef needs to be called to clear it). So here
    -- check that it's really a hole
    isHole : Defs -> Name -> Core Bool
    isHole defs n
        = do Just def <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure True
             case definition def of
                  None => pure True
                  Hole _ _ => pure True
                  _ => pure False

export
addDef : {auto c : Ref Ctxt Defs} ->
         Name -> GlobalDef -> Core Int
addDef n def
    = do defs <- get Ctxt
         (idx, gam') <- addCtxt n def (gamma defs)
         put Ctxt (record { gamma = gam' } defs)
         case definition def of
              None => pure ()
              Hole _ _ => pure ()
              _ => clearUserHole (fullname def)
         pure idx

export
addContextEntry : {auto c : Ref Ctxt Defs} ->
                  Name -> Binary -> Core Int
addContextEntry n def
    = do defs <- get Ctxt
         (idx, gam') <- addEntry n (Coded def) (gamma defs)
         put Ctxt (record { gamma = gam' } defs)
         pure idx

export
addBuiltin : {auto x : Ref Ctxt Defs} ->
             Name -> ClosedTerm -> Totality ->
             PrimFn arity -> Core ()
addBuiltin n ty tot op
    = do addDef n (MkGlobalDef emptyFC n ty [] RigW [] Public tot
                               [Inline] empty False False True (Builtin op)
                               Nothing [])
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

export
setCompiled : {auto c : Ref Ctxt Defs} ->
              Name -> CDef -> Core ()
setCompiled n cexp
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure ()
         addDef n (record { compexpr = Just cexp } gdef)
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
setCtxt : {auto c : Ref Ctxt Defs} -> Context -> Core ()
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

export
addName : {auto c : Ref Ctxt Defs} ->
          Name -> Core Int
addName (Resolved idx) = pure idx
addName n
  = do defs <- get Ctxt
       (i, gam') <- newEntry n (gamma defs)
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
  = do defs <- get Ctxt
       gam' <- commitCtxt (gamma defs)
       setCtxt gam'

export
depth : {auto c : Ref Ctxt Defs} ->
      Core Nat
depth
  = do defs <- get Ctxt
       pure (branchDepth (gamma defs))

-- Explicitly note that the name should be saved when writing out a .ttc
export
addToSave : {auto c : Ref Ctxt Defs} ->
          Name -> Core ()
addToSave n
  = do defs <- get Ctxt
       put Ctxt (record { toSave $= insert !(full (gamma defs) n) () } defs)

-- Specific lookup functions
export
lookupExactBy : (GlobalDef -> a) -> Name -> Context ->
              Core (Maybe a)
lookupExactBy fn n gam
  = do Just gdef <- lookupCtxtExact n gam
            | Nothing => pure Nothing
       pure (Just (fn gdef))

export
lookupNameBy : (GlobalDef -> a) -> Name -> Context ->
             Core (List (Name, Int, a))
lookupNameBy fn n gam
  = do gdef <- lookupCtxtName n gam
       pure (map (\ (n, i, gd) => (n, i, fn gd)) gdef)

export
lookupDefExact : Name -> Context -> Core (Maybe Def)
lookupDefExact = lookupExactBy definition

export
lookupDefName : Name -> Context -> Core (List (Name, Int, Def))
lookupDefName = lookupNameBy definition

export
lookupTyExact : Name -> Context -> Core (Maybe ClosedTerm)
lookupTyExact = lookupExactBy type

export
lookupTyName : Name -> Context -> Core (List (Name, Int, ClosedTerm))
lookupTyName = lookupNameBy type

export
lookupDefTyExact : Name -> Context -> Core (Maybe (Def, ClosedTerm))
lookupDefTyExact = lookupExactBy (\g => (definition g, type g))

-- private names are only visible in this namespace if their namespace
-- is the current namespace (or an outer one)
-- that is: given that most recent namespace is first in the list,
-- the namespace of 'n' is a suffix of nspace
visibleIn : (nspace : List String) -> Name -> Visibility -> Bool
visibleIn nspace (NS ns n) Private = isSuffixOf ns nspace
-- Public and Export names are always visible
visibleIn nspace n _ = True

export
visibleInAny : (nspace : List (List String)) -> Name -> Visibility -> Bool
visibleInAny nss n vis = any (\ns => visibleIn ns n vis) nss

reducibleIn : (nspace : List String) -> Name -> Visibility -> Bool
reducibleIn nspace (NS ns (UN n)) Export = isSuffixOf ns nspace
reducibleIn nspace (NS ns (UN n)) Private = isSuffixOf ns nspace
reducibleIn nspace n _ = True

export
reducibleInAny : (nspace : List (List String)) -> Name -> Visibility -> Bool
reducibleInAny nss n vis = any (\ns => reducibleIn ns n vis) nss

export
toFullNames : {auto c : Ref Ctxt Defs} ->
              HasNames a => a -> Core a
toFullNames t
    = do defs <- get Ctxt
         full (gamma defs) t

export
toResolvedNames : {auto c : Ref Ctxt Defs} ->
                  HasNames a => a -> Core a
toResolvedNames t
    = do defs <- get Ctxt
         resolved (gamma defs) t

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
setSizeChange : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> List SCCall -> Core ()
setSizeChange loc n sc
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName loc n)
         addDef n (record { sizeChange = sc } def)
         pure ()

export
setTotality : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Totality -> Core ()
setTotality loc n tot
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName loc n)
         addDef n (record { totality = tot } def)
         pure ()

export
setCovering : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Covering -> Core ()
setCovering loc n tot
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName loc n)
         addDef n (record { totality->isCovering = tot } def)
         pure ()

export
setTerminating : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> Terminating -> Core ()
setTerminating loc n tot
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName loc n)
         addDef n (record { totality->isTerminating = tot } def)
         pure ()

export
getTotality : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Core Totality
getTotality loc n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName loc n)
         pure $ totality def

export
getSizeChange : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core (List SCCall)
getSizeChange loc n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName loc n)
         pure $ sizeChange def

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
  hintGroups : List (Bool, List Name)
       -- names of functions to use as hints, and whether ambiguity is allowed
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
         Just (TCon _ _ _ dets _ _) <- lookupDefExact target (gamma defs)
              | _ => throw (UndefinedName fc target)
         let hs = case lookup !(toFullNames target) (typeHints defs) of
                       Just hs => hs
                       Nothing => []
         if defaults
            then let defns = map fst (filter isDefault
                                             (toList (autoHints defs))) in
                     pure (MkSearchData [] [(False, defns)])
            else let opens = map fst (toList (openHints defs))
                     autos = map fst (filter (not . isDefault)
                                             (toList (autoHints defs)))
                     tyhs = map fst (filter direct hs)
                     chasers = map fst (filter (not . direct) hs) in
                     pure (MkSearchData dets (filter (isCons . snd)
                               [(False, opens),
                                (False, autos),
                                (False, tyhs),
                                (True, chasers)]))
  where
    isDefault : (Name, Bool) -> Bool
    isDefault = snd

    direct : (Name, Bool) -> Bool
    direct = snd

export
setMutWith : {auto c : Ref Ctxt Defs} ->
             FC -> Name -> List Name -> Core ()
setMutWith fc tn tns
    = do defs <- get Ctxt
         Just g <- lookupCtxtExact tn (gamma defs)
              | _ => throw (UndefinedName fc tn)
         let TCon t a ps dets _ cons = definition g
              | _ => throw (GenericMsg fc (show (fullname g) ++ " is not a type constructor [setMutWith]"))
         updateDef tn (const (Just (TCon t a ps dets tns cons)))

export
addMutData : {auto c : Ref Ctxt Defs} ->
             Name -> Core ()
addMutData n
    = do defs <- get Ctxt
         put Ctxt (record { mutData $= (n ::) } defs)

export
dropMutData : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
dropMutData n
    = do defs <- get Ctxt
         put Ctxt (record { mutData $= filter (/= n) } defs)

export
setDetermining : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> List Name -> Core ()
setDetermining fc tyn args
    = do defs <- get Ctxt
         Just g <- lookupCtxtExact tyn (gamma defs)
              | _ => throw (UndefinedName fc tyn)
         let TCon t a ps _ cons ms = definition g
              | _ => throw (GenericMsg fc (show (fullname g) ++ " is not a type constructor [setDetermining]"))
         apos <- getPos 0 args (type g)
         updateDef tyn (const (Just (TCon t a ps apos cons ms)))
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
					   FC -> Name -> Name -> Bool -> Bool -> Core ()
addHintFor fc tyn_in hintn_in direct loading
    = do defs <- get Ctxt
         tyn <- toFullNames tyn_in
          -- ^ We have to index by full name because of the order we load -
          -- the name may not be resolved yet when we load the hints.
          -- Revisit if this turns out to be a bottleneck (it seems unlikely)
         hintn <- toResolvedNames hintn_in

         let hs = case lookup tyn (typeHints defs) of
                       Just hs => hs
                       Nothing => []
         if loading
            then put Ctxt
                     (record { typeHints $= insert tyn ((hintn, direct) :: hs)
                             } defs)
            else put Ctxt
                     (record { typeHints $= insert tyn ((hintn, direct) :: hs),
                               saveTypeHints $= ((tyn, hintn, direct) :: )
                             } defs)

export
addGlobalHint : {auto c : Ref Ctxt Defs} ->
					      Name -> Bool -> Core ()
addGlobalHint hintn_in isdef
    = do defs <- get Ctxt
         hintn <- toResolvedNames hintn_in

         put Ctxt (record { autoHints $= insert hintn isdef,
                            saveAutoHints $= ((hintn, isdef) ::) } defs)

export
addOpenHint : {auto c : Ref Ctxt Defs} -> Name -> Core ()
addOpenHint hintn_in
    = do defs <- get Ctxt
         hintn <- toResolvedNames hintn_in
         put Ctxt (record { openHints $= insert hintn () } defs)

export
dropOpenHint : {auto c : Ref Ctxt Defs} -> Name -> Core ()
dropOpenHint hintn_in
    = do defs <- get Ctxt
         hintn <- toResolvedNames hintn_in
         put Ctxt (record { openHints $= delete hintn } defs)

export
setOpenHints : {auto c : Ref Ctxt Defs} -> NameMap () -> Core ()
setOpenHints hs
    = do d <- get Ctxt
         put Ctxt (record { openHints = hs } d)

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

-- Set the nested namespaces we're allowed to look inside
export
setNestedNS : {auto c : Ref Ctxt Defs} ->
              List (List String) -> Core ()
setNestedNS ns
    = do defs <- get Ctxt
         put Ctxt (record { nestedNS = ns } defs)

-- Get the default namespace for new definitions
export
getNS : {auto c : Ref Ctxt Defs} ->
        Core (List String)
getNS
    = do defs <- get Ctxt
         pure (currentNS defs)

-- Get the nested namespaces we're allowed to look inside
export
getNestedNS : {auto c : Ref Ctxt Defs} ->
              Core (List (List String))
getNestedNS
    = do defs <- get Ctxt
         pure (nestedNS defs)

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

-- If a name appears more than once in an argument list, only the first is
-- considered a parameter
dropReps : List (Maybe (Term vars)) -> List (Maybe (Term vars))
dropReps [] = []
dropReps {vars} (Just (Local fc r x p) :: xs)
    = Just (Local fc r x p) :: assert_total (dropReps (map toNothing xs))
  where
    toNothing : Maybe (Term vars) -> Maybe (Term vars)
    toNothing tm@(Just (Local _ _ v' _))
        = if x == v' then Nothing else tm
    toNothing tm = tm
dropReps (x :: xs) = x :: dropReps xs

updateParams : Maybe (List (Maybe (Term vars))) ->
                  -- arguments to the type constructor which could be
                  -- parameters
                  -- Nothing, as an argument, means this argument can't
                  -- be a parameter position
               List (Term vars) ->
                  -- arguments to an application
               List (Maybe (Term vars))
updateParams Nothing args = dropReps $ map couldBeParam args
  where
    couldBeParam : Term vars -> Maybe (Term vars)
    couldBeParam (Local fc r v p) = Just (Local fc r v p)
    couldBeParam _ = Nothing
updateParams (Just args) args' = dropReps $ zipWith mergeArg args args'
  where
    mergeArg : Maybe (Term vars) -> Term vars -> Maybe (Term vars)
    mergeArg (Just (Local fc r x p)) (Local _ _ y _)
        = if x == y then Just (Local fc r x p) else Nothing
    mergeArg _ _ = Nothing

getPs : Maybe (List (Maybe (Term vars))) -> Name -> Term vars ->
        Maybe (List (Maybe (Term vars)))
getPs acc tyn (Bind _ x (Pi _ _ ty) sc)
      = let scPs = getPs (map (map (map weaken)) acc) tyn sc in
            map (map shrink) scPs
  where
    shrink : Maybe (Term (x :: vars)) -> Maybe (Term vars)
    shrink Nothing = Nothing
    shrink (Just tm) = shrinkTerm tm (DropCons SubRefl)
getPs acc tyn tm
    = case getFnArgs tm of
           (Ref _ _ n, args) =>
              if n == tyn
                 then Just (updateParams acc args)
                 else acc
           _ => acc

toPos : Maybe (List (Maybe a)) -> List Nat
toPos Nothing = []
toPos (Just ns) = justPos 0 ns
  where
    justPos : Nat -> List (Maybe a) -> List Nat
    justPos i [] = []
    justPos i (Just x :: xs) = i :: justPos (1 + i) xs
    justPos i (Nothing :: xs) = justPos (1 + i) xs

getConPs : Maybe (List (Maybe (Term vars))) -> Name -> Term vars -> List Nat
getConPs acc tyn (Bind _ x (Pi _ _ ty) sc)
    = let bacc = getPs acc tyn ty in
          getConPs (map (map (map weaken)) bacc) tyn sc
getConPs acc tyn tm = toPos (getPs acc tyn tm)

combinePos : Eq a => List (List a) -> List a
combinePos [] = []
combinePos (xs :: xss) = filter (\x => all (elem x) xss) xs

paramPos : Name -> (dcons : List ClosedTerm) ->
           List Nat
paramPos tyn dcons = combinePos (map (getConPs Nothing tyn) dcons)

export
addData : {auto c : Ref Ctxt Defs} ->
					List Name -> Visibility -> Int -> DataDef -> Core Int
addData vars vis tidx (MkData (MkCon dfc tyn arity tycon) datacons)
    = do defs <- get Ctxt
         tag <- getNextTypeTag
         let tydef = newDef dfc tyn RigW vars tycon vis
                            (TCon tag arity
                                  (paramPos (Resolved tidx) (map type datacons))
                                  (allDet arity)
                                  [] (map name datacons))
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
                          Context -> Core Context
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
         pure (any visible (allParents (currentNS defs) ++
                            nestedNS defs ++
                            visibleNS (gamma defs)))
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
setCG : {auto c : Ref Ctxt Defs} ->
        CG -> Core ()
setCG cg
    = do defs <- get Ctxt
         put Ctxt (record { options->session->codegen = cg } defs)

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
addLibDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
addLibDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->lib_dirs $= (++ [dir]) } defs)

export
setBuildDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
setBuildDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->build_dir = dir } defs)

export
setSourceDir : {auto c : Ref Ctxt Defs} -> Maybe String -> Core ()
setSourceDir mdir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->source_dir = mdir } defs)

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
         put Ctxt (record { namedirectives $= ((n', ns) ::) } defs)

-- Checking special names from Options

export
isPairType : {auto c : Ref Ctxt Defs} ->
             Name -> Core Bool
isPairType n
    = do defs <- get Ctxt
         case pairnames (options defs) of
              Nothing => pure False
              Just l => pure $ !(getFullName n) == !(getFullName (pairType l))

export
fstName : {auto c : Ref Ctxt Defs} ->
          Core (Maybe Name)
fstName
    = do defs <- get Ctxt
         pure $ maybe Nothing (Just . fstName) (pairnames (options defs))

export
sndName : {auto c : Ref Ctxt Defs} ->
          Core (Maybe Name)
sndName
    = do defs <- get Ctxt
         pure $ maybe Nothing (Just . sndName) (pairnames (options defs))

export
getRewrite :{auto c : Ref Ctxt Defs} ->
            Core (Maybe Name)
getRewrite
    = do defs <- get Ctxt
         pure $ maybe Nothing (Just . rewriteName) (rewritenames (options defs))

export
isEqualTy : {auto c : Ref Ctxt Defs} ->
            Name -> Core Bool
isEqualTy n
    = do defs <- get Ctxt
         case rewritenames (options defs) of
              Nothing => pure False
              Just r => pure $ !(getFullName n) == !(getFullName (equalType r))

export
fromIntegerName : {auto c : Ref Ctxt Defs} ->
                  Core (Maybe Name)
fromIntegerName
    = do defs <- get Ctxt
         pure $ fromIntegerName (primnames (options defs))

export
fromStringName : {auto c : Ref Ctxt Defs} ->
                 Core (Maybe Name)
fromStringName
    = do defs <- get Ctxt
         pure $ fromStringName (primnames (options defs))

export
fromCharName : {auto c : Ref Ctxt Defs} ->
               Core (Maybe Name)
fromCharName
    = do defs <- get Ctxt
         pure $ fromCharName (primnames (options defs))

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
setDebugElabCheck : {auto c : Ref Ctxt Defs} ->
                    Bool -> Core ()
setDebugElabCheck b
    = do defs <- get Ctxt
         put Ctxt (record { options->session->debugElabCheck = b } defs)

export
getSession : {auto c : Ref Ctxt Defs} ->
             Core Session
getSession
    = do defs <- get Ctxt
         pure (session (options defs))

export
setSession : {auto c : Ref Ctxt Defs} ->
             Session -> Core ()
setSession sopts
    = do defs <- get Ctxt
         put Ctxt (record { options->session = sopts } defs)

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
logTimeOver : {auto c : Ref Ctxt Defs} ->
              Integer -> Core String -> Core a -> Core a
logTimeOver nsecs str act
    = do clock <- coreLift clockTime
         let nano = 1000000000
         let t = seconds clock * nano + nanoseconds clock
         res <- act
         clock <- coreLift clockTime
         let t' = seconds clock * nano + nanoseconds clock
         let time = t' - t
         when (time > nsecs) $
           assert_total $ -- We're not dividing by 0
              do str' <- str
                 coreLift $ putStrLn $ "TIMING " ++ str' ++ ": " ++
                          show (time `div` nano) ++ "." ++
                          addZeros (unpack (show ((time `mod` nano) `div` 1000000))) ++
                          "s"
         pure res
  where
    addZeros : List Char -> String
    addZeros [] = "000"
    addZeros [x] = "00" ++ cast x
    addZeros [x,y] = "0" ++ cast x ++ cast y
    addZeros str = pack str

export
logTimeWhen : {auto c : Ref Ctxt Defs} ->
              Bool -> Lazy String -> Core a -> Core a
logTimeWhen p str act
    = if p
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

-- for ad-hoc profiling, record the time the action takes and add it
-- to the time for the given category
export
logTimeRecord : {auto c : Ref Ctxt Defs} ->
                String -> Core a -> Core a
logTimeRecord key act
    = do clock <- coreLift clockTime
         let nano = 1000000000
         let t = seconds clock * nano + nanoseconds clock
         res <- act
         clock <- coreLift clockTime
         let t' = seconds clock * nano + nanoseconds clock
         let time = t' - t
         defs <- get Ctxt
         let tot = case lookup key (timings defs) of
                        Nothing => 0
                        Just t => t
         put Ctxt (record { timings $= insert key (tot + time) } defs)
         pure res

export
showTimeRecord : {auto c : Ref Ctxt Defs} ->
                 Core ()
showTimeRecord
    = do defs <- get Ctxt
         traverse_ showTimeLog (toList (timings defs))
  where
    addZeros : List Char -> String
    addZeros [] = "000"
    addZeros [x] = "00" ++ cast x
    addZeros [x,y] = "0" ++ cast x ++ cast y
    addZeros str = pack str

    showTimeLog : (String, Integer) -> Core ()
    showTimeLog (key, time)
        = do coreLift $ putStr (key ++ ": ")
             let nano = 1000000000
             assert_total $ -- We're not dividing by 0
                    coreLift $ putStrLn $ show (time `div` nano) ++ "." ++
                               addZeros (unpack (show ((time `mod` nano) `div` 1000000))) ++
                               "s"

export
logTime : {auto c : Ref Ctxt Defs} ->
          Lazy String -> Core a -> Core a
logTime str act
    = do opts <- getSession
         logTimeWhen (logTimings opts) str act

