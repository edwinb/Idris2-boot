module Core.Binary

import Core.Context
import Core.Core
import Core.Hash
import Core.Normalise
import Core.Options
import Core.TT
import Core.TTC
import Core.UnifyState

import Data.IntMap
import Data.NameMap

-- Reading and writing 'Defs' from/to  a binary file
-- In order to be saved, a name must have been flagged using 'toSave'.
-- (Otherwise we'd save out everything, not just the things in the current
-- file).

import public Utils.Binary

import Data.Buffer

%default covering

-- increment this when changing anything in the data format
-- TTC files can only be compatible if the version number is the same
export
ttcVersion : Int
ttcVersion = 1

export
checkTTCVersion : Int -> Int -> Core ()
checkTTCVersion ver exp
  = if ver < exp
       then throw (TTCError FormatOlder)
       else if ver > exp
            then throw (TTCError FormatNewer)
            else pure ()

record TTCFile extra where
  constructor MkTTCFile
  version : Int
  ifaceHash : Int
  importHashes : List (List String, Int)
  holes : List (Int, (FC, Name))
  guesses : List (Int, (FC, Name))
  constraints : List (Int, Constraint)
  context : List (Name, Binary)
  autoHints : List (Name, Bool)
  typeHints : List (Name, Name, Bool)
  imported : List (List String, Bool, List String)
  nextVar : Int
  currentNS : List String
  pairnames : Maybe PairNames
  rewritenames : Maybe RewriteNames
  primnames : PrimNames
  namedirectives : List (Name, List String)
  cgdirectives : List (CG, String)
  extraData : extra

HasNames a => HasNames (List a) where
  full c [] = pure []
  full c (n :: ns) = pure $ !(full c n) :: !(full c ns)

  resolved c [] = pure []
  resolved c (n :: ns) = pure $ !(resolved c n) :: !(resolved c ns)

HasNames (Name, Bool) where
  full c (n, b) = pure (!(full c n), b)
  resolved c (n, b) = pure (!(resolved c n), b)

HasNames (Name, List String) where
  full c (n, b) = pure (!(full c n), b)
  resolved c (n, b) = pure (!(resolved c n), b)

HasNames (Name, Name, Bool) where
  full c (n1, n2, b) = pure (!(full c n1), !(full c n2), b)
  resolved c (n1, n2, b) = pure (!(resolved c n1), !(resolved c n2), b)

HasNames (Maybe Name) where
  full c Nothing = pure Nothing
  full c (Just n) = pure $ Just !(full c n)

  resolved c Nothing = pure Nothing
  resolved c (Just n) = pure $ Just !(resolved c n)

HasNames e => HasNames (TTCFile e) where
  full gam (MkTTCFile version ifaceHash iHashes
                      holes guesses constraints
                      context 
                      autoHints typeHints
                      imported nextVar currentNS 
                      pairnames rewritenames primnames
                      namedirectives cgdirectives
                      extra)
      = pure $ MkTTCFile version ifaceHash iHashes
                         holes guesses constraints
                         context
                         !(traverse (full gam) autoHints)
                         !(traverse (full gam) typeHints)
                         imported nextVar currentNS
                         !(fullPair gam pairnames)
                         !(fullRW gam rewritenames)
                         !(fullPrim gam primnames)
                         !(full gam namedirectives)
                         cgdirectives 
                         !(full gam extra)
    where
      fullPair : Context -> Maybe PairNames -> Core (Maybe PairNames)
      fullPair gam Nothing = pure Nothing
      fullPair gam (Just (MkPairNs t f s))
          = pure $ Just $ MkPairNs !(full gam t) !(full gam f) !(full gam s)

      fullRW : Context -> Maybe RewriteNames -> Core (Maybe RewriteNames)
      fullRW gam Nothing = pure Nothing
      fullRW gam (Just (MkRewriteNs e r))
          = pure $ Just $ MkRewriteNs !(full gam e) !(full gam r)

      fullPrim : Context -> PrimNames -> Core PrimNames
      fullPrim gam (MkPrimNs mi ms mc)
          = pure $ MkPrimNs !(full gam mi) !(full gam ms) !(full gam mc)


  -- I don't think we ever actually want to call this, because after we read
  -- from the file we're going to add them to learn what the resolved names
  -- are supposed to be! But for completeness, let's do it right.
  resolved gam (MkTTCFile version ifaceHash iHashes
                      holes guesses constraints
                      context 
                      autoHints typeHints
                      imported nextVar currentNS 
                      pairnames rewritenames primnames
                      namedirectives cgdirectives
                      extra)
      = pure $ MkTTCFile version ifaceHash iHashes
                         holes guesses constraints
                         context
                         !(traverse (resolved gam) autoHints)
                         !(traverse (resolved gam) typeHints)
                         imported nextVar currentNS
                         !(resolvedPair gam pairnames)
                         !(resolvedRW gam rewritenames)
                         !(resolvedPrim gam primnames)
                         !(resolved gam namedirectives)
                         cgdirectives
                         !(resolved gam extra)
    where
      resolvedPair : Context -> Maybe PairNames -> Core (Maybe PairNames)
      resolvedPair gam Nothing = pure Nothing
      resolvedPair gam (Just (MkPairNs t f s))
          = pure $ Just $ MkPairNs !(resolved gam t) !(resolved gam f) !(resolved gam s)

      resolvedRW : Context -> Maybe RewriteNames -> Core (Maybe RewriteNames)
      resolvedRW gam Nothing = pure Nothing
      resolvedRW gam (Just (MkRewriteNs e r))
          = pure $ Just $ MkRewriteNs !(resolved gam e) !(resolved gam r)

      resolvedPrim : Context -> PrimNames -> Core PrimNames
      resolvedPrim gam (MkPrimNs mi ms mc)
          = pure $ MkPrimNs !(resolved gam mi) !(resolved gam ms) !(resolved gam mc)


asName : List String -> Maybe (List String) -> Name -> Name
asName mod (Just ns) (NS oldns n) 
    = if mod == oldns 
         then NS ns n -- TODO: What about if there are nested namespaces in a module?
         else NS oldns n
asName _ _ n = n

-- NOTE: TTC files are only compatible if the version number is the same,
-- *and* the 'annot/extra' type are the same, or there are no holes/constraints
writeTTCFile : (HasNames extra, TTC extra) => 
               {auto c : Ref Ctxt Defs} ->
               Ref Bin Binary -> TTCFile extra -> Core ()
writeTTCFile b file_in
      = do file <- toFullNames file_in
           toBuf b "TTC"
           toBuf b (version file)
           toBuf b (ifaceHash file)
           toBuf b (importHashes file)
--            toBuf b (holes file)
--            toBuf b (guesses file)
--            toBuf b (constraints file)
           toBuf b (context file)
           toBuf b (autoHints file)
           toBuf b (typeHints file)
           toBuf b (imported file)
           toBuf b (nextVar file)
           toBuf b (currentNS file)
           toBuf b (pairnames file)
           toBuf b (rewritenames file)
           toBuf b (primnames file)
           toBuf b (namedirectives file)
           toBuf b (cgdirectives file)
           toBuf b (extraData file)

readTTCFile : TTC extra => 
              {auto c : Ref Ctxt Defs} ->
              List String -> Maybe (List String) ->
              Ref Bin Binary -> Core (TTCFile extra)
readTTCFile modns as b
      = do hdr <- fromBuf b
           when (hdr /= "TTC") $ corrupt "TTC header"
           ver <- fromBuf b
           checkTTCVersion ver ttcVersion
           ifaceHash <- fromBuf b
           importHashes <- fromBuf b
--            holes <- fromBuf b
--            coreLift $ putStrLn $ "Read " ++ show (length holes) ++ " holes"
--            guesses <- fromBuf b
--            coreLift $ putStrLn $ "Read " ++ show (length guesses) ++ " guesses"
--            constraints <- the (Core (List (Int, Constraint))) $ fromBuf b
--            coreLift $ putStrLn $ "Read " ++ show (length constraints) ++ " constraints"
           defs <- logTime "Definitions" $ fromBuf b
           autohs <- fromBuf b
           typehs <- fromBuf b
--            coreLift $ putStrLn ("Hints: " ++ show typehs)
--            coreLift $ putStrLn $ "Read " ++ show (length (map fullname defs)) ++ " defs"
           imp <- fromBuf b
           nextv <- fromBuf b
           cns <- fromBuf b
           pns <- fromBuf b
           rws <- fromBuf b
           prims <- fromBuf b
           nds <- fromBuf b
           cgds <- fromBuf b
           ex <- fromBuf b
           pure (MkTTCFile ver ifaceHash importHashes
                           [] [] [] defs -- holes guesses constraints defs 
                           autohs typehs imp nextv cns 
                           pns rws prims nds cgds ex)
-- Pull out the list of GlobalDefs that we want to save
getSaveDefs : List Name -> List (Name, Binary) -> Defs -> 
              Core (List (Name, Binary))
getSaveDefs [] acc _ = pure acc
getSaveDefs (n :: ns) acc defs
    = do Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => getSaveDefs ns acc defs -- 'n' really should exist though!
         -- No need to save builtins
         case definition gdef of
              Builtin _ => getSaveDefs ns acc defs
              _ => do bin <- initBinaryS 16384
                      toBuf bin !(full (gamma defs) gdef)
                      getSaveDefs ns ((fullname gdef, !(get Bin)) :: acc) defs

-- Write out the things in the context which have been defined in the
-- current source file
export
writeToTTC : (HasNames extra, TTC extra) =>
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             extra -> (fname : String) -> Core ()
writeToTTC extradata fname
    = do buf <- initBinary
         defs <- get Ctxt
         ust <- get UST
         gdefs <- getSaveDefs (keys (toSave defs)) [] defs
         log 5 $ "Writing " ++ fname ++ " with hash " ++ show (ifaceHash defs)
         writeTTCFile buf 
                   (MkTTCFile ttcVersion (ifaceHash defs) (importHashes defs)
                              (toList (holes ust)) 
                              (toList (guesses ust)) 
                              (toList (constraints ust))
                              gdefs
                              (saveAutoHints defs)
                              (saveTypeHints defs)
                              (imported defs)
                              (nextName ust)
                              (currentNS defs)
                              (pairnames (options defs)) 
                              (rewritenames (options defs)) 
                              (primnames (options defs)) 
                              (namedirectives (options defs)) 
                              (cgdirectives defs)
                              extradata)
         Right ok <- coreLift $ writeToFile fname !(get Bin)
               | Left err => throw (InternalError (fname ++ ": " ++ show err))
         pure ()

addGlobalDef : {auto c : Ref Ctxt Defs} ->
               (modns : List String) -> (importAs : Maybe (List String)) ->
               (Name, Binary) -> Core ()
addGlobalDef modns as (n, def)
    = do addContextEntry (asName modns as n) def
         pure ()

addTypeHint : {auto c : Ref Ctxt Defs} ->
              FC -> (Name, Name, Bool) -> Core ()
addTypeHint fc (tyn, hintn, d) 
   = do logC 10 (pure (show !(getFullName hintn) ++ " for " ++ 
                       show !(getFullName tyn)))
        addHintFor fc tyn hintn d True

addAutoHint : {auto c : Ref Ctxt Defs} ->
              (Name, Bool) -> Core ()
addAutoHint (hintn, d) = addGlobalHint hintn d

export
updatePair : {auto c : Ref Ctxt Defs} -> 
             Maybe PairNames -> Core ()
updatePair p
    = do defs <- get Ctxt
         put Ctxt (record { options->pairnames $= (p <+>) } defs)

export
updateRewrite : {auto c : Ref Ctxt Defs} -> 
                Maybe RewriteNames -> Core ()
updateRewrite r
    = do defs <- get Ctxt
         put Ctxt (record { options->rewritenames $= (r <+>) } defs)

export
updatePrimNames : PrimNames -> PrimNames -> PrimNames
updatePrimNames p
    = record { fromIntegerName $= ((fromIntegerName p) <+>),
               fromStringName $= ((fromStringName p) <+>),
               fromCharName $= ((fromCharName p) <+>) } 

export
updatePrims : {auto c : Ref Ctxt Defs} -> 
              PrimNames -> Core ()
updatePrims p
    = do defs <- get Ctxt
         put Ctxt (record { options->primnames $= updatePrimNames p } defs)

-- Add definitions from a binary file to the current context
-- Returns the "extra" section of the file (user defined data), the interface
-- hash and the list of additional TTCs that need importing
-- (we need to return these, rather than do it here, because after loading
-- the data that's when we process the extra data...)
export
readFromTTC : TTC extra =>
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> Bool ->
              (fname : String) -> -- file containing the module
              (modNS : List String) -> -- module namespace
              (importAs : List String) -> -- namespace to import as
              Core (Maybe (extra, Int, 
                           List (List String, Bool, List String)))
readFromTTC loc reexp fname modNS importAs
    = do defs <- get Ctxt
         -- If it's already in the context, don't load it again
         let False = (fname, importAs) `elem` allImported defs
              | True => pure Nothing
         put Ctxt (record { allImported $= ((fname, importAs) :: ) } defs)

         Right buf <- coreLift $ readFromFile fname
               | Left err => throw (InternalError (fname ++ ": " ++ show err))
         bin <- newRef Bin buf -- for reading the file into
         let as = if importAs == modNS 
                     then Nothing 
                     else Just importAs
         ttc <- readTTCFile modNS as bin
         logTime "Adding defs" $ traverse (addGlobalDef modNS as) (context ttc)
         setNS (currentNS ttc)
         -- Set up typeHints and autoHints based on the loaded data
         traverse_ (addTypeHint loc) (typeHints ttc)
         defs <- get Ctxt
         traverse_ addAutoHint (autoHints ttc)
         -- Set up pair/rewrite etc names
         updatePair (pairnames ttc)
         updateRewrite (rewritenames ttc)
         updatePrims (primnames ttc)
         -- TODO: Name directives

         when (not reexp) clearSavedHints
         resetFirstEntry

         -- Finally, update the unification state with the holes from the
         -- ttc
         ust <- get UST
         put UST (record { holes = fromList (holes ttc),
                           constraints = fromList (constraints ttc),
                           nextName = nextVar ttc } ust)
         pure (Just (extraData ttc, ifaceHash ttc, imported ttc))

getImportHashes : Ref Bin Binary ->
                  Core (List (List String, Int))
getImportHashes b
    = do hdr <- fromBuf {a = String} b
         when (hdr /= "TTC") $ corrupt "TTC header"
         ver <- fromBuf {a = Int} b
         checkTTCVersion ver ttcVersion
         ifaceHash <- fromBuf {a = Int} b
         fromBuf b

getHash : Ref Bin Binary -> Core Int
getHash b
    = do hdr <- fromBuf {a = String} b
         when (hdr /= "TTC") $ corrupt "TTC header"
         ver <- fromBuf {a = Int} b
         checkTTCVersion ver ttcVersion
         fromBuf b

export
readIFaceHash : (fname : String) -> -- file containing the module
                Core Int
readIFaceHash fname
    = do Right buf <- coreLift $ readFromFile fname
            | Left err => pure 0
         b <- newRef Bin buf
         catch (getHash b)
               (\err => pure 0)

export
readImportHashes : (fname : String) -> -- file containing the module
                   Core (List (List String, Int))
readImportHashes fname
    = do Right buf <- coreLift $ readFromFile fname
            | Left err => pure []
         b <- newRef Bin buf
         catch (getImportHashes b)
               (\err => pure [])

