module Idris.ModTree

import Core.Binary
import Core.Context
import Core.Core
import Core.Directory
import Core.Metadata
import Core.Options
import Core.Primitives
import Core.InitPrimitives
import Core.UnifyState

import Idris.Desugar
import Idris.Error
import Idris.Parser
import Idris.ProcessIdr
import Idris.REPLCommon
import Idris.Syntax

%default covering

record ModTree where
  constructor MkModTree
  nspace : List String
  sourceFile : Maybe String
  deps : List ModTree

-- A module file to build, and its list of dependencies
-- From this we can work out if the source file needs rebuilding, assuming
-- things are build in dependency order. A source file needs rebuilding
-- if:
--  + Its corresponding ttc is older than the source file
--  + Any of the import ttcs are *newer* than the corresponding ttc
--    (If so: also any imported ttc's fingerprint is different from the one
--    stored in the source file's ttc) 
public export
record BuildMod where
  constructor MkBuildMod
  buildFile : String
  buildNS : List String
  imports : List (List String)

export
Show BuildMod where
  show t = buildFile t ++ " [" ++ showSep ", " (map showNS (imports t)) ++ "]"
    where
      showNS : List String -> String
      showNS ns = showSep "." (reverse ns)

readHeader : {auto c : Ref Ctxt Defs} ->
             FC -> (mod : List String) -> Core (String, Module)
readHeader loc mod
    = do path <- nsToSource loc mod
         Right res <- coreLift (readFile path)
            | Left err => throw (FileErr path err)
         case runParser res (progHdr path) of
              Left err => throw (ParseFail (getParseErrorLoc path err) err)
              Right mod => pure (path, mod)

data AllMods : Type where

mkModTree : {auto c : Ref Ctxt Defs} ->
            {auto a : Ref AllMods (List (List String, ModTree))} ->
            FC -> 
            (done : List (List String)) -> -- if 'mod' is here we have a cycle
            (mod : List String) ->
            Core ModTree
mkModTree loc done mod
  = if mod `elem` done
       then throw (CyclicImports (done ++ [mod]))
       else 
          -- Read imports from source file. If the source file isn't
          -- available, it's not our responsibility
          catch (do all <- get AllMods
                    -- If we've seen it before, reuse what we found
                    case lookup mod all of
                         Nothing =>
                           do (file, modInfo) <- readHeader loc mod
                              let imps = map path (imports modInfo)
                              ms <- traverse (mkModTree loc done) imps
                              let mt = MkModTree mod (Just file) ms
                              all <- get AllMods
                              put AllMods ((mod, mt) :: all)
                              pure mt
                         Just m => pure m)
                -- Couldn't find source, assume it's in a package directory
                (\err => pure (MkModTree mod Nothing []))

-- Given a module tree, returns the modules in the reverse order they need to
-- be built, including their dependencies
mkBuildMods : List BuildMod -> ModTree -> List BuildMod
mkBuildMods acc mod
    = let req = buildDeps acc (reverse (deps mod)) in
          maybe req -- only build ones where we can find the source code
             (\sf => if sf `elem` map buildFile req
                        then req
                        else MkBuildMod sf (nspace mod) 
                                        (map nspace (deps mod)) :: req)
             (sourceFile mod)
  where
    buildDeps : List BuildMod -> List ModTree -> List BuildMod
    buildDeps acc [] = acc
    buildDeps acc (m :: ms) = buildDeps (mkBuildMods acc m) ms

-- Given a main file name, return the list of modules that need to be
-- built for that main file, in the order they need to be built
export
getBuildMods : {auto c : Ref Ctxt Defs} ->
               {auto o : Ref ROpts REPLOpts} ->
               FC -> (mainFile : String) -> 
               Core (List BuildMod)
getBuildMods loc fname
    = do a <- newRef AllMods []
         d <- getDirs

         t <- mkModTree {a} loc [] (pathToNS (working_dir d) fname)
         pure (reverse (mkBuildMods [] t))

fnameModified : String -> Core Integer
fnameModified fname
    = do Right f <- coreLift $ openFile fname Read
             | Left err => throw (FileErr fname err)
         Right t <- coreLift $ fileModifiedTime f
             | Left err => throw (FileErr fname err)
         coreLift $ closeFile f
         pure t

buildMod : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           FC -> Nat -> Nat -> BuildMod -> 
           Core (List Error)
-- Build from source if any of the dependencies, or the associated source
-- file, have a modification time which is newer than the module's ttc
-- file
buildMod loc num len mod
   = do clearCtxt; addPrimitives
        let src = buildFile mod
        mttc <- getTTCFileName src ".ttc"
        depFiles <- traverse (nsToPath loc) (imports mod)
        ttcTime <- catch (do t <- fnameModified mttc
                             pure (Just t))
                         (\err => pure Nothing)
        srcTime <- fnameModified src
        depTimes <- traverse (\f => do t <- fnameModified f
                                       pure (f, t)) depFiles
        let needsBuilding =
               case ttcTime of
                    Nothing => True
                    Just t => any (\x => x > t) (srcTime :: map snd depTimes)
        u <- newRef UST initUState
        m <- newRef MD initMetadata
        put Syn initSyntax

        let showMod = showSep "." (reverse (buildNS mod))

        if needsBuilding
           then do let msg = show num ++ "/" ++ show len ++
                                   ": Building " ++ showMod ++
                                   " (" ++ src ++ ")"
                   [] <- process {u} {m} msg src
                      | errs => do traverse emitError errs
                                   pure errs
                   pure []
           else pure []

buildMods : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto o : Ref ROpts REPLOpts} ->
            FC -> Nat -> Nat -> List BuildMod -> 
            Core (List Error)
buildMods fc num len [] = pure []
buildMods fc num len (m :: ms)
    = case !(buildMod fc num len m) of
           [] => buildMods fc (1 + num) len ms
           errs => pure errs

export
buildDeps : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto o : Ref ROpts REPLOpts} ->
            (mainFile : String) -> 
            Core (List Error)
buildDeps fname
    = do mods <- getBuildMods toplevelFC fname
         ok <- buildMods toplevelFC 1 (length mods) mods
         case ok of
              [] => do -- On success, reload the main ttc in a clean context
                       clearCtxt; addPrimitives
                       put MD initMetadata
                       mainttc <- getTTCFileName fname ".ttc"
                       log 10 $ "Reloading " ++ show mainttc
                       readAsMain mainttc

                       -- Load the associated metadata for interactive editing
                       mainttm <- getTTCFileName fname ".ttm"
                       log 10 $ "Reloading " ++ show mainttm
                       logTime "Reading TTM" $
                         readFromTTM mainttm
                       pure []
              errs => pure errs -- Error happened, give up

export
buildAll : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           (allFiles : List String) -> 
           Core (List Error)
buildAll allFiles
    = do mods <- traverse (getBuildMods toplevelFC) allFiles
         -- There'll be duplicates, so if something is already built, drop it
         let mods' = dropLater (concat mods)
         buildMods toplevelFC 1 (length mods') mods'
  where
    dropLater : List BuildMod -> List BuildMod
    dropLater [] = []
    dropLater (b :: bs)
        = b :: dropLater (filter (\x => buildFile x /= buildFile b) bs)

