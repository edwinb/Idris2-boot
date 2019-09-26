module Core.Options

import Core.Core
import Core.Name
import Utils.Binary

public export
record Dirs where
  constructor MkDirs
  working_dir : String
  build_dir : String -- build directory, relative to working directory
  dir_prefix : String -- installation prefix, for finding data files (e.g. run time support)
  extra_dirs : List String -- places to look for import files
  lib_dirs : List String -- places to look for libraries (for code generation)
  data_dirs : List String -- places to look for data file

public export
toString : Dirs -> String
toString (MkDirs wdir bdir dfix edirs ldirs ddirs) =
  unlines [ "+ Working Directory   :: " ++ show wdir
          , "+ Build Directory     :: " ++ show bdir
          , "+ Installation Prefix :: " ++ show dfix
          , "+ Extra Directories :: " ++ show edirs
          , "+ CG Library Directories :: " ++ show ldirs
          , "+ Data Directories :: " ++ show ddirs]

public export
data CG = Chez
        | Chicken
        | Racket

export
Eq CG where
  Chez == Chez = True
  Chicken == Chicken = True
  Racket == Racket = True
  _ == _ = False

export
availableCGs : List (String, CG)
availableCGs = [("chez", Chez), ("chicken", Chicken), ("racket", Racket)]

export
getCG : String -> Maybe CG
getCG cg = lookup (toLower cg) availableCGs

-- Name options, to be saved in TTC
public export
record PairNames where
  constructor MkPairNs
  pairType : Name
  fstName : Name
  sndName : Name

public export
record RewriteNames where
  constructor MkRewriteNs
  equalType : Name
  rewriteName : Name

public export
record PrimNames where
  constructor MkPrimNs
  fromIntegerName : Maybe Name
  fromStringName : Maybe Name
  fromCharName : Maybe Name

public export
data LangExt = Borrowing -- not yet implemented

export
Eq LangExt where
  Borrowing == Borrowing = True

-- Other options relevant to the current session (so not to be saved in a TTC)
public export
record ElabDirectives where
  constructor MkElabDirectives
  lazyActive : Bool
  autoImplicits : Bool

public export
record Session where
  constructor MkSessionOpts
  noprelude : Bool
  nobanner : Bool
  codegen : CG
  logLevel : Nat
  logTimings : Bool

public export
record PPrinter where
  constructor MkPPOpts
  showImplicits : Bool
  showFullEnv : Bool
  fullNamespace : Bool

public export
record Options where
  constructor MkOptions
  dirs : Dirs
  printing : PPrinter
  session : Session
  elabDirectives : ElabDirectives
  pairnames : Maybe PairNames
  rewritenames : Maybe RewriteNames
  primnames : PrimNames
  extensions : List LangExt

defaultDirs : Dirs
defaultDirs = MkDirs "." "build" "/usr/local" ["."] ["."] []

defaultPPrint : PPrinter
defaultPPrint = MkPPOpts False True False

defaultSession : Session
defaultSession = MkSessionOpts False False Chez 0 False

defaultElab : ElabDirectives
defaultElab = MkElabDirectives True True

export
defaults : Options
defaults = MkOptions defaultDirs defaultPPrint defaultSession
                     defaultElab Nothing Nothing
                     (MkPrimNs Nothing Nothing Nothing)
                     []

-- Reset the options which are set by source files
export
clearNames : Options -> Options
clearNames = record { pairnames = Nothing,
                      rewritenames = Nothing,
                      primnames = MkPrimNs Nothing Nothing Nothing,
                      extensions = []
                    }

export
setPair : (pairType : Name) -> (fstn : Name) -> (sndn : Name) ->
          Options -> Options
setPair ty f s = record { pairnames = Just (MkPairNs ty f s) }

export
setRewrite : (eq : Name) -> (rwlemma : Name) -> Options -> Options
setRewrite eq rw = record { rewritenames = Just (MkRewriteNs eq rw) }

export
setFromInteger : Name -> Options -> Options
setFromInteger n = record { primnames->fromIntegerName = Just n }

export
setFromString : Name -> Options -> Options
setFromString n = record { primnames->fromStringName = Just n }

export
setFromChar : Name -> Options -> Options
setFromChar n = record { primnames->fromCharName = Just n }

export
setExtension : LangExt -> Options -> Options
setExtension e = record { extensions $= (e ::) }

export
isExtension : LangExt -> Options -> Bool
isExtension e opts = e `elem` extensions opts
