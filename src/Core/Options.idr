module Core.Options

import Core.Core
import Core.Name
import Core.TT
import Utils.Binary

import System.Info

public export
record Dirs where
  constructor MkDirs
  working_dir : String
  source_dir : Maybe String -- source directory, relative to working directory
  build_dir : String -- build directory, relative to working directory
  exec_dir : String -- executable directory, relative to working directory
  dir_prefix : String -- installation prefix, for finding data files (e.g. run time support)
  extra_dirs : List String -- places to look for import files
  lib_dirs : List String -- places to look for libraries (for code generation)
  data_dirs : List String -- places to look for data file

public export
toString : Dirs -> String
toString (MkDirs wdir sdir bdir edir dfix edirs ldirs ddirs) =
  unlines [ "+ Working Directory   :: " ++ show wdir
          , "+ Source Directory    :: " ++ show sdir
          , "+ Build Directory     :: " ++ show bdir
          , "+ Executable Directory     :: " ++ show edir
          , "+ Installation Prefix :: " ++ show dfix
          , "+ Extra Directories :: " ++ show edirs
          , "+ CG Library Directories :: " ++ show ldirs
          , "+ Data Directories :: " ++ show ddirs]

public export
data CG = Chez
        | Racket
        | Gambit

export
Eq CG where
  Chez == Chez = True
  Racket == Racket = True
  Gambit == Gambit = True
  _ == _ = False

export
availableCGs : List (String, CG)
availableCGs
    = [("chez", Chez),
       ("racket", Racket),
       ("gambit", Gambit)]

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
record PrimCastNames where
  constructor MkPrimCastNames
  fromIntegerName : Maybe Name
  fromStringName : Maybe Name
  fromCharName : Maybe Name

public export
record PrimBuiltinNames where
  constructor MkPrimBuiltinNames
  -- Naturals
  builtinNatZero : Maybe Name
  builtinNatSucc : Maybe Name
  builtinNatToInteger : Maybe Name
  builtinIntegerToNat : Maybe Name
  builtinNatAdd : Maybe Name
  builtinNatSub : Maybe Name
  builtinNatMul : Maybe Name
  builtinNatDiv : Maybe Name
  builtinNatMod : Maybe Name
  builtinNatEq  : Maybe Name
  builtinNatLT  : Maybe Name
  builtinNatLTE : Maybe Name
  builtinNatGT  : Maybe Name
  builtinNatGTE : Maybe Name

public export
record PrimNames where
  constructor MkPrimNames
  primCastNames    : PrimCastNames
  primBuiltinNames : PrimBuiltinNames

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
  unboundImplicits : Bool
  totality : TotalReq
  ambigLimit : Nat
  undottedRecordProjections : Bool

public export
record Session where
  constructor MkSessionOpts
  noprelude : Bool
  nobanner : Bool
  findipkg : Bool
  codegen : CG
  logLevel : Nat
  logTimings : Bool
  debugElabCheck : Bool -- do conversion check to verify results of elaborator
  dumpcases : Maybe String -- file to output compiled case trees
  dumplifted : Maybe String -- file to output lambda lifted definitions
  dumpanf : Maybe String -- file to output ANF definitions
  dumpvmcode : Maybe String -- file to output VM code definitions

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

isWindows : Bool
isWindows = os `elem` ["windows", "mingw32", "cygwin32"]

export
sep : Char
sep = '/'

export
dirSep : String
dirSep = cast sep

export
pathSep : Char
pathSep = if isWindows then ';' else ':'

defaultDirs : Dirs
defaultDirs = MkDirs "." Nothing "build"
                     ("build" ++ dirSep ++ "exec")
                     "/usr/local" ["."] [] []

defaultPPrint : PPrinter
defaultPPrint = MkPPOpts False True False

defaultSession : Session
defaultSession = MkSessionOpts False False False Chez 0 False False
                               Nothing Nothing Nothing Nothing

defaultElab : ElabDirectives
defaultElab = MkElabDirectives True True PartialOK 3 True

defaultPrimNames : PrimNames
defaultPrimNames =
  MkPrimNames
    (MkPrimCastNames Nothing Nothing Nothing)
    (MkPrimBuiltinNames Nothing Nothing Nothing Nothing Nothing Nothing Nothing
       Nothing Nothing Nothing Nothing Nothing Nothing Nothing)

export
defaults : Options
defaults = MkOptions defaultDirs defaultPPrint defaultSession
                     defaultElab Nothing Nothing defaultPrimNames
                     []

-- Getters

export
getDefinedBuiltinNames : PrimBuiltinNames -> List Name
getDefinedBuiltinNames primBuiltinNames = catMaybes $
  [builtinNatZero, builtinNatSucc, builtinNatToInteger, builtinIntegerToNat,
   builtinNatAdd, builtinNatSub, builtinNatMul, builtinNatDiv, builtinNatMod,
   builtinNatEq, builtinNatLT, builtinNatLTE, builtinNatGT, builtinNatGTE] <*> [primBuiltinNames]

-- Reset the options which are set by source files
export
clearNames : Options -> Options
clearNames = record { pairnames = Nothing,
                      rewritenames = Nothing,
                      primnames = defaultPrimNames,
                      extensions = []
                    }

-- Setters

export
setPair : (pairType : Name) -> (fstn : Name) -> (sndn : Name) ->
          Options -> Options
setPair ty f s = record { pairnames = Just (MkPairNs ty f s) }

export
setRewrite : (eq : Name) -> (rwlemma : Name) -> Options -> Options
setRewrite eq rw = record { rewritenames = Just (MkRewriteNs eq rw) }

export
setFromInteger : Name -> Options -> Options
setFromInteger n = record { primnames->primCastNames->fromIntegerName = Just n }

export
setFromString : Name -> Options -> Options
setFromString n = record { primnames->primCastNames->fromStringName = Just n }

export
setFromChar : Name -> Options -> Options
setFromChar n = record { primnames->primCastNames->fromCharName = Just n }

export
setBuiltinNatZero : Name -> Options -> Options
setBuiltinNatZero n = record { primnames->primBuiltinNames->builtinNatZero = Just n }

export
setBuiltinNatSucc : Name -> Options -> Options
setBuiltinNatSucc n = record { primnames->primBuiltinNames->builtinNatSucc = Just n }

export
setBuiltinNatToInteger : Name -> Options -> Options
setBuiltinNatToInteger n = record { primnames->primBuiltinNames->builtinNatToInteger = Just n }

export
setBuiltinIntegerToNat : Name -> Options -> Options
setBuiltinIntegerToNat n = record { primnames->primBuiltinNames->builtinIntegerToNat = Just n }

export
setBuiltinNatAdd : Name -> Options -> Options
setBuiltinNatAdd n = record { primnames->primBuiltinNames->builtinNatAdd = Just n }

export
setBuiltinNatSub : Name -> Options -> Options
setBuiltinNatSub n = record { primnames->primBuiltinNames->builtinNatSub = Just n }

export
setBuiltinNatMul : Name -> Options -> Options
setBuiltinNatMul n = record { primnames->primBuiltinNames->builtinNatMul = Just n }

export
setBuiltinNatDiv : Name -> Options -> Options
setBuiltinNatDiv n = record { primnames->primBuiltinNames->builtinNatDiv = Just n }

export
setBuiltinNatMod : Name -> Options -> Options
setBuiltinNatMod n = record { primnames->primBuiltinNames->builtinNatMod = Just n }

export
setBuiltinNatEq : Name -> Options -> Options
setBuiltinNatEq n = record { primnames->primBuiltinNames->builtinNatEq = Just n }

export
setBuiltinNatLT : Name -> Options -> Options
setBuiltinNatLT n = record { primnames->primBuiltinNames->builtinNatLT = Just n }

export
setBuiltinNatLTE : Name -> Options -> Options
setBuiltinNatLTE n = record { primnames->primBuiltinNames->builtinNatLTE = Just n }

export
setBuiltinNatGT : Name -> Options -> Options
setBuiltinNatGT n = record { primnames->primBuiltinNames->builtinNatGT = Just n }

export
setBuiltinNatGTE : Name -> Options -> Options
setBuiltinNatGTE n = record { primnames->primBuiltinNames->builtinNatGTE = Just n }

export
setExtension : LangExt -> Options -> Options
setExtension e = record { extensions $= (e ::) }

export
isExtension : LangExt -> Options -> Bool
isExtension e opts = e `elem` extensions opts
