module Core.Options

import Core.Core
import Core.Name
import Core.TTC
import Utils.Binary

public export
record Dirs where
  constructor MkDirs
  working_dir : String
  build_dir : String -- build directory, relative to working directory
  dir_prefix : String -- installation prefix, for finding data files (e.g. run time support)
  extra_dirs : List String -- places to look for import files
  data_dirs : List String -- places to look for data file

public export
toString : Dirs -> String
toString (MkDirs wdir bdir dfix edirs ddirs) =
  unlines [ "+ Working Directory   :: " ++ show wdir
          , "+ Build Directory     :: " ++ show bdir
          , "+ Installation Prefix :: " ++ show dfix
          , "+ Extra Directories :: " ++ show edirs
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
TTC CG where
  toBuf b Chez = tag 0
  toBuf b Chicken = tag 1
  toBuf b Racket = tag 2

  fromBuf r b
      = case !getTag of
             0 => pure Chez
             1 => pure Chicken
             2 => pure Racket
             _ => corrupt "CG"

export
availableCGs : List (String, CG)
availableCGs = [("chez", Chez), ("chicken", Chicken), ("racket", Racket)]

export
getCG : String -> Maybe CG
getCG cg = lookup (toLower cg) availableCGs

-- Other options relevant to the current session (so not to be saved in a TTC)
public export
record Session where
  constructor MkSessionOpts
  noprelude : Bool
  codegen : CG

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

defaultDirs : Dirs
defaultDirs = MkDirs "." "build" "/usr/local" ["."] []

defaultPPrint : PPrinter
defaultPPrint = MkPPOpts False True False

defaultSession : Session
defaultSession = MkSessionOpts False Chez

export
defaults : Options
defaults = MkOptions defaultDirs defaultPPrint defaultSession

