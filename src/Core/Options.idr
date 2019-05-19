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

-- Name options, to be saved in TTC
public export
record LazyNames where
  constructor MkLazy
  active : Bool
  delayType : Name
  delay : Name
  force : Name
  infinite : Name

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

export
TTC LazyNames where
  toBuf b l
      = do toBuf b (delayType l)
           toBuf b (delay l)
           toBuf b (force l)
           toBuf b (infinite l)
  fromBuf r b
      = do ty <- fromBuf r b
           d <- fromBuf r b
           f <- fromBuf r b
           i <- fromBuf r b
           pure (MkLazy True ty d f i)

export
TTC PairNames where
  toBuf b l
      = do toBuf b (pairType l)
           toBuf b (fstName l)
           toBuf b (sndName l)
  fromBuf r b
      = do ty <- fromBuf r b
           d <- fromBuf r b
           f <- fromBuf r b
           pure (MkPairNs ty d f)

export
TTC RewriteNames where
  toBuf b l
      = do toBuf b (equalType l)
           toBuf b (rewriteName l)
  fromBuf r b
      = do ty <- fromBuf r b
           l <- fromBuf r b
           pure (MkRewriteNs ty l)

export
TTC PrimNames where
  toBuf b l
      = do toBuf b (fromIntegerName l)
           toBuf b (fromStringName l)
           toBuf b (fromCharName l)
  fromBuf r b
      = do i <- fromBuf r b
           str <- fromBuf r b
           c <- fromBuf r b
           pure (MkPrimNs i str c)

-- Other options relevant to the current session (so not to be saved in a TTC)
public export
record Session where
  constructor MkSessionOpts
  noprelude : Bool
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
  laziness : Maybe LazyNames
  pairnames : Maybe PairNames
  rewritenames : Maybe RewriteNames
  primnames : PrimNames
  namedirectives : List (Name, List String)

defaultDirs : Dirs
defaultDirs = MkDirs "." "build" "/usr/local" ["."] []

defaultPPrint : PPrinter
defaultPPrint = MkPPOpts False True False

defaultSession : Session
defaultSession = MkSessionOpts False Chez 0 False

export
defaults : Options
defaults = MkOptions defaultDirs defaultPPrint defaultSession
                     Nothing Nothing Nothing
                     (MkPrimNs Nothing Nothing Nothing)
                     []

export
setLazy : (delayType : Name) -> (delay : Name) -> (force : Name) ->
          (infinite : Name) -> Options -> Options
setLazy ty d f i = record { laziness = Just (MkLazy True ty d f i) }

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
addNameDirective : (Name, List String) -> Options -> Options
addNameDirective nd = record { namedirectives $= (nd ::) }

