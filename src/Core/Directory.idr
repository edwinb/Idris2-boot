module Core.Directory

import Core.Context
import Core.Core
import Core.FC
import Core.Name
import Core.Options

import System.Info

%default total

isWindows : Bool
isWindows = os `elem` ["windows", "mingw32", "cygwin32"]

sep : Char
sep = '/'

export
dirSep : String
dirSep = cast sep

export
pathSep : Char
pathSep = if isWindows then ';' else ':'

fullPath : String -> List String
fullPath fp = filter (/="") $ split (==sep) fp

dropExtension : String -> String
dropExtension fname 
    = case span (/= '.') (reverse fname) of
           (all, "") => -- no extension
               reverse all
           (ext, root) => 
               -- assert that root can't be empty
               reverse (assert_total (strTail root))
    
-- Return the contents of the first file available in the list
firstAvailable : List String -> Core (Maybe String)
firstAvailable [] = pure Nothing
firstAvailable (f :: fs)
    = do Right ok <- coreLift $ openFile f Read
               | Left err => firstAvailable fs
         coreLift $ closeFile ok
         pure (Just f)

export
readDataFile : {auto c : Ref Ctxt Defs} ->
               String -> Core String
readDataFile fname
    = do d <- getDirs
         let fs = map (\p => p ++ cast sep ++ fname) (data_dirs d)
         Just f <- firstAvailable fs
            | Nothing => throw (InternalError ("Can't find data file " ++ fname))
         Right d <- coreLift $ readFile f
            | Left err => throw (FileErr f err)
         pure d

-- Given a namespace, return the full path to the checked module, 
-- looking first in the build directory then in the extra_dirs
export
nsToPath : {auto c : Ref Ctxt Defs} ->
           FC -> List String -> Core (Either Error String)
nsToPath loc ns
    = do d <- getDirs
         let fnameBase = showSep (cast sep) (reverse ns)
         let fs = map (\p => p ++ cast sep ++ fnameBase ++ ".ttc")
                      (build_dir d :: extra_dirs d)
         Just f <- firstAvailable fs
            | Nothing => pure (Left (ModuleNotFound loc ns))
         pure (Right f)

-- Given a namespace, return the full path to the source module (if it
-- exists in the working directory)
export
nsToSource : {auto c : Ref Ctxt Defs} ->
             FC -> List String -> Core String
nsToSource loc ns
    = do d <- getDirs
         let fnameBase = showSep (cast sep) (reverse ns)
         let fs = map (\ext => fnameBase ++ ext)
                      [".yaff", ".idr", ".lidr"]
         Just f <- firstAvailable fs
            | Nothing => throw (ModuleNotFound loc ns)
         pure f

-- Given a filename in the working directory, return the correct
-- namespace for it
export
pathToNS : String -> String -> List String
pathToNS wdir fname
    = let wsplit = splitSep wdir
          fsplit = splitSep fname in
          dropWdir wsplit fsplit fsplit
  where
    dropWdir : List String -> List String -> List String -> List String
    dropWdir wdir orig [] = []
    dropWdir wdir orig (x :: xs)
        = if wdir == xs
             then [x]
             else x :: dropWdir wdir orig xs

    splitSep : String -> List String
    splitSep fname 
        = case span (/=sep) fname of
               (end, "") => [dropExtension end]
               (mod, rest) => assert_total (splitSep (strTail rest)) ++ [mod]

-- Create subdirectories, if they don't exist
export
mkdirs : List String -> IO (Either FileError ())
mkdirs [] = pure (Right ())
mkdirs (d :: ds)
    = do ok <- changeDir d
         if ok
            then do mkdirs ds
                    changeDir ".."
                    pure (Right ())
            else do Right _ <- createDir d
                        | Left err => pure (Left err)
                    ok <- changeDir d
                    mkdirs ds
                    changeDir ".."
                    pure (Right ())

-- Given a namespace (i.e. a module name), make the build directory for the 
-- corresponding ttc file
export
makeBuildDirectory : {auto c : Ref Ctxt Defs} ->
                     List String -> Core ()
makeBuildDirectory ns
    = do d <- getDirs
         let bdir = build_dir d
         let ndirs = case ns of
                          [] => []
                          (n :: ns) => ns -- first item is file name
         let fname = showSep (cast sep) (reverse ndirs)
         Right _ <- coreLift $ mkdirs (build_dir d :: reverse ndirs)
            | Left err => throw (FileErr (bdir ++ cast sep ++ fname) err)
         pure ()

-- Given a source file, return the name of the ttc file to generate
export
getTTCFileName : {auto c : Ref Ctxt Defs} -> 
                 String -> String -> Core String
getTTCFileName inp ext
    = do ns <- getNS
         d <- getDirs
         -- Get its namespace from the file relative to the working directory
         -- and generate the ttc file from that
         let ns = pathToNS (working_dir d) inp
         let fname = showSep (cast sep) (reverse ns) ++ ext
         let bdir = build_dir d
         pure $ bdir ++ cast sep ++ fname

-- Given a root executable name, return the name in the build directory
export
getExecFileName : {auto c : Ref Ctxt Defs} -> String -> Core String
getExecFileName efile
    = do d <- getDirs
         pure $ build_dir d ++ cast sep ++ efile
