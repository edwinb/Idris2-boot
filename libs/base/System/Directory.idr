module System.Directory

import public System.File

public export
data Directory : Type where
  DHandle : (p : AnyPtr) -> Directory

export
dirOpen : (d : String) -> IO (Either FileError Directory)
-- dirOpen d
--     = do dptr <- foreign FFI_C "idris_dirOpen" (String -> IO Ptr) d
--          if !(nullPtr dptr)
--             then Left <$> getFileError
--             else pure (Right (DHandle dptr))

export
dirClose : Directory -> IO ()
-- dirClose (DHandle d) = foreign FFI_C "idris_dirClose" (Ptr -> IO ()) d

export
dirError : Directory -> IO Bool
-- dirError (DHandle d)
--     = do err <- foreign FFI_C "idris_dirError" (Ptr -> IO Int) d
--          pure (err /= 0)

export
dirEntry : Directory -> IO (Either FileError String)
-- dirEntry (DHandle d)
--     = do fn <- foreign FFI_C "idris_nextDirEntry" (Ptr -> IO String) d
--          if !(dirError (DHandle d))
--             then pure (Left FileReadError)
--             else pure (Right fn)

export
createDir : String -> IO (Either FileError ())
-- createDir d
--     = do ok <- foreign FFI_C "idris_mkdir" (String -> IO Int) d
--          if (ok == 0)
--             then pure (Right ())
--             else Left <$> getFileError

export
changeDir : String -> IO Bool
-- changeDir dir 
--     = do ok <- foreign FFI_C "idris_chdir" (String -> IO Int) dir
--          pure (ok == 0)

export
currentDir : IO String
-- currentDir = do
--   MkRaw s <- foreign FFI_C "idris_currentDir" (IO (Raw String))
--   pure s
