module System.Directory

import public System.File

public export
data DirPtr : Type where

toFileError : Int -> FileError
toFileError 1 = FileReadError
toFileError 2 = FileWriteError
toFileError 3 = FileNotFound
toFileError 4 = PermissionDenied
toFileError 5 = FileExists
toFileError x = GenericFileError (x - 256)

fpure : Either Int a -> IO (Either FileError a)
fpure (Left err) = pure (Left (toFileError err))
fpure (Right x) = pure (Right x)

%foreign "scheme:blodwen-current-directory"
prim_currentDir : PrimIO String

%foreign "scheme:blodwen-change-directory"
prim_changeDir : String -> PrimIO Int

%foreign "scheme:blodwen-create-directory"
prim_createDir : String -> PrimIO (Either Int ())

%foreign "scheme:blodwen-open-directory"
prim_openDir : String -> PrimIO (Either Int DirPtr)

%foreign "scheme:blodwen-close-directory"
prim_closeDir : DirPtr -> PrimIO ()

%foreign "scheme:blodwen-next-dir-entry"
prim_dirEntry : DirPtr -> PrimIO (Either Int String)

export
data Directory : Type where
     MkDir : DirPtr -> Directory

export
createDir : String -> IO (Either FileError ())
createDir dir
    = do ok <- primIO (prim_createDir dir)
         fpure ok

export
changeDir : String -> IO Bool
changeDir dir
    = do ok <- primIO (prim_changeDir dir)
         pure (ok /= 0)

export
currentDir : IO String
currentDir = primIO prim_currentDir

export
dirOpen : String -> IO (Either FileError Directory)
dirOpen d
    = do res <- primIO (prim_openDir d)
         fpure (map MkDir res)

export
dirClose : Directory -> IO ()
dirClose (MkDir d) = primIO (prim_closeDir d)

export
dirEntry : Directory -> IO (Either FileError String)
dirEntry (MkDir d)
    = do res <- primIO (prim_dirEntry d)
         fpure res
