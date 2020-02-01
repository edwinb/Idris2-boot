module System.Directory

import public System.File

toFileError : Int -> FileError
toFileError 1 = FileReadError
toFileError 2 = FileWriteError
toFileError 3 = FileNotFound
toFileError 4 = PermissionDenied
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
