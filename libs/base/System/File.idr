module System.File

import Data.List
import Data.Strings

public export
data Mode = Read | WriteTruncate | Append | ReadWrite | ReadWriteTruncate | ReadAppend

public export
data FilePtr : Type where

%extern prim__open : String -> String -> Int ->
                     (1 x : %World) -> IORes (Either Int FilePtr)
%extern prim__close : FilePtr -> (1 x : %World) -> IORes ()
%extern prim__readLine : FilePtr -> (1 x : %World) -> IORes (Either Int String)
%extern prim__writeLine : FilePtr -> String -> (1 x : %World) -> IORes (Either Int ())
%extern prim__eof : FilePtr -> (1 x : %World) -> IORes Int

%extern prim__stdin : FilePtr
%extern prim__stdout : FilePtr
%extern prim__stderr : FilePtr

modeStr : Mode -> String
modeStr Read              = "r"
modeStr WriteTruncate     = "w"
modeStr Append            = "a"
modeStr ReadWrite         = "r+"
modeStr ReadWriteTruncate = "w+"
modeStr ReadAppend        = "a+"

public export
data FileError = GenericFileError Int -- errno
               | FileReadError
               | FileWriteError
               | FileNotFound
               | PermissionDenied
               | FileExists

export
Show FileError where
  show (GenericFileError errno) = "File error: " ++ show errno
  show FileReadError = "File Read Error"
  show FileWriteError = "File Write Error"
  show FileNotFound = "File Not Found"
  show PermissionDenied = "Permission Denied"
  show FileExists = "File Exists"

toFileError : Int -> FileError
toFileError 1 = FileReadError
toFileError 2 = FileWriteError
toFileError 3 = FileNotFound
toFileError 4 = PermissionDenied
toFileError x = GenericFileError (x - 256)

fpure : Either Int a -> IO (Either FileError a)
fpure (Left err) = pure (Left (toFileError err))
fpure (Right x) = pure (Right x)

public export
data FileT : Bool -> Type where
     FHandle : FilePtr -> FileT bin

public export
File : Type
File = FileT False

public export
BinaryFile : Type
BinaryFile = FileT True

export
stdin : File
stdin = FHandle prim__stdin

export
stdout : File
stdout = FHandle prim__stdout

export
stderr : File
stderr = FHandle prim__stderr

export
openFile : String -> Mode -> IO (Either FileError File)
openFile f m
    = do res <- primIO (prim__open f (modeStr m) 0)
         fpure (map FHandle res)

export
openBinaryFile : String -> Mode -> IO (Either FileError BinaryFile)
openBinaryFile f m
    = do res <- primIO (prim__open f (modeStr m) 1)
         fpure (map FHandle res)

export
closeFile : FileT t -> IO ()
closeFile (FHandle f) = primIO (prim__close f)

export
fGetLine : (h : File) -> IO (Either FileError String)
fGetLine (FHandle f)
    = do res <- primIO (prim__readLine f)
         fpure res

export
fPutStr : (h : File) -> String -> IO (Either FileError ())
fPutStr (FHandle f) str
    = do res <- primIO (prim__writeLine f str)
         fpure res

export
fPutStrLn : (h : File) -> String -> IO (Either FileError ())
fPutStrLn f str = fPutStr f (str ++ "\n")

export
fEOF : (h : File) -> IO Bool
fEOF (FHandle f)
    = do res <- primIO (prim__eof f)
         pure (res /= 0)

export
readFile : String -> IO (Either FileError String)
readFile file
  = do Right h <- openFile file Read
          | Left err => pure (Left err)
       Right content <- read [] h
          | Left err => do closeFile h
                           pure (Left err)
       closeFile h
       pure (Right (fastAppend content))
  where
    read : List String -> File -> IO (Either FileError (List String))
    read acc h
        = do eof <- fEOF h
             if eof
                then pure (Right (reverse acc))
                else
                  do Right str <- fGetLine h
                        | Left err => pure (Left err)
                     read (str :: acc) h
