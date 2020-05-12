module System.File

import Data.List
import Data.Strings

public export
data Mode = Read | WriteTruncate | Append | ReadWrite | ReadWriteTruncate | ReadAppend

public export
FilePtr : Type
FilePtr = AnyPtr

support : String -> String
support fn = "C:" ++ fn ++ ", libidris2_support"

%foreign support "idris2_openFile"
prim__open : String -> String -> Int -> PrimIO FilePtr
%foreign support "idris2_closeFile"
prim__close : FilePtr -> PrimIO ()

%foreign support "idris2_fileError"
prim_error : FilePtr -> PrimIO Int

%foreign support "idris2_fileErrno"
prim_fileErrno : PrimIO Int

%foreign support "idris2_readLine"
prim__readLine : FilePtr -> PrimIO (Ptr String)
%foreign support "idris2_writeLine"
prim__writeLine : FilePtr -> String -> PrimIO Int
%foreign support "idris2_eof"
prim__eof : FilePtr -> PrimIO Int

%foreign support "idris2_fileModifiedTime"
prim__fileModifiedTime : FilePtr -> PrimIO Int

%foreign support "idris2_stdin"
prim__stdin : FilePtr
%foreign support "idris2_stdout"
prim__stdout : FilePtr
%foreign support "idris2_stderr"
prim__stderr : FilePtr

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

returnError : IO (Either FileError a)
returnError
    = do err <- primIO prim_fileErrno
         case err of
              0 => pure $ Left FileReadError
              1 => pure $ Left FileWriteError
              2 => pure $ Left FileNotFound
              3 => pure $ Left PermissionDenied
              4 => pure $ Left FileExists
              _ => pure $ Left (GenericFileError (err-5))

export
Show FileError where
  show (GenericFileError errno) = "File error: " ++ show errno
  show FileReadError = "File Read Error"
  show FileWriteError = "File Write Error"
  show FileNotFound = "File Not Found"
  show PermissionDenied = "Permission Denied"
  show FileExists = "File Exists"

ok : a -> IO (Either FileError a)
ok x = pure (Right x)

public export
data File : Type where
     FHandle : FilePtr -> File

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
         if prim__nullAnyPtr res /= 0
            then returnError
            else ok (FHandle res)

export
closeFile : File -> IO ()
closeFile (FHandle f) = primIO (prim__close f)

export
fGetLine : (h : File) -> IO (Either FileError String)
fGetLine (FHandle f)
    = do res <- primIO (prim__readLine f)
         if prim__nullPtr res /= 0
            then returnError
            else ok (prim__getString res)

export
fPutStr : (h : File) -> String -> IO (Either FileError ())
fPutStr (FHandle f) str
    = do res <- primIO (prim__writeLine f str)
         if res == 0
            then returnError
            else ok ()

export
fPutStrLn : (h : File) -> String -> IO (Either FileError ())
fPutStrLn f str = fPutStr f (str ++ "\n")

export
fEOF : (h : File) -> IO Bool
fEOF (FHandle f)
    = do res <- primIO (prim__eof f)
         pure (res /= 0)

export
fileModifiedTime : (h : File) -> IO (Either FileError Int)
fileModifiedTime (FHandle f)
    = do res <- primIO (prim__fileModifiedTime f)
         if res > 0
            then ok res
            else returnError

export
readFile : String -> IO (Either FileError String)
readFile file
  = do Right h <- openFile file Read
          | Left err => returnError
       Right content <- read [] h
          | Left err => do closeFile h
                           returnError
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
                        | Left err => returnError
                     read (str :: acc) h

||| Write a string to a file
export
writeFile : (filepath : String) -> (contents : String) ->
            IO (Either FileError ())
writeFile fn contents = do
     Right h  <- openFile fn WriteTruncate
        | Left err => pure (Left err)
     Right () <- fPutStr h contents
        | Left err => do closeFile h
                         pure (Left err)
     closeFile h
     pure (Right ())
