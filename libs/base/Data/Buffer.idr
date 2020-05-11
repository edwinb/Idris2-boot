module Data.Buffer

import System.File

export
data Buffer : Type where
     MkBuffer : AnyPtr -> (size : Int) -> (loc : Int) -> Buffer

%foreign "scheme:blodwen-buffer-size"
prim__bufferSize : AnyPtr -> Int

export
rawSize : Buffer -> IO Int
rawSize (MkBuffer buf _ _)
    = pure (prim__bufferSize buf)

%foreign "scheme:blodwen-new-buffer"
prim__newBuffer : Int -> PrimIO AnyPtr

export
newBuffer : Int -> IO (Maybe Buffer)
newBuffer size
    = do buf <- primIO (prim__newBuffer size)
         let sz = prim__bufferSize buf
         if sz == 0
            then pure Nothing
            else pure $ Just $ MkBuffer buf size 0

export
resetBuffer : Buffer -> Buffer
resetBuffer (MkBuffer ptr s l) = MkBuffer ptr s 0

export
size : Buffer -> Int
size (MkBuffer _ s _) = s

%foreign "scheme:blodwen-buffer-setbyte"
prim__setByte : AnyPtr -> Int -> Int -> PrimIO ()

-- Assumes val is in the range 0-255
export
setByte : Buffer -> (loc : Int) -> (val : Int) -> IO ()
setByte (MkBuffer buf _ _) loc val
    = primIO (prim__setByte buf loc val)

%foreign "scheme:blodwen-buffer-getbyte"
prim__getByte : AnyPtr -> Int -> PrimIO Int

export
getByte : Buffer -> (loc : Int) -> IO Int
getByte (MkBuffer buf _ _) loc
    = primIO (prim__getByte buf loc)

%foreign "scheme:blodwen-buffer-setint"
prim__setInt : AnyPtr -> Int -> Int -> PrimIO ()

export
setInt : Buffer -> (loc : Int) -> (val : Int) -> IO ()
setInt (MkBuffer buf _ _) loc val
    = primIO (prim__setInt buf loc val)

%foreign "scheme:blodwen-buffer-getint"
prim__getInt : AnyPtr -> Int -> PrimIO Int

export
getInt : Buffer -> (loc : Int) -> IO Int
getInt (MkBuffer buf _ _) loc
    = primIO (prim__getInt buf loc)

%foreign "scheme:blodwen-buffer-setdouble"
prim__setDouble : AnyPtr -> Int -> Double -> PrimIO ()

export
setDouble : Buffer -> (loc : Int) -> (val : Double) -> IO ()
setDouble (MkBuffer buf _ _) loc val
    = primIO (prim__setDouble buf loc val)

%foreign "scheme:blodwen-buffer-getdouble"
prim__getDouble : AnyPtr -> Int -> PrimIO Double

export
getDouble : Buffer -> (loc : Int) -> IO Double
getDouble (MkBuffer buf _ _) loc
    = primIO (prim__getDouble buf loc)

-- Get the length of a string in bytes, rather than characters
export
%foreign "scheme:blodwen-stringbytelen"
stringByteLength : String -> Int

%foreign "scheme:blodwen-buffer-setstring"
prim__setString : AnyPtr -> Int -> String -> PrimIO ()

export
setString : Buffer -> (loc : Int) -> (val : String) -> IO ()
setString (MkBuffer buf _ _) loc val
    = primIO (prim__setString buf loc val)

%foreign "scheme:blodwen-buffer-getstring"
prim__getString : AnyPtr -> Int -> Int -> PrimIO String

export
getString : Buffer -> (loc : Int) -> (len : Int) -> IO String
getString (MkBuffer buf _ _) loc len
    = primIO (prim__getString buf loc len)

export
bufferData : Buffer -> IO (List Int)
bufferData buf
    = do len <- rawSize buf
         unpackTo [] len
  where
    unpackTo : List Int -> Int -> IO (List Int)
    unpackTo acc 0 = pure acc
    unpackTo acc loc
        = do val <- getByte buf (loc - 1)
             unpackTo (val :: acc) (loc - 1)

%foreign "scheme:blodwen-buffer-copydata"
prim__copyData : AnyPtr -> Int -> Int -> AnyPtr -> Int -> PrimIO ()

export
copyData : (src : Buffer) -> (start, len : Int) ->
           (dest : Buffer) -> (loc : Int) -> IO ()
copyData (MkBuffer src _ _) start len (MkBuffer dest _ _) loc
    = primIO (prim__copyData src start len dest loc)

%foreign "scheme:blodwen-readbuffer-bytes"
prim__readBufferBytes : FilePtr -> AnyPtr -> Int -> Int -> PrimIO Int

export
readBufferFromFile : BinaryFile -> Buffer -> (maxbytes : Int) ->
                     IO (Either FileError Buffer)
readBufferFromFile (FHandle h) (MkBuffer buf size loc) max
    = do read <- primIO (prim__readBufferBytes h buf loc max)
         if read >= 0
            then pure (Right (MkBuffer buf size (loc + read)))
            else pure (Left FileReadError)

%foreign "scheme:blodwen-readbuffer"
prim__readBuffer : FilePtr -> PrimIO AnyPtr

-- Create a new buffer by reading all the contents from the given file
-- Fails if no bytes can be read or buffer can't be created
export
createBufferFromFile : BinaryFile -> IO (Either FileError Buffer)
createBufferFromFile (FHandle h)
    = do buf <- primIO (prim__readBuffer h)
         let sz = prim__bufferSize buf
         if sz >= 0
            then pure (Right (MkBuffer buf sz sz))
            else pure (Left FileReadError)

%foreign "scheme:blodwen-writebuffer"
prim__writeBuffer : FilePtr -> AnyPtr -> Int -> Int -> PrimIO Int

export
writeBufferToFile : BinaryFile -> Buffer -> (maxbytes : Int) ->
                    IO (Either FileError Buffer)
writeBufferToFile (FHandle h) (MkBuffer buf size loc) max
    = do let maxwrite = size - loc
         let max' = if maxwrite < max then maxwrite else max
         written <- primIO (prim__writeBuffer h buf loc max')
         if written == max'
            then pure (Right (MkBuffer buf size (loc + max')))
            else pure (Left FileWriteError)

export
resizeBuffer : Buffer -> Int -> IO (Maybe Buffer)
resizeBuffer old newsize
    = do Just buf <- newBuffer newsize
              | Nothing => pure Nothing
         -- If the new buffer is smaller than the old one, just copy what
         -- fits
         let oldsize = size old
         let len = if newsize < oldsize then newsize else oldsize
         copyData old 0 len buf 0
         pure (Just buf)
