module Data.Buffer

import System.File

export
data Buffer : Type where
     MkBuffer : AnyPtr -> (size : Int) -> (loc : Int) -> Buffer

support : String -> String
support fn = "C:" ++ fn ++ ", libidris2_support"

%foreign support "idris2_getBufferSize"
prim__bufferSize : AnyPtr -> Int

%foreign support "idris2_isNull"
prim__nullPtr : AnyPtr -> Int

export
rawSize : Buffer -> IO Int
rawSize (MkBuffer buf _ _)
    = pure (prim__bufferSize buf)

%foreign support "idris2_newBuffer"
prim__newBuffer : Int -> PrimIO AnyPtr

%foreign support "idris2_freeBuffer"
prim__freeBuffer : AnyPtr -> PrimIO ()

export
newBuffer : Int -> IO (Maybe Buffer)
newBuffer size
    = do buf <- primIO (prim__newBuffer size)
         if prim__nullPtr buf /= 0
            then pure Nothing
            else pure $ Just $ MkBuffer buf size 0

export
freeBuffer : Buffer -> IO ()
freeBuffer (MkBuffer buf _ _) = primIO (prim__freeBuffer buf)

export
resetBuffer : Buffer -> Buffer
resetBuffer (MkBuffer ptr s l) = MkBuffer ptr s 0

export
size : Buffer -> Int
size (MkBuffer _ s _) = s

%foreign support "idris2_setBufferByte"
prim__setByte : AnyPtr -> Int -> Int -> PrimIO ()

-- Assumes val is in the range 0-255
export
setByte : Buffer -> (loc : Int) -> (val : Int) -> IO ()
setByte (MkBuffer buf _ _) loc val
    = primIO (prim__setByte buf loc val)

%foreign support "idris2_getBufferByte"
prim__getByte : AnyPtr -> Int -> PrimIO Int

export
getByte : Buffer -> (loc : Int) -> IO Int
getByte (MkBuffer buf _ _) loc
    = primIO (prim__getByte buf loc)

%foreign support "idris2_setBufferInt"
prim__setInt : AnyPtr -> Int -> Int -> PrimIO ()

export
setInt : Buffer -> (loc : Int) -> (val : Int) -> IO ()
setInt (MkBuffer buf _ _) loc val
    = primIO (prim__setInt buf loc val)

%foreign support "idris2_getBufferInt"
prim__getInt : AnyPtr -> Int -> PrimIO Int

export
getInt : Buffer -> (loc : Int) -> IO Int
getInt (MkBuffer buf _ _) loc
    = primIO (prim__getInt buf loc)

%foreign support "idris2_setBufferDouble"
prim__setDouble : AnyPtr -> Int -> Double -> PrimIO ()

export
setDouble : Buffer -> (loc : Int) -> (val : Double) -> IO ()
setDouble (MkBuffer buf _ _) loc val
    = primIO (prim__setDouble buf loc val)

%foreign support "idris2_getBufferDouble"
prim__getDouble : AnyPtr -> Int -> PrimIO Double

export
getDouble : Buffer -> (loc : Int) -> IO Double
getDouble (MkBuffer buf _ _) loc
    = primIO (prim__getDouble buf loc)

-- Get the length of a string in bytes, rather than characters
export
%foreign support "strlen"
stringByteLength : String -> Int

%foreign support "idris2_setBufferString"
prim__setString : AnyPtr -> Int -> String -> PrimIO ()

export
setString : Buffer -> (loc : Int) -> (val : String) -> IO ()
setString (MkBuffer buf _ _) loc val
    = primIO (prim__setString buf loc val)

%foreign support "idris2_getBufferString"
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

%foreign support "idris2_copyBuffer"
prim__copyData : AnyPtr -> Int -> Int -> AnyPtr -> Int -> PrimIO ()

export
copyData : (src : Buffer) -> (start, len : Int) ->
           (dest : Buffer) -> (loc : Int) -> IO ()
copyData (MkBuffer src _ _) start len (MkBuffer dest _ _) loc
    = primIO (prim__copyData src start len dest loc)

-- %foreign "scheme:blodwen-readbuffer-bytes"
-- prim__readBufferBytes : FilePtr -> AnyPtr -> Int -> Int -> PrimIO Int
--
-- export
-- readBufferFromFile : BinaryFile -> Buffer -> (maxbytes : Int) ->
--                      IO (Either FileError Buffer)
-- readBufferFromFile (FHandle h) (MkBuffer buf size loc) max
--     = do read <- primIO (prim__readBufferBytes h buf loc max)
--          if read >= 0
--             then pure (Right (MkBuffer buf size (loc + read)))
--             else pure (Left FileReadError)

%foreign support "idris2_readBufferFromFile"
prim__readBufferFromFile : String -> PrimIO AnyPtr

-- Create a new buffer by reading all the contents from the given file
-- Fails if no bytes can be read or buffer can't be created
export
createBufferFromFile : String -> IO (Either FileError Buffer)
createBufferFromFile fn
    = do buf <- primIO (prim__readBufferFromFile fn)
         if prim__nullPtr buf /= 0
            then pure (Left FileReadError)
            else do let sz = prim__bufferSize buf
                    pure (Right (MkBuffer buf sz sz))

%foreign support "idris2_writeBufferToFile"
prim__writeBuffer : String -> AnyPtr -> Int -> PrimIO Int

export
writeBufferToFile : String -> Buffer -> (maxbytes : Int) ->
                    IO (Either FileError ())
writeBufferToFile fn (MkBuffer buf size loc) max
    = do res <- primIO (prim__writeBuffer fn buf max)
         if res == 0
            then pure (Left FileWriteError)
            else pure (Right ())

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
