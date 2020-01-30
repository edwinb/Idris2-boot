module Data.Buffer

import System.File

export
data Buffer : Type where
     MkBuffer : AnyPtr -> (size : Int) -> (loc : Int) -> Buffer

export
newBuffer : Int -> IO Buffer
newBuffer size
    = do buf <- schemeCall AnyPtr "blodwen-new-buffer" [size]
         pure (MkBuffer buf size 0)

export
resetBuffer : Buffer -> Buffer
resetBuffer (MkBuffer ptr s l) = MkBuffer ptr s 0

export
rawSize : Buffer -> IO Int
rawSize (MkBuffer buf _ _)
    = schemeCall Int "blodwen-buffer-size" [buf]

export
size : Buffer -> Int
size (MkBuffer _ s _) = s

-- Assumes val is in the range 0-255
export
setByte : Buffer -> (loc : Int) -> (val : Int) -> IO ()
setByte (MkBuffer buf _ _) loc val
    = schemeCall () "blodwen-buffer-setbyte" [buf, loc, val]

export
getByte : Buffer -> (loc : Int) -> IO Int
getByte (MkBuffer buf _ _) loc
    = schemeCall Int "blodwen-buffer-getbyte" [buf, loc]

export
setInt : Buffer -> (loc : Int) -> (val : Int) -> IO ()
setInt (MkBuffer buf _ _) loc val
    = schemeCall () "blodwen-buffer-setint" [buf, loc, val]

export
getInt : Buffer -> (loc : Int) -> IO Int
getInt (MkBuffer buf _ _) loc
    = schemeCall Int "blodwen-buffer-getint" [buf, loc]

export
setDouble : Buffer -> (loc : Int) -> (val : Double) -> IO ()
setDouble (MkBuffer buf _ _) loc val
    = schemeCall () "blodwen-buffer-setdouble" [buf, loc, val]

export
getDouble : Buffer -> (loc : Int) -> IO Double
getDouble (MkBuffer buf _ _) loc
    = schemeCall Double "blodwen-buffer-getdouble" [buf, loc]

-- Get the length of a string in bytes, rather than characters
export
%foreign "scheme:blodwen-stringbytelen"
stringByteLength : String -> Int

export
setString : Buffer -> (loc : Int) -> (val : String) -> IO ()
setString (MkBuffer buf _ _) loc val
    = schemeCall () "blodwen-buffer-setstring" [buf, loc, val]

export
getString : Buffer -> (loc : Int) -> (len : Int) -> IO String
getString (MkBuffer buf _ _) loc len
    = schemeCall String "blodwen-buffer-getstring" [buf, loc, len]

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

export
copyData : (src : Buffer) -> (start, len : Int) ->
           (dest : Buffer) -> (loc : Int) -> IO ()
copyData (MkBuffer src _ _) start len (MkBuffer dest _ _) loc
    = schemeCall () "blodwen-buffer-copydata" [src,start,len,dest,loc]

export
readBufferFromFile : BinaryFile -> Buffer -> (maxbytes : Int) ->
                     IO (Either FileError Buffer)
readBufferFromFile (FHandle h) (MkBuffer buf size loc) max
    = do read <- schemeCall Int "blodwen-readbuffer" [h, buf, loc, max]
         if read >= 0
            then pure (Right (MkBuffer buf size (loc + read)))
            else pure (Left FileReadError)

export
writeBufferToFile : BinaryFile -> Buffer -> (maxbytes : Int) ->
                    IO (Either FileError Buffer)
writeBufferToFile (FHandle h) (MkBuffer buf size loc) max
    = do let maxwrite = size - loc
         let max' = if maxwrite < max then maxwrite else max
         written <- schemeCall Int "blodwen-writebuffer" [h, buf, loc, max']
         if written == max'
            then pure (Right (MkBuffer buf size (loc + max')))
            else pure (Left FileWriteError)
