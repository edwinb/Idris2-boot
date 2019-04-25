module Utils.Binary

import Core.Core
import Core.Name

import Data.Buffer
import public Data.IOArray
import Data.List
import Data.Vect


-- Serialising data as binary. Provides an interface TTC which allows
-- reading and writing to chunks of memory, "Binary", which can be written
-- to and read from files.

%default covering

-- A label for binary states
export 
data Bin : Type where

-- A label for storing resolved name ids
export
data ResID : Type where

-- A component of the serialised data.
record Chunk where
  constructor MkChunk
  buf : Buffer
  loc : Int
  size : Int -- Capacity
  used : Int -- Amount used

newChunk : Buffer -> Chunk
newChunk b = MkChunk b 0 (size b) 0

avail : Chunk -> Int
avail c = size c - loc c

toRead : Chunk -> Int
toRead c = used c - loc c

appended : Int -> Chunk -> Chunk
appended i c = record { loc $= (+i),
                        used $= (+i) } c

incLoc : Int -> Chunk -> Chunk
incLoc i c = record { loc $= (+i) } c

-- Serialised data is stored as a list of chunks, in a zipper.
-- i.e. processed chunks, chunk we're working on, chunks to do
export
data Binary = MkBin (List Chunk) Chunk (List Chunk)

dumpBin : Binary -> IO ()
dumpBin (MkBin done chunk rest)
   = do printLn !(traverse bufferData (map buf done))
        printLn !(bufferData (buf chunk))
        printLn !(traverse bufferData (map buf rest))

nonEmptyRev : NonEmpty (xs ++ y :: ys)
nonEmptyRev {xs = []} = IsNonEmpty
nonEmptyRev {xs = (x :: xs)} = IsNonEmpty

reset : Binary -> Binary
reset (MkBin done cur rest) 
    = setBin (reverse done ++ cur :: rest) nonEmptyRev
  where
    setBin : (xs : List Chunk) -> (prf : NonEmpty xs) -> Binary
    setBin (chunk :: rest) IsNonEmpty 
        = MkBin [] (record { loc = 0 } chunk)
                   (map (record { loc = 0 }) rest)

req : List Chunk -> Int
req [] = 0
req (c :: cs)
    = used c + req cs

-- Take all the data from the chunks in a 'Binary' and copy them into one
-- single buffer, ready for writing to disk.
-- TODO: YAGNI? Delete if so...
toBuffer : Binary -> IO (Maybe Buffer)
toBuffer (MkBin done cur rest)
    = do let chunks = reverse done ++ cur :: rest
         Just b <- newBuffer (req chunks)
              | Nothing => pure Nothing
         copyToBuf 0 b chunks
         pure (Just b)
  where
    copyToBuf : (pos : Int) -> Buffer -> List Chunk -> IO ()
    copyToBuf pos b [] = pure ()
    copyToBuf pos b (c :: cs)
        = do copyData (buf c) 0 (used c) b pos
             copyToBuf (pos + used c) b cs

fromBuffer : Buffer -> IO Binary
fromBuffer buf
    = do len <- rawSize buf
         pure (MkBin [] (MkChunk buf 0 len len) []) -- assume all used

export
writeToFile : (fname : String) -> Binary -> IO (Either FileError ())
writeToFile fname (MkBin done cur rest)
    = do Right h <- openFile fname WriteTruncate
               | Left err => pure (Left err)
         let chunks = reverse done ++ cur :: rest
         writeChunks h chunks
         closeFile h
         pure (Right ())
  where
    writeChunks : File -> List Chunk -> IO ()
    writeChunks h [] = pure ()
    writeChunks h (c :: cs)
        = do writeBufferToFile h (resetBuffer (buf c)) (used c)
             writeChunks h cs

export
readFromFile : (fname : String) -> IO (Either FileError Binary)
readFromFile fname
    = do Right h <- openFile fname Read
               | Left err => pure (Left err)
         Right max <- fileSize h
               | Left err => pure (Left err)
         Just b <- newBuffer max
               | Nothing => pure (Left (GenericFileError 0)) --- um, not really
         b <- readBufferFromFile h b max
         pure (Right (MkBin [] (MkChunk b 0 max max) []))

-- A mapping from the resolved name ids encountered in a TTC file to the
-- name they represent, and (if known) the new resolved id it'll be after
-- reading
-- (We need this because files will be used in different contexts and resolved
-- name ids are not going to be unique, so we need to recalculate them when
-- loading from TTC)
public export
NameRefs : Type
NameRefs = IOArray (Name, Maybe Int)

public export
interface TTC a where -- TTC = TT intermediate code/interface file
  -- Add binary data representing the value to the given buffer
  toBuf : Ref Bin Binary -> a -> Core ()
  -- Return the data representing a thing of type 'a' from the given buffer.
  -- Throws if the data can't be parsed as an 'a'
  fromBuf : NameRefs -> Ref Bin Binary -> Core a

blockSize : Int
blockSize = 655360

-- Create a new list of chunks, initialised with one 64k chunk
export
initBinary : Core (Ref Bin Binary)
initBinary
    = do Just buf <- coreLift $ newBuffer blockSize
             | Nothing => throw (InternalError "Buffer creation failed")
         newRef Bin (MkBin [] (newChunk buf) [])

export
initNameRefs : Int -> Core NameRefs
initNameRefs num 
    = coreLift $ newArray num

export
corrupt : String -> Core a
corrupt ty = throw (TTCError (Corrupt ty))

-- Primitives; these are the only things that have to deal with growing
-- the buffer list

export
TTC Bits8 where
  toBuf b val 
    = do MkBin done chunk rest <- get Bin
         if avail chunk >= 1
            then
              do coreLift $ setByte (buf chunk) (loc chunk) val
                 put Bin (MkBin done (appended 1 chunk) rest)
            else 
              do Just newbuf <- coreLift $ newBuffer blockSize
                    | Nothing => throw (InternalError "Buffer expansion failed")
                 coreLift $ setByte newbuf 0 val
                 put Bin (MkBin (chunk :: done)
                                (MkChunk newbuf 1 (size newbuf) 1)
                                rest)

  fromBuf s b
    = do MkBin done chunk rest <- get Bin
         if toRead chunk >= 1
            then
              do val <- coreLift $ getByte (buf chunk) (loc chunk)
                 put Bin (MkBin done (incLoc 1 chunk) rest)
                 pure val
              else
                case rest of
                     [] => throw (TTCError (EndOfBuffer "Byte"))
                     (next :: rest) =>
                        do val <- coreLift $ getByte (buf next) 0
                           put Bin (MkBin (chunk :: done) (incLoc 1 next) rest)
                           pure val

export
tag : {auto b : Ref Bin Binary} -> Bits8 -> Core ()
tag {b} val = toBuf b val

export
getTag : {auto r : NameRefs} ->
         {auto b : Ref Bin Binary} -> Core Bits8
getTag {r} {b} = fromBuf r b

-- Some useful types from the prelude

export
TTC Int where
  toBuf b val
    = do MkBin done chunk rest <- get Bin
         if avail chunk >= 4
            then 
              do coreLift $ setInt (buf chunk) (loc chunk) val
                 put Bin (MkBin done (appended 4 chunk) rest)
            else 
              do Just newbuf <- coreLift $ newBuffer blockSize
                    | Nothing => throw (InternalError "Buffer expansion failed")
                 coreLift $ setInt newbuf 0 val
                 put Bin (MkBin (chunk :: done)
                                (MkChunk newbuf 4 (size newbuf) 4)
                                rest)
  fromBuf r b 
    = do MkBin done chunk rest <- get Bin
         if toRead chunk >= 4
            then
              do val <- coreLift $ getInt (buf chunk) (loc chunk)
                 put Bin (MkBin done (incLoc 4 chunk) rest)
                 pure val
              else
                case rest of
                     [] => throw (TTCError (EndOfBuffer "Int"))
                     (next :: rest) =>
                        do val <- coreLift $ getInt (buf next) 0
                           put Bin (MkBin (chunk :: done) (incLoc 4 next) rest)
                           pure val

export
TTC String where
  toBuf b val
      = do let req : Int = cast (length val)
           toBuf b req
           MkBin done chunk rest <- get Bin
           if avail chunk >= req
              then
                do coreLift $ setString (buf chunk) (loc chunk) val
                   put Bin (MkBin done (appended req chunk) rest)
              else 
                do Just newbuf <- coreLift $ newBuffer blockSize
                      | Nothing => throw (InternalError "Buffer expansion failed")
                   coreLift $ setString newbuf 0 val
                   put Bin (MkBin (chunk :: done)
                                  (MkChunk newbuf req (size newbuf) req)
                                  rest)

  fromBuf r b 
      = do len <- fromBuf {a = Int} r b
           MkBin done chunk rest <- get Bin
           if toRead chunk >= len
              then
                do val <- coreLift $ getString (buf chunk) (loc chunk) len
                   put Bin (MkBin done (incLoc len chunk) rest)
                   pure val
              else 
                case rest of
                     [] => throw (TTCError (EndOfBuffer "String"))
                     (next :: rest) =>
                        do val <- coreLift $ getString (buf next) 0 len
                           put Bin (MkBin (chunk :: done)
                                          (incLoc len next) rest)
                           pure val

export
TTC Bool where
  toBuf b False = tag 0
  toBuf b True = tag 1
  fromBuf r b
      = case !getTag of
             0 => pure False
             1 => pure True
             _ => corrupt "Bool"

export
TTC Char where
  toBuf b c = toBuf b (cast {to=Int} c)
  fromBuf r b
      = do i <- fromBuf r b
           pure (cast {from=Int} i)

export
TTC Double where
  toBuf b val
    = do MkBin done chunk rest <- get Bin
         if avail chunk >= 8
            then 
              do coreLift $ setDouble (buf chunk) (loc chunk) val
                 put Bin (MkBin done (appended 8 chunk) rest)
            else 
              do Just newbuf <- coreLift $ newBuffer blockSize
                    | Nothing => throw (InternalError "Buffer expansion failed")
                 coreLift $ setDouble newbuf 0 val
                 put Bin (MkBin (chunk :: done)
                                (MkChunk newbuf 8 (size newbuf) 8)
                                rest)
  fromBuf r b 
    = do MkBin done chunk rest <- get Bin
         if toRead chunk >= 8
            then
              do val <- coreLift $ getDouble (buf chunk) (loc chunk)
                 put Bin (MkBin done (incLoc 8 chunk) rest)
                 pure val
              else
                case rest of
                     [] => throw (TTCError (EndOfBuffer "Double"))
                     (next :: rest) =>
                        do val <- coreLift $ getDouble (buf next) 0
                           put Bin (MkBin (chunk :: done) (incLoc 8 next) rest)
                           pure val

export
(TTC a, TTC b) => TTC (a, b) where
  toBuf b (x, y)
     = do toBuf b x
          toBuf b y
  fromBuf r b
     = do x <- fromBuf r b
          y <- fromBuf r b
          pure (x, y)

export
TTC () where
  toBuf b () = pure ()
  fromBuf r b = pure ()

export
(TTC a, {y : a} -> TTC (p y)) => TTC (DPair a p) where
  toBuf b (vs ** tm)
      = do toBuf b vs
           toBuf b tm

  fromBuf r b
      = do x <- fromBuf r b
           p <- fromBuf r b
           pure (x ** p)

export
TTC a => TTC (Maybe a) where
  toBuf b Nothing
     = tag 0
  toBuf b (Just val)
     = do tag 1
          toBuf b val

  fromBuf r b
     = case !getTag of
            0 => pure Nothing
            1 => do val <- fromBuf r b
                    pure (Just val)
            _ => corrupt "Maybe"

export
(TTC a, TTC b) => TTC (Either a b) where
  toBuf b (Left val)
     = do tag 0
          toBuf b val
  toBuf b (Right val)
     = do tag 1
          toBuf b val

  fromBuf r b
     = case !getTag of
            0 => do val <- fromBuf r b
                    pure (Left val)
            1 => do val <- fromBuf r b
                    pure (Right val)
            _ => corrupt "Either"

export
TTC a => TTC (List a) where
  toBuf b xs
      = do toBuf b (cast {to=Int} (length xs))
           traverse (toBuf b) xs
           pure ()
  fromBuf r b 
      = do len <- fromBuf r b {a = Int}
           readElems [] (cast len)
    where
      readElems : List a -> Nat -> Core (List a)
      readElems xs Z = pure (reverse xs)
      readElems xs (S k)
          = do val <- fromBuf r b
               readElems (val :: xs) k

export
TTC a => TTC (Vect n a) where
  toBuf b xs = writeAll xs
    where
      writeAll : Vect n a -> Core ()
      writeAll [] = pure ()
      writeAll (x :: xs) = do toBuf b x; writeAll xs

  fromBuf {n} r b = rewrite sym (plusZeroRightNeutral n) in readElems [] n
    where
      readElems : Vect done a -> (todo : Nat) -> Core (Vect (todo + done) a)
      readElems {done} xs Z 
          = pure (reverse xs)
      readElems {done} xs (S k)
          = do val <- fromBuf r b
               rewrite (plusSuccRightSucc k done)
               readElems (val :: xs) k

count : List.Elem x xs -> Int
count Here = 0
count (There p) = 1 + count p

toLimbs : Integer -> List Int
toLimbs x
    = if x == 0 
         then []
         else if x == -1 then [-1]
              else fromInteger (prim__andBigInt x 0xffffffff) ::
                    toLimbs (prim__ashrBigInt x 32)

fromLimbs : List Int -> Integer
fromLimbs [] = 0
fromLimbs (x :: xs) = cast x + prim__shlBigInt (fromLimbs xs) 32

export
TTC Integer where
  toBuf b val
    = assert_total $ if val < 0
         then do toBuf b (the Bits8 0)
                 toBuf b (toLimbs (-val))
         else do toBuf b (the Bits8 1)
                 toBuf b (toLimbs val)
  fromBuf r b 
    = do val <- fromBuf r b {a = Bits8}
         case val of
              0 => do val <- fromBuf r b
                      pure (-(fromLimbs val))
              1 => do val <- fromBuf r b
                      pure (fromLimbs val)
              _ => corrupt "Integer"

export
TTC Nat where
  toBuf b val = toBuf b (cast {to=Integer} val)
  fromBuf r b 
     = do val <- fromBuf r b
          pure (fromInteger val)
