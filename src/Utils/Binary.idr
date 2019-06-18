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

export
record Binary where
  constructor MkBin
  buf : Buffer
  loc : Int
  size : Int -- Capacity
  used : Int -- Amount used

newBinary : Buffer -> Binary
newBinary b = MkBin b 0 (size b) 0

blockSize : Int
blockSize = 655360

avail : Binary -> Int
avail c = (size c - loc c) - 1

toRead : Binary -> Int
toRead c = used c - loc c 

appended : Int -> Binary -> Binary
appended i (MkBin b loc s used) = MkBin b (loc+i) s (used + i)

incLoc : Int -> Binary -> Binary
incLoc i c = record { loc $= (+i) } c

dumpBin : Binary -> IO ()
dumpBin chunk
   = do -- printLn !(traverse bufferData (map buf done))
        printLn !(bufferData (buf chunk))
        -- printLn !(traverse bufferData (map buf rest))

nonEmptyRev : NonEmpty (xs ++ y :: ys)
nonEmptyRev {xs = []} = IsNonEmpty
nonEmptyRev {xs = (x :: xs)} = IsNonEmpty

fromBuffer : Buffer -> IO Binary
fromBuffer buf
    = do len <- rawSize buf
         pure (MkBin buf 0 len len)

export
writeToFile : (fname : String) -> Binary -> IO (Either FileError ())
writeToFile fname c
    = do Right h <- openFile fname WriteTruncate
               | Left err => pure (Left err)
         writeBufferToFile h (resetBuffer (buf c)) (used c)
         closeFile h
         pure (Right ())

export
readFromFile : (fname : String) -> IO (Either FileError Binary)
readFromFile fname
    = do Right h <- openFile fname Read
               | Left err => pure (Left err)
         Right fsize <- fileSize h
               | Left err => pure (Left err)
         Just b <- newBuffer fsize
               | Nothing => pure (Left (GenericFileError 0)) --- um, not really
         b <- readBufferFromFile h b fsize
         pure (Right (MkBin b 0 fsize fsize))

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

-- Create a new list of chunks, initialised with one 64k chunk
export
initBinary : Core (Ref Bin Binary)
initBinary
    = do Just buf <- coreLift $ newBuffer blockSize
             | Nothing => throw (InternalError "Buffer creation failed")
         newRef Bin (newBinary buf)

extendBinary : Binary -> Core Binary
extendBinary (MkBin buf l s u)
    = do let s' = s + blockSize
         Just buf' <- coreLift $ resizeBuffer buf s'
             | Nothing => throw (InternalError "Buffer expansion failed")
         pure (MkBin buf' l s' u)


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
    = do chunk <- get Bin
         if avail chunk >= 1
            then
              do coreLift $ setByte (buf chunk) (loc chunk) val
                 put Bin (appended 1 chunk)
            else do chunk' <- extendBinary chunk
                    coreLift $ setByte (buf chunk') (loc chunk') val
                    put Bin (appended 1 chunk')

  fromBuf s b
    = do chunk <- get Bin
         if toRead chunk >= 1
            then
              do val <- coreLift $ getByte (buf chunk) (loc chunk)
                 put Bin (incLoc 1 chunk)
                 pure val
              else throw (TTCError (EndOfBuffer "Byte"))

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
    = do chunk <- get Bin
         if avail chunk >= 4
            then 
              do coreLift $ setInt (buf chunk) (loc chunk) val
                 put Bin (appended 4 chunk)
            else do chunk' <- extendBinary chunk
                    coreLift $ setInt (buf chunk') (loc chunk') val
                    put Bin (appended 4 chunk')

  fromBuf r b 
    = do chunk <- get Bin
         if toRead chunk >= 4
            then
              do val <- coreLift $ getInt (buf chunk) (loc chunk)
                 put Bin (incLoc 4 chunk)
                 pure val
              else throw (TTCError (EndOfBuffer ("Int " ++ show (loc chunk, size chunk))))

export
TTC String where
  toBuf b val
      = do let req : Int = cast (length val)
           toBuf b req
           chunk <- get Bin
           if avail chunk >= req
              then
                do coreLift $ setString (buf chunk) (loc chunk) val
                   put Bin (appended req chunk)
              else do chunk' <- extendBinary chunk
                      coreLift $ setString (buf chunk') (loc chunk') val
                      put Bin (appended req chunk')

  fromBuf r b 
      = do len <- fromBuf {a = Int} r b
           chunk <- get Bin
           if toRead chunk >= len
              then
                do val <- coreLift $ getString (buf chunk) (loc chunk) len
                   put Bin (incLoc len chunk)
                   pure val
              else throw (TTCError (EndOfBuffer "String"))

export
TTC Binary where
  toBuf b val
    = do toBuf b (used val)
         chunk <- get Bin
         if avail chunk >= used val
            then
              do coreLift $ copyData (buf val) 0 (used val)
                                     (buf chunk) (loc chunk)
                 put Bin (appended (used val) chunk)
            else do chunk' <- extendBinary chunk
                    coreLift $ copyData (buf val) 0 (used val)
                                        (buf chunk) (loc chunk)
                    put Bin (appended (used val) chunk)

  fromBuf s b
    = do len <- fromBuf s b
         chunk <- get Bin
         if toRead chunk >= len
            then
              do Just newbuf <- coreLift $ newBuffer len
                      | Nothing => throw (InternalError "Can't create buffer")
                 coreLift $ copyData (buf chunk) (loc chunk) len
                                     newbuf 0
                 pure (MkBin newbuf 0 len len)
            else throw (TTCError (EndOfBuffer "Binary"))

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
    = do chunk <- get Bin
         if avail chunk >= 8
            then 
              do coreLift $ setDouble (buf chunk) (loc chunk) val
                 put Bin (appended 8 chunk)
            else do chunk' <- extendBinary chunk
                    coreLift $ setDouble (buf chunk') (loc chunk') val
                    put Bin (appended 8 chunk')

  fromBuf r b 
    = do chunk <- get Bin
         if toRead chunk >= 8
            then
              do val <- coreLift $ getDouble (buf chunk) (loc chunk)
                 put Bin (incLoc 8 chunk)
                 pure val
              else throw (TTCError (EndOfBuffer "Double"))

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
           traverse_ (toBuf b) xs
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
