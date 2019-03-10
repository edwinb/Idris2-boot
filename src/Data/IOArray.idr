module Data.IOArray

%default total

-- Raw access to IOArrays. This interface is unsafe because there's no
-- bounds checking, and is merely intended to provide primitive access via
-- the RTS. Safe interfaces (either with run time or compile time
-- bounds checking) can be implemented on top of this

-- Implemented entirely by the array primitives in the RTS
data ArrayData : Type -> Type where

export
data IORawArray elem = MkIORawArray (ArrayData elem)

||| Create a new array of the given size, with all entries set to the
||| given default element.
export
newRawArray : Int -> elem -> IO (IORawArray elem)
newRawArray size default
    = do vm <- getMyVM
         MkRaw p <- foreign FFI_C "idris_newArray"
                          (Ptr -> Int -> Raw elem -> IO (Raw (ArrayData elem)))
                          vm size (MkRaw default)
         pure (MkIORawArray p)

||| Write an element at a location in an array. 
||| There is *no* bounds checking, hence this is unsafe. Safe interfaces can
||| be implemented on top of this, either with a run time or compile time
||| check.
export
unsafeWriteArray : IORawArray elem -> Int -> elem -> IO ()
unsafeWriteArray (MkIORawArray p) i val
    = foreign FFI_C "idris_arraySet"
                    (Raw (ArrayData elem) -> Int -> Raw elem -> IO ())
                    (MkRaw p) i (MkRaw val)

||| Read the element at a location in an array. 
||| There is *no* bounds checking, hence this is unsafe. Safe interfaces can
||| be implemented on top of this, either with a run time or compile time
||| check.
export
unsafeReadArray : IORawArray elem -> Int -> IO elem
unsafeReadArray (MkIORawArray p) i
    = do MkRaw val <- foreign FFI_C "idris_arrayGet"
                              (Raw (ArrayData elem) -> Int -> IO (Raw elem))
                              (MkRaw p) i
         pure val

-- As IORawArray, but wrapped in dynamic checks that elements exist and
-- are in bounds
public export
record IOArray elem where
  constructor MkIOArray
  max : Int
  content : IORawArray (Maybe elem)

export
newArray : Int -> IO (IOArray elem)
newArray size
    = pure (MkIOArray size !(newRawArray size Nothing))

export
writeArray : IOArray elem -> Int -> elem -> IO ()
writeArray arr pos el
    = if pos < 0 || pos >= max arr
         then pure ()
         else unsafeWriteArray (content arr) pos (Just el)

export
readArray : IOArray elem -> Int -> IO (Maybe elem)
readArray arr pos
    = if pos < 0 || pos >= max arr
         then pure Nothing
         else unsafeReadArray (content arr) pos

-- Make a new array of the given size with the elements copied from the
-- other array
export
newArrayCopy : (newsize : Int) -> IOArray elem -> IO (IOArray elem)
newArrayCopy newsize arr
    = do let newsize' = if newsize < max arr then max arr else newsize
         arr' <- newArray newsize'
         copyFrom (content arr) (content arr') (max arr - 1)
         pure arr'
  where
    copyFrom : IORawArray (Maybe elem) ->
               IORawArray (Maybe elem) ->
               Int -> IO ()
    copyFrom old new pos
        = if pos < 0
             then pure ()
             else do el <- unsafeReadArray old pos
                     unsafeWriteArray new pos el
                     assert_total (copyFrom old new (pos - 1))

