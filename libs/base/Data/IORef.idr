module Data.IORef

-- Implemented externally
-- e.g., in Scheme, passed around as a box
data Mut : Type -> Type where [external]

%extern prim__newIORef : forall a . a -> (1 x : %World) -> IORes (Mut a)
%extern prim__readIORef : forall a . Mut a -> (1 x : %World) -> IORes a
%extern prim__writeIORef : forall a . Mut a -> (1 val : a) -> (1 x : %World) -> IORes ()

export
data IORef : Type -> Type where
     MkRef : Mut a -> IORef a

export
newIORef : a -> IO (IORef a)
newIORef val
    = do m <- primIO (prim__newIORef val)
         pure (MkRef m)

export
readIORef : IORef a -> IO a
readIORef (MkRef m) = primIO (prim__readIORef m)

export
writeIORef : IORef a -> (1 val : a) -> IO ()
writeIORef (MkRef m) val = primIO (prim__writeIORef m val)

export
modifyIORef : IORef a -> (a -> a) -> IO ()
modifyIORef ref f
    = do val <- readIORef ref
         writeIORef ref (f val)

