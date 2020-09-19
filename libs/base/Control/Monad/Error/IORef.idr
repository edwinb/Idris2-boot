module Control.Monad.Error.IORef
import Control.Monad.Error
import Data.IORef

public export
overIORef : IORef a -> ( a -> IOError e a ) -> IOError e a
overIORef ref xform = do
    val <- lift( readIORef ref )
    newval <- xform val
    lift( writeIORef ref newval )
    pure newval
