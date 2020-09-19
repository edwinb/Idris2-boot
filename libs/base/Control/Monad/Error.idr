module Control.Monad.Error
import Control.Monad.Trans

public export
interface Monad m => MonadError e m where
    throw : e -> m a
    catch : m a -> ( e -> m a ) -> m a

public export
data ErrorT : Type -> ( Type -> Type ) -> Type -> Type where
    RunErrorT : m ( Either e a ) -> ErrorT e m a

public export
IOError : Type -> Type -> Type
IOError e a = ErrorT e IO a

public export
Functor m => Functor( ErrorT e m ) where
    map f ( RunErrorT op ) = RunErrorT( map ( map f ) op )

public export
Monad m => Applicative( ErrorT e m ) where
    pure x = RunErrorT( pure ( Right x ) )
    RunErrorT f <*> RunErrorT op = RunErrorT $
        op >>= \ e_val => map ( <*> e_val ) f

public export
Monad m => Monad( ErrorT e m ) where
    RunErrorT op >>= f = RunErrorT $ op >>= \ e_val =>
        case e_val of
            Left  err => pure( Left err )
            Right val => let RunErrorT op = f val in op

public export
Monad m => MonadError e ( ErrorT e m ) where
    throw = RunErrorT . pure . Left
    catch( RunErrorT op ) handler = RunErrorT $ op >>= \ e_val => case e_val of
        Left  err => let RunErrorT op' = handler err in op'
        Right val => pure( Right val )

public export
MonadTrans( ErrorT e ) where
--  lift : Monad m => m a -> ErrorT e m a
    lift op = RunErrorT( map Right op )

throwIf : MonadError e m => Bool -> Lazy e -> m ()
throwIf test err = if test
    then throw err
    else pure ()
