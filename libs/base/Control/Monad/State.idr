module Control.Monad.State

import public Control.Monad.Identity
import public Control.Monad.Trans

||| A computation which runs in a context and produces an output
public export
interface Monad m => MonadState stateType (m : Type -> Type) | m where
    ||| Get the context
    get : m stateType
    ||| Write a new context/output
    put : stateType -> m ()

||| The transformer on which the State monad is based
public export
record StateT (stateType : Type) (m : Type -> Type) (a : Type) where
  constructor ST
  runStateT : stateType -> m (a, stateType)

public export
implementation Functor f => Functor (StateT stateType f) where
    map f (ST g) = ST (\st => map (mapFst f) (g st)) where
       mapFst : (a -> x) -> (a, s) -> (x, s)
       mapFst fn (a, b) = (fn a, b)

public export
implementation Monad f => Applicative (StateT stateType f) where
    pure x = ST (\st => pure (x, st))

    (ST f) <*> (ST a)
        = ST (\st =>
                do (g, r) <- f st
                   (b, t) <- a r
                   pure (g b, t))

public export
implementation Monad m => Monad (StateT stateType m) where
    (ST f) >>= k
        = ST (\st =>
                do (v, st') <- f st
                   let ST kv = k v
                   kv st')

public export
implementation Monad m => MonadState stateType (StateT stateType m) where
    get   = ST (\x => pure (x, x))
    put x = ST (\y => pure ((), x))

public export
implementation MonadTrans (StateT stateType) where
    lift x
        = ST (\st =>
                do r <- x
                   pure (r, st))

public export
implementation (Monad f, Alternative f) => Alternative (StateT st f) where
    empty = lift empty
    (ST f) <|> (ST g) = ST (\st => f st <|> g st)

||| Apply a function to modify the context of this computation
public export
modify : MonadState stateType m => (stateType -> stateType) -> m ()
modify f
    = do s <- get
         put (f s)

||| Evaluate a function in the context held by this computation
public export
gets : MonadState stateType m => (stateType -> a) -> m a
gets f
    = do s <- get
         pure (f s)

||| The State monad. See the MonadState interface
public export
State : (stateType : Type) -> (ty : Type) -> Type
State = \s, a => StateT s Identity a

||| Unwrap a State monad computation.
public export
runState : StateT stateType Identity a -> stateType -> (a, stateType)
runState act = runIdentity . runStateT act

||| Unwrap a State monad computation, but discard the final state.
public export
evalState : State stateType a -> stateType -> a
evalState m = fst . runState m

||| Unwrap a State monad computation, but discard the resulting value.
public export
execState : State stateType a -> stateType -> stateType
execState m = snd . runState m
