||| Utilities functions for contitionally delaying values.
module Control.Delayed

%default total

||| Type-level function for a conditionally delayed type (`Lazy` or `Inf`).
public export
delayed : DelayReason -> Bool -> Type -> Type
delayed r False a = a
delayed r True a = Delayed r a

||| Type-level function for a conditionally infinite type.
public export
inf : Bool -> Type -> Type
inf = delayed Infinite

||| Type-level function for a conditionally lazy type.
public export
lazy : Bool -> Type -> Type
lazy = delayed LazyValue

||| Conditionally delay a value.
export
delay : {r : DelayReason} -> (d : Bool) -> a -> delayed r d a
delay False x = x
delay {r=Infinite}  True x = Delay x
delay {r=LazyValue} True x = Delay x
