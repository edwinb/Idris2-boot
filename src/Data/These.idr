module Data.These

%access public export
%default total

data These a b = This a | That b | Both a b

fromEither : Either a b -> These a b
fromEither = either This That

these : (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
these l r lr (This a)   = l a
these l r lr (That b)   = r b
these l r lr (Both a b) = lr a b

bimap : (f : a -> b) -> (g : c -> d) -> These a c -> These b d
bimap f g (This a)   = This (f a)
bimap f g (That b)   = That (g b)
bimap f g (Both a b) = Both (f a) (g b)

(Show a, Show b) => Show (These a b) where
  showPrec d (This x)   = showCon d "This" $ showArg x
  showPrec d (That x)   = showCon d "That" $ showArg x
  showPrec d (Both x y) = showCon d "Both" $ showArg x ++ showArg y

Functor (These a) where
  map = bimap id

mapFst : (f : a -> b) -> These a c -> These b c
mapFst f = bimap f id

bifold : Monoid m => These m m -> m
bifold (This a)   = a
bifold (That b)   = b
bifold (Both a b) = a <+> b

bitraverse : Applicative f => (a -> f c) -> (b -> f d) -> These a b -> f (These c d)
bitraverse f g (This a)   = [| This (f a) |]
bitraverse f g (That b)   = [| That (g b) |]
bitraverse f g (Both a b) = [| Both (f a) (g b) |]
