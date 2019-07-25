module Data.StringTrie

import Data.These
import Data.StringMap

%access public export
%default total

-- prefix tree specialised to use `String`s as keys

record StringTrie a where
  constructor MkStringTrie
  node : These a (StringMap (StringTrie a))
  
Functor StringTrie where 
  map f (MkStringTrie node) = MkStringTrie $ assert_total $ bimap f (map (map f)) node

empty : StringTrie a 
empty = MkStringTrie $ That empty

singleton : List String -> a -> StringTrie a
singleton []      v = MkStringTrie $ This v
singleton (k::ks) v = MkStringTrie $ That $ singleton k (singleton ks v)

-- insert using supplied function to resolve clashes
insertWith : List String -> (Maybe a -> a) -> StringTrie a -> StringTrie a
insertWith []      f (MkStringTrie nd) = 
  MkStringTrie $ these (This . f . Just) (Both (f Nothing)) (Both . f . Just) nd
insertWith (k::ks) f (MkStringTrie nd) = 
  MkStringTrie $ these (\x => Both x (singleton k end)) (That . rec) (\x => Both x . rec) nd
  where
  end : StringTrie a
  end = singleton ks (f Nothing)
  rec : StringMap (StringTrie a) -> StringMap (StringTrie a)
  rec sm = maybe (insert k end sm) (\tm => insert k (insertWith ks f tm) sm) (lookup k sm) 

insert : List String -> a -> StringTrie a -> StringTrie a
insert ks v = insertWith ks (const v)

-- fold the trie in a depth-first fashion performing monadic actions on values, then keys  
foldWithKeysM : (Monad m, Monoid b) => (List String -> m b) -> (List String -> a -> m b) -> StringTrie a -> m b
foldWithKeysM {a} {m} {b} fk fv = go [] 
  where 
  go : List String -> StringTrie a -> m b
  go as (MkStringTrie nd) = 
    bifold <$> bitraverse 
                (fv as) 
                (\sm => foldlM 
                          (\x, (k, vs) => do let as' = as ++ [k]
                                             y <- assert_total $ go as' vs
                                             z <- fk as'
                                             pure $ x <+> y <+> z)
                          neutral 
                          (toList sm)) 
                nd 
