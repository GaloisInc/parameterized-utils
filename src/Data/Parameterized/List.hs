{-|
Copyright        : (c) Galois, Inc 2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This module defines a list over two parameters.  The first
is a fixed type-level function @k -> *@ for some kind @k@, and the
second is a list of types with kind k that provide the indices for
the values in the list.

This type is closely related to the @Context@ type in
@Data.Parameterized.Context@.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Data.Parameterized.List
  ( List(..)
  , Index(..)
  , indexValue
  , (!!)
  , update
  , indexed
  , imap
  , ifoldr
  , itraverse
    -- * Constants
  , index0
  , index1
  , index2
  , index3
  ) where

import qualified Control.Lens as Lens
import Prelude hiding ((!!))

import Data.Parameterized.Classes
import Data.Parameterized.TraversableFC

-- | Parameterized list of elements.
data List :: (k -> *) -> [k] -> * where
  Nil  :: List f '[]
  (:>) :: f tp -> List f tps -> List f (tp : tps)

infixr 5 :>

instance ShowF f => Show (List f sh) where
  show Nil = "Nil"
  show (elt :> rest) = showF elt ++ " :> " ++ show rest

instance ShowF f => ShowF (List f)

instance FunctorFC List where
  fmapFC _ Nil = Nil
  fmapFC f (x :> xs) = f x :> fmapFC f xs

instance FoldableFC List where
  foldrFC _ z Nil = z
  foldrFC f z (x :> xs) = f x (foldrFC f z xs)

instance TraversableFC List where
  traverseFC _ Nil = pure Nil
  traverseFC f (h :> r) = (:>) <$> f h <*> traverseFC f r

instance TestEquality f => TestEquality (List f) where
  testEquality Nil Nil = Just Refl
  testEquality (xh :> xl) (yh :> yl) = do
    Refl <- testEquality xh yh
    Refl <- testEquality xl yl
    pure Refl
  testEquality _ _ = Nothing

instance OrdF f => OrdF (List f) where
  compareF Nil Nil = EQF
  compareF Nil _ = LTF
  compareF _ Nil = GTF
  compareF (xh :> xl) (yh :> yl) =
    lexCompareF xh yh $
    lexCompareF xl yl $
    EQF


instance KnownRepr (List f) '[] where
  knownRepr = Nil

instance (KnownRepr f s, KnownRepr (List f) sh) => KnownRepr (List f) (s ': sh) where
  knownRepr = knownRepr :> knownRepr

--------------------------------------------------------------------------------
-- Indexed operations


-- | Represents an index into a type-level list. Used in place of integers to
--   1. ensure that the given index *does* exist in the list
--   2. guarantee that it has the given kind
data Index :: [k] -> k -> *  where
  IndexHere :: Index (x:r) x
  IndexThere :: !(Index r y) -> Index (x:r) y

deriving instance Eq (Index l x)
deriving instance Show  (Index l x)

instance TestEquality (Index l) where
  testEquality IndexHere IndexHere = Just Refl
  testEquality (IndexThere x) (IndexThere y) = testEquality x y
  testEquality _ _ = Nothing

instance OrdF (Index l) where
  compareF IndexHere IndexHere = EQF
  compareF IndexHere IndexThere{} = LTF
  compareF IndexThere{} IndexHere = GTF
  compareF (IndexThere x) (IndexThere y) = compareF x y

instance Ord (Index sh x) where
  x `compare` y = toOrdering $ x `compareF` y

-- | Return the index as an integer.
indexValue :: Index l tp -> Integer
indexValue = go 0
  where go :: Integer -> Index l tp -> Integer
        go i IndexHere = i
        go i (IndexThere x) = seq j $ go j x
          where j = i+1

-- | Index 0
index0 :: Index (x:r) x
index0 = IndexHere

-- | Index 1
index1 :: Index (x0:x1:r) x1
index1 = IndexThere index0

-- | Index 2
index2 :: Index (x0:x1:x2:r) x2
index2 = IndexThere index1

-- | Index 3
index3 :: Index (x0:x1:x2:x3:r) x3
index3 = IndexThere index2

-- | Return the value in a list at a given index
(!!) :: List f l -> Index l x -> f x
l !! (IndexThere i) =
  case l of
    _ :> r -> r !! i
l !! IndexHere =
  case l of
    (h :> _) -> h

-- | Update the 'List' at an index
update :: List f l -> Index l s -> (f s -> f s) -> List f l
update vals IndexHere upd =
  case vals of
    x :> rest -> upd x :> rest
update vals (IndexThere th) upd =
  case vals of
    x :> rest -> x :> update rest th upd

-- | Provides a lens for manipulating the element at the given index.
indexed :: Index l x -> Lens.Simple Lens.Lens (List f l) (f x)
indexed IndexHere      f (x :> rest) = (:> rest) <$> f x
indexed (IndexThere i) f (x :> rest) = (x :>) <$> indexed i f rest

--------------------------------------------------------------------------------
-- Indexed operations

-- | Map over the elements in the list, and provide the index into
-- each element along with the element itself.
imap :: forall f g l
     . (forall x . Index l x -> f x -> g x)
     -> List f l
     -> List g l
imap f = go id
  where
    go :: forall l'
        . (forall tp . Index l' tp -> Index l tp)
       -> List f l'
       -> List g l'
    go g l =
      case l of
        Nil -> Nil
        e :> rest -> f (g IndexHere) e :> go (g . IndexThere) rest

-- | Right-fold with an additional index.
ifoldr :: forall sh a b . (forall tp . Index sh tp -> a tp -> b -> b) -> b -> List a sh -> b
ifoldr f seed0 l = go id l seed0
  where
    go :: forall tps
        . (forall tp . Index tps tp -> Index sh tp)
       -> List a tps
       -> b
       -> b
    go g ops b =
      case ops of
        Nil -> b
        a :> rest -> f (g IndexHere) a (go (\ix -> g (IndexThere ix)) rest b)

-- | Traverse with an additional index.
itraverse :: forall a b sh t
          . Applicative t
          => (forall tp . Index sh tp -> a tp -> t (b tp))
          -> List a sh
          -> t (List b sh)
itraverse f = go id
  where
    go :: forall tps . (forall tp . Index tps tp -> Index sh tp)
       -> List a tps
       -> t (List b tps)
    go g l =
      case l of
        Nil -> pure Nil
        e :> rest -> (:>) <$> f (g IndexHere) e <*> go (\ix -> g (IndexThere ix)) rest
