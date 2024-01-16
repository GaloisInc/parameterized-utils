{-|
Module           : Data.Parameterized.Context.Elective
Copyright        : (c) Galois, Inc 2024
Maintainer       : Ryan Scott <rscott@galois.com>

Provides the 'Elective' type, which picks one element from a 'Ctx'.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Parameterized.Context.Elective
  ( Elective(..)
  , elective
  , ielective
  , elect
  , isElective
  , fromElective
  , partitionElectives
  , electiveIndex
  , electiveElement
  ) where

import Control.Lens (over)
import Data.Functor.Compose (Compose(..))
import Data.Kind (Type)

import Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx (replicate)
import Data.Parameterized.Context hiding (replicate)
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC
import Data.Parameterized.TraversableFC.WithIndex

-- | An @'Elective' f ctx@ value chooses one particular element whose type
-- @f tp@ (for some @tp@) belongs to the @ctx@. The element also comes equipped
-- with an @'Index' ctx tp@ value, which allows users to recover which position
-- in the @ctx@ the type belongs to.
--
-- 'Elective' can be thought of as a generaliztion of the 'Either' type to an
-- arbitrary number of constructors, similar to how 'Assignment' is a
-- generalization of pairs to an arbitrary number of fields.
--
-- Naming intuition: an 'Assignment' requires every element to be filled out
-- (much like an assignment in school), whereas an 'Elective' grants the ability
-- to choose which element to use (much like an elective in school).
data Elective (f :: k -> Type) (ctx :: Ctx k) where
  Elective :: !(Index ctx tp) -> !(f tp) -> Elective f ctx

-- | Case analysis for the 'Elective' type. Analogous to 'either'.
elective :: (forall tp . f tp -> c) -> Elective f ctx -> c
elective f (Elective _ x) = f x

-- | 'elective', but the function can use the 'Index'.
ielective :: (forall tp . Index ctx tp -> f tp -> c) -> Elective f ctx -> c
ielective f (Elective idx x) = f idx x

-- | Extracts all the elements of a particular index from a list of
-- 'Elective's. All such elements are extracted in order. Analogous to
-- 'Data.Either.lefts' and 'Data.Either.rights'.
elect :: Index ctx tp -> [Elective f ctx] -> [f tp]
elect _ [] = []
elect idx1 (Elective idx2 x : es)
  | Just Refl <- testEquality idx1 idx2
  = x : elect idx1 es
  | otherwise
  = elect idx1 es

-- | Returns 'True' if the given value is an element of a particular 'Elective'
-- index, 'False' otherwise. Analogous to 'Data.Either.isLeft' and
-- 'Data.Either.isRight'.
isElective :: Index ctx tp -> Elective f ctx -> Bool
isElective idx1 (Elective idx2 _) = isJust (testEquality idx1 idx2)

-- | Return the contents of a 'Elective' value if its index matches, or a
-- default value otherwise. Analogous to 'Data.Either.fromLeft' and
-- 'Data.Either.fromRight'.
fromElective :: Index ctx tp -> f tp -> Elective f ctx -> f tp
fromElective idx1 x (Elective idx2 y)
  | Just Refl <- testEquality idx1 idx2
  = y
  | otherwise
  = x

-- | Partition a list of @'Elective' f ctx@ values into @n@ lists, where @n@ is
-- the number of different types in @ctx@. Analogous to
-- 'Data.Either.partitionEithers'.
partitionElectives ::
  forall f ctx.
  KnownContext ctx =>
  [Elective f ctx] ->
  Assignment (Compose [] f) ctx
partitionElectives = foldr insertIntoAssignment emptyListAssignment
  where
    emptyListAssignment ::
      Assignment (Compose [] f) ctx
    emptyListAssignment = Ctx.replicate knownSize (Compose [])

    insertIntoAssignment ::
      Elective f ctx ->
      Assignment (Compose [] f) ctx ->
      Assignment (Compose [] f) ctx
    insertIntoAssignment (Elective idx x) a =
      over (ixF idx) (\(Compose xs) -> Compose (x:xs)) a

-- | Retrieve the 'Index' from an 'Elective' value.
electiveIndex :: Elective f ctx -> Some (Index ctx)
electiveIndex (Elective idx _) = Some idx

-- | Retrieve the contents of an 'Elective' value.
electiveElement :: Elective f ctx -> Some f
electiveElement (Elective _ x) = Some x

type instance IndexF   (Elective f ctx) = Index  ctx
type instance IxValueF (Elective f ctx) = f

instance forall k (f :: k -> Type) ctx. IxedF k (Elective f ctx) where
  ixF idx1 f e@(Elective idx2 x)
    | Just Refl <- testEquality idx1 idx2
    = Elective idx2 <$> f x
    | otherwise
    = pure e

instance FunctorFC Elective where
  fmapFC f (Elective idx x) = Elective idx (f x)
instance FunctorFCWithIndex Elective where
  imapFC f (Elective idx x) = Elective idx (f idx x)

instance FoldableFC Elective where
  foldMapFC f (Elective _ x) = f x
  foldrFC f z (Elective _ x) = f x z
instance FoldableFCWithIndex Elective where
  ifoldMapFC f (Elective idx x) = f idx x
  ifoldrFC f z (Elective idx x) = f idx x z

instance TraversableFC Elective where
  traverseFC f (Elective idx x) = Elective idx <$> f x
instance TraversableFCWithIndex Elective where
  itraverseFC f (Elective idx x) = Elective idx <$> f idx x

instance TestEquality f => Eq (Elective f ctx) where
  Elective idx1 x1 == Elective idx2 x2
    = isJust (testEquality idx1 idx2) && isJust (testEquality x1 x2)

instance OrdF f => Ord (Elective f ctx) where
  compare (Elective idx1 x1) (Elective idx2 x2) =
    toOrdering (compareF idx1 idx2) <> toOrdering (compareF x1 x2)

instance (HashableF f, TestEquality f) => Hashable (Elective f ctx) where
  hashWithSalt s (Elective idx x) = s `hashWithSaltF` idx `hashWithSaltF` x
instance (HashableF f, TestEquality f) => HashableF (Elective f) where
  hashWithSaltF = hashWithSalt

instance ShowF f => Show (Elective f ctx) where
  showsPrec p (Elective idx x) =
    showParen (p >= 11) $
      showString "Elective " .
      showsPrec 11 idx .
      showChar ' ' .
      showsPrecF 11 x
instance ShowF f => ShowF (Elective f)
