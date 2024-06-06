{-|
Description : Strongly-kinded version of "Data.Parameterized.Nonce"
Copyright   : (c) Galois, Inc 2024
Maintainer  : Langston Barrett <langston@galois.com>

The \"brand\" type parameter of 'Nonce.NonceGenerator' and 'Nonce.Nonce' has
kind 'Type', making it easy to confuse with other type variables of the same
kind. This module introduces a @newtype@ wrapper for the types and functions
in "Data.Parameterized.Nonce" with a dedicated kind for brands ('NonceBrand').
Using this module turns some classes of incorrect type signatures into type
(kind) errors, helping to find issues earlier in the development process.

The primary downside is that we cannot offer an analog to
'Nonce.runSTNonceGenerator', the type of which would be ill-kinded under this
scheme.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Parameterized.Nonce.Strong
  ( NonceBrand
  , NonceGenerator
  , Nonce
  , indexValue
  , freshNonce
  , countNoncesGenerated
    -- * Accessing a nonce generator
  , newSTNonceGenerator
  , newIONonceGenerator
  , withIONonceGenerator
  , withSTNonceGenerator
    -- * Global nonce generator
  , GlobalNonceGenerator
  , globalNonceGenerator
  , withGlobalSTNonceGenerator
  ) where

import Control.Monad.ST (ST)
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Hashable (Hashable)
import Data.Word (Word64)

import           Data.Parameterized.Classes (HashableF, OrdF, TestEquality)
import qualified Data.Parameterized.Nonce as Nonce
import           Data.Parameterized.Some (Some(Some))

-- | Kind of brand type variables used in 'NonceGenerator', 'Nonce'.
--
-- Such variables function similarly to that of the 'ST' monad, see
-- "Data.Parameterized.Nonce" for more information.
newtype NonceBrand = NonceBrand Type

-- | See 'Nonce.GlobalNonceGenerator'.
type GlobalNonceGenerator = 'NonceBrand Nonce.GlobalNonceGenerator

-- | Not exported
type family Unwrap (nk :: NonceBrand) :: Type where
  Unwrap ('NonceBrand s) = s

-- | See 'Nonce.NonceGenerator'.
newtype NonceGenerator (m :: Type -> Type) (s :: NonceBrand)
  = NonceGenerator { getNonceGenerator :: Nonce.NonceGenerator m (Unwrap s) }

-- | See 'Nonce.Nonce'.
newtype Nonce (s :: NonceBrand) (tp :: k)
  = Nonce { getNonce :: Nonce.Nonce (Unwrap s) tp }
  deriving (Eq, Ord, Hashable, HashableF, OrdF, Show, TestEquality)

-- See comment in "Data.Parameterized.Nonce"
type role Nonce nominal nominal

-- | See 'Nonce.indexValue'.
indexValue :: Nonce s tp -> Word64
indexValue = Nonce.indexValue . getNonce

-- | See 'Nonce.freshNonce'.
freshNonce ::
  forall m s k (tp :: k).
  Functor m =>
  NonceGenerator m s ->
  m (Nonce s tp)
freshNonce (NonceGenerator ng) = Nonce <$> Nonce.freshNonce ng

-- | See 'Nonce.countNoncesGenerated'.
countNoncesGenerated :: NonceGenerator m s -> m Integer
countNoncesGenerated = Nonce.countNoncesGenerated . getNonceGenerator

-- | See 'Nonce.newSTNonceGenerator'.
newSTNonceGenerator :: ST t (Some (NonceGenerator (ST t)))
newSTNonceGenerator = do
  Some (ng :: Nonce.NonceGenerator (ST t) s) <- Nonce.newSTNonceGenerator
  let ng' :: NonceGenerator (ST t) ('NonceBrand s)
      ng' = NonceGenerator ng
  pure (Some ng')

-- | See 'Nonce.newIONonceGenerator'.
newIONonceGenerator :: IO (Some (NonceGenerator IO))
newIONonceGenerator = do
  Some (ng :: Nonce.NonceGenerator IO s) <- Nonce.newIONonceGenerator
  let ng' :: NonceGenerator IO ('NonceBrand s)
      ng' = NonceGenerator ng
  pure (Some ng')

-- | See 'Nonce.withSTNonceGenerator'.
withSTNonceGenerator :: (forall s . NonceGenerator (ST t) s -> ST t r) -> ST t r
withSTNonceGenerator f = do
  Some r <- newSTNonceGenerator
  f r

-- | See 'Nonce.withIONonceGenerator'.
withIONonceGenerator :: (forall s . NonceGenerator IO s -> IO r) -> IO r
withIONonceGenerator f =  do
  Some r <- newIONonceGenerator
  f r

------------------------------------------------------------------------
-- * GlobalNonceGenerator

-- | See 'Nonce.globalNonceGenerator'.
globalNonceGenerator :: NonceGenerator IO GlobalNonceGenerator
globalNonceGenerator = NonceGenerator Nonce.globalNonceGenerator

-- | See 'Nonce.withGlobalSTNonceGenerator'.
withGlobalSTNonceGenerator ::
  (forall (t :: Type) (s :: NonceBrand). NonceGenerator (ST t) s -> ST t r) ->
  r
withGlobalSTNonceGenerator f =
  Nonce.withGlobalSTNonceGenerator (coerce f)
