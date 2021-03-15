{-|
Description : A typeclass and monad transformers for generating nonces.
Copyright   : (c) Galois, Inc 2014-2019
Maintainer  : Eddy Westbrook <westbrook@galois.com>

This module provides a typeclass and monad transformers for generating
nonces.
-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Parameterized.Nonce.Transformers
  ( MonadNonce(..)
  , NonceT(..)
  , NonceST
  , NonceIO
  , getNonceSTGen
  , runNonceST
  , runNonceIO
  , module Data.Parameterized.Nonce
  ) where

import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.State
import Data.Kind

import Data.Parameterized.Nonce


-- | A 'MonadNonce' is a monad that can generate fresh 'Nonce's in a given set
-- (where we view the phantom type parameter of 'Nonce' as a designator of the
-- set that the 'Nonce' came from).
class Monad m => MonadNonce m where
  type NonceSet m :: Type
  freshNonceM :: forall k (tp :: k) . m (Nonce (NonceSet m) tp)

-- | This transformer adds a nonce generator to a given monad.
newtype NonceT s m a =
  NonceT { runNonceT :: ReaderT (NonceGenerator m s) m a }
  deriving (Functor, Applicative, Monad)

instance MonadTrans (NonceT s) where
  lift m = NonceT $ lift m

instance Monad m => MonadNonce (NonceT s m) where
  type NonceSet (NonceT s m) = s
  freshNonceM = NonceT $ lift . freshNonce =<< ask

instance MonadNonce m => MonadNonce (StateT s m) where
  type NonceSet (StateT s m) = NonceSet m
  freshNonceM = lift $ freshNonceM

-- | Helper type to build a 'MonadNonce' from the 'ST' monad.
type NonceST t s = NonceT s (ST t)

-- | Helper type to build a 'MonadNonce' from the 'IO' monad.
type NonceIO s = NonceT s IO

-- | Return the actual 'NonceGenerator' used in an 'ST' computation.
getNonceSTGen :: NonceST t s (NonceGenerator (ST t) s)
getNonceSTGen = NonceT ask

-- | Run a 'NonceST' computation with a fresh 'NonceGenerator'.
runNonceST :: (forall t s. NonceST t s a) -> a
runNonceST m = runST $ withSTNonceGenerator $ runReaderT $ runNonceT m

-- | Run a 'NonceIO' computation with a fresh 'NonceGenerator' inside 'IO'.
runNonceIO :: (forall s. NonceIO s a) -> IO a
runNonceIO m = withIONonceGenerator $ runReaderT $ runNonceT m
