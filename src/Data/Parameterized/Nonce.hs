{-|
Description : Index generator in the ST monad.
Copyright   : (c) Galois, Inc 2014-2019
Maintainer  : Joe Hendrix <jhendrix@galois.com>

This module provides a simple generator of new indexes in the 'ST' monad.
It is predictable and not intended for cryptographic purposes.

This module also provides a global nonce generator that will generate
2^64 nonces before repeating.

NOTE: The 'TestEquality' and 'OrdF' instances for the 'Nonce' type simply
compare the generated nonce values and then assert to the compiler
(via 'unsafeCoerce') that the types ascribed to the nonces are equal
if their values are equal.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE Trustworthy #-}
#if MIN_VERSION_base(4,9,0)
{-# LANGUAGE TypeInType #-}
#endif
module Data.Parameterized.Nonce
  ( -- * NonceGenerator
    NonceGenerator
  , freshNonce
  , countNoncesGenerated
  , Nonce
  , indexValue
    -- * Accessing a nonce generator
  , newSTNonceGenerator
  , newIONonceGenerator
  , withIONonceGenerator
  , withSTNonceGenerator
    -- * Global nonce generator
  , withGlobalSTNonceGenerator
  , GlobalNonceGenerator
  , globalNonceGenerator
  ) where

import Control.Monad.ST
import Data.Hashable
import Data.IORef
import Data.STRef
import Data.Typeable
import Data.Word
import Unsafe.Coerce
import System.IO.Unsafe (unsafePerformIO)

import Data.Parameterized.Classes
import Data.Parameterized.Some

#if MIN_VERSION_base(4,9,0) && __GLASGOW_HASKELL__ < 805
import Data.Kind
#endif

-- | Provides a monadic action for getting fresh typed names.
--
-- The first type parameter @m@ is the monad used for generating names, and
-- the second parameter @s@ is used for the counter.
data NonceGenerator (m :: * -> *) (s :: *) where
  STNG :: !(STRef t Word64) -> NonceGenerator (ST t) s
  IONG :: !(IORef Word64) -> NonceGenerator IO s

#if MIN_VERSION_base(4,9,0)
-- We have to make the k explicit in GHC 8.0 to avoid a warning.
freshNonce :: forall m s k (tp :: k) . NonceGenerator m s -> m (Nonce s tp)
#else
freshNonce :: forall m s (tp :: k) . NonceGenerator m s -> m (Nonce s tp)
#endif
freshNonce (IONG r) =
  atomicModifyIORef' r $ \n -> (n+1, Nonce n)
freshNonce (STNG r) = do
  i <- readSTRef r
  writeSTRef r $! i+1
  return $ Nonce i
  -- (Weirdly, there's no atomicModifySTRef'.  Yes, only the IO monad
  -- does concurrency, but the ST monad is part of the IO monad via
  -- stToIO, so there's no guarantee that ST code won't be run in
  -- multiple threads.)

{-# INLINE freshNonce #-}
  -- Inlining is particularly necessary since there's no @Monad m@
  -- constraint on 'freshNonce', so SPECIALIZE doesn't work on it.  In
  -- this case, though, we get specialization for free from inlining.
  -- For instance, a @NonceGenerator IO s@ must be an @IONG@, so the
  -- simplifier eliminates the STNG branch.

-- | The number of nonces generated so far by this generator.  Only
-- really useful for profiling.
countNoncesGenerated :: NonceGenerator m s -> m Integer
countNoncesGenerated (IONG r) = toInteger <$> readIORef r
countNoncesGenerated (STNG r) = toInteger <$> readSTRef r

-- | Create a new nonce generator in the 'ST' monad.
newSTNonceGenerator :: ST t (Some (NonceGenerator (ST t)))
newSTNonceGenerator = Some . STNG <$> newSTRef (toEnum 0)

-- | Create a new nonce generator in the 'ST' monad.
newIONonceGenerator :: IO (Some (NonceGenerator IO))
newIONonceGenerator = Some . IONG <$> newIORef (toEnum 0)

-- | Run a 'ST' computation with a new nonce generator in the 'ST' monad.
withSTNonceGenerator :: (forall s . NonceGenerator (ST t) s -> (ST t) r) -> ST t r
withSTNonceGenerator f = do
  Some r <- newSTNonceGenerator
  f r

-- | Create a new nonce generator in the 'IO' monad.
withIONonceGenerator :: (forall s . NonceGenerator IO s -> IO r) -> IO r
withIONonceGenerator f = do
  Some r <- newIONonceGenerator
  f r

-- | An index generated by the counter.
newtype Nonce (s :: *) (tp :: k) = Nonce { indexValue :: Word64 }
  deriving (Eq, Ord, Hashable, Show)

--  Force the type role of Nonce to be nominal: this prevents Data.Coerce.coerce
--  from casting the types of nonces, which it would otherwise be able to do
--  because tp is a phantom type parameter.  This partially helps to protect
--  the nonce abstraction.
type role Nonce nominal nominal

instance TestEquality (Nonce s) where
  testEquality x y | indexValue x == indexValue y = unsafeCoerce (Just Refl)
                   | otherwise = Nothing

instance OrdF (Nonce s) where
  compareF x y =
    case compare (indexValue x) (indexValue y) of
      LT -> LTF
      EQ -> unsafeCoerce EQF
      GT -> GTF

instance HashableF (Nonce s) where
  hashWithSaltF s (Nonce x) = hashWithSalt s x

instance ShowF (Nonce s)

------------------------------------------------------------------------
-- * GlobalNonceGenerator

data GlobalNonceGenerator

globalNonceIORef :: IORef Word64
globalNonceIORef = unsafePerformIO (newIORef 0)
{-# NOINLINE globalNonceIORef #-}

-- | A nonce generator that uses a globally-defined counter.
globalNonceGenerator :: NonceGenerator IO GlobalNonceGenerator
globalNonceGenerator = IONG globalNonceIORef

-- | Create a new counter.
withGlobalSTNonceGenerator :: (forall t . NonceGenerator (ST t) t -> ST t r) -> r
withGlobalSTNonceGenerator f = runST $ do
  r <- newSTRef (toEnum 0)
  f $! STNG r
