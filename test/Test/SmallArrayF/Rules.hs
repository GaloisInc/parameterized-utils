{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- Compile at -O2 so all INLINE pragmas and RULES fire fully.
-- Disable HPC ticks and worker-wrapper so LHS/RHS Core can be compared.
{-# OPTIONS_GHC -O2 -fplugin=Test.Tasty.Inspection.Plugin -fno-hpc -fno-worker-wrapper #-}
-- Several rules rely on simplifier/rewriter behavior that only matches
-- LHS/RHS Core on GHC >= 9.8; on older GHCs we skip the whole suite.
-- Semantic correctness is still covered by RulesSemantics.

module Test.SmallArrayF.Rules (tests) where

import qualified Test.Tasty as TT

#if __GLASGOW_HASKELL__ >= 908

import           Control.Monad.ST (ST)
import           Data.Functor.Identity (Identity(Identity, runIdentity))
import           Data.Kind (Type)
import           Data.Parameterized.Context (Index)
import qualified Data.Parameterized.SmallArrayF as SAF
import           Data.Parameterized.SmallArrayF (SmallArrayF)
import           Data.Parameterized.TraversableFC
import           Data.Parameterized.TraversableFC.WithIndex
import           Test.Tasty.Inspection

import           Data.Parameterized.Ctx (EmptyCtx, type (::>))
import qualified Data.Parameterized.Context as Ctx

------------------------------------------------------------------------
-- Payload type

newtype V (tp :: Type) = V Int
  deriving (Show, Eq)

type Ctx3 = EmptyCtx ::> Int ::> Bool ::> Char

------------------------------------------------------------------------
-- NOINLINE element-level functions (so rules can still fire on the
-- container combinators but the payloads don't get optimized away).

{-# NOINLINE twiddle #-}
twiddle :: V tp -> V tp
twiddle (V n) = V (n + 1)

{-# NOINLINE twaddle #-}
twaddle :: V tp -> V tp
twaddle (V n) = V (n * 2)

{-# NOINLINE itwiddle #-}
itwiddle :: Index ctx tp -> V tp -> V tp
itwiddle idx (V n) = V (n + Ctx.indexVal idx)

{-# NOINLINE itwaddle #-}
itwaddle :: Index ctx tp -> V tp -> V tp
itwaddle idx (V n) = V (n * (1 + Ctx.indexVal idx))

{-# NOINLINE stTwiddle #-}
stTwiddle :: V tp -> ST s (V tp)
stTwiddle (V n) = pure (V (n + 1))

{-# NOINLINE ioTwiddle #-}
ioTwiddle :: V tp -> IO (V tp)
ioTwiddle (V n) = pure (V (n + 1))

{-# NOINLINE stZipFn #-}
stZipFn :: V tp -> V tp -> ST s (V tp)
stZipFn (V a) (V b) = pure (V (a + b))

{-# NOINLINE ioZipFn #-}
ioZipFn :: V tp -> V tp -> IO (V tp)
ioZipFn (V a) (V b) = pure (V (a + b))

{-# NOINLINE istTwiddle #-}
istTwiddle :: Index ctx tp -> V tp -> ST s (V tp)
istTwiddle idx (V n) = pure (V (n + Ctx.indexVal idx))

{-# NOINLINE ioiTwiddle #-}
ioiTwiddle :: Index ctx tp -> V tp -> IO (V tp)
ioiTwiddle idx (V n) = pure (V (n + Ctx.indexVal idx))

------------------------------------------------------------------------
-- Fusion rules: fmapFC_/fmapFC_
--
-- After the rule fires, fmapFC twaddle (fmapFC twiddle arr) becomes
-- fmapFC (twaddle . twiddle) arr — a single pass.  We verify this by
-- checking that the two-pass version compiles to the same Core as the
-- single-pass version.  NOINLINE prevents worker-wrapper from creating
-- differently-named wrappers that defeat the comparison.

{-# NOINLINE lhs_fmapFC_fmapFC #-}
lhs_fmapFC_fmapFC :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
lhs_fmapFC_fmapFC arr = fmapFC twaddle (fmapFC twiddle arr)

{-# NOINLINE rhs_fmapFC_fmapFC #-}
rhs_fmapFC_fmapFC :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
rhs_fmapFC_fmapFC arr = fmapFC (twaddle . twiddle) arr

-- Fusion rules: traverseFC/fmapFC_

{-# NOINLINE lhs_traverseFC_fmapFC #-}
lhs_traverseFC_fmapFC :: SmallArrayF V Ctx3 -> Identity (SmallArrayF V Ctx3)
lhs_traverseFC_fmapFC arr = traverseFC (Identity . twaddle) (fmapFC twiddle arr)

{-# NOINLINE rhs_traverseFC_fmapFC #-}
rhs_traverseFC_fmapFC :: SmallArrayF V Ctx3 -> Identity (SmallArrayF V Ctx3)
rhs_traverseFC_fmapFC arr = traverseFC (Identity . twaddle . twiddle) arr

-- Fusion rules: itraverseFC/fmapFC_

{-# NOINLINE lhs_itraverseFC_fmapFC #-}
lhs_itraverseFC_fmapFC :: SmallArrayF V Ctx3 -> Identity (SmallArrayF V Ctx3)
lhs_itraverseFC_fmapFC arr = itraverseFC (\idx x -> Identity (itwiddle idx x)) (fmapFC twiddle arr)

{-# NOINLINE rhs_itraverseFC_fmapFC #-}
rhs_itraverseFC_fmapFC :: SmallArrayF V Ctx3 -> Identity (SmallArrayF V Ctx3)
rhs_itraverseFC_fmapFC arr = itraverseFC (\idx -> Identity . itwiddle idx . twiddle) arr

-- Fusion rules: itraverseFC/imapFC_

{-# NOINLINE lhs_itraverseFC_imapFC #-}
lhs_itraverseFC_imapFC :: SmallArrayF V Ctx3 -> Identity (SmallArrayF V Ctx3)
lhs_itraverseFC_imapFC arr = itraverseFC (\idx x -> Identity (itwiddle idx x)) (imapFC itwaddle arr)

{-# NOINLINE rhs_itraverseFC_imapFC #-}
rhs_itraverseFC_imapFC :: SmallArrayF V Ctx3 -> Identity (SmallArrayF V Ctx3)
rhs_itraverseFC_imapFC arr = itraverseFC (\idx -> Identity . itwiddle idx . itwaddle idx) arr

-- Fusion rules: imapFC_/fmapFC_

{-# NOINLINE lhs_imapFC_fmapFC #-}
lhs_imapFC_fmapFC :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
lhs_imapFC_fmapFC arr = imapFC itwiddle (fmapFC twiddle arr)

{-# NOINLINE rhs_imapFC_fmapFC #-}
rhs_imapFC_fmapFC :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
rhs_imapFC_fmapFC arr = imapFC (\idx -> itwiddle idx . twiddle) arr

-- Fusion rules: imapFC_/imapFC_

{-# NOINLINE lhs_imapFC_imapFC #-}
lhs_imapFC_imapFC :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
lhs_imapFC_imapFC arr = imapFC itwiddle (imapFC itwaddle arr)

{-# NOINLINE rhs_imapFC_imapFC #-}
rhs_imapFC_imapFC :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
rhs_imapFC_imapFC arr = imapFC (\idx -> itwiddle idx . itwaddle idx) arr

-- Fusion rules: fmapFC_/imapFC_

{-# NOINLINE lhs_fmapFC_imapFC #-}
lhs_fmapFC_imapFC :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
lhs_fmapFC_imapFC arr = fmapFC twaddle (imapFC itwaddle arr)

{-# NOINLINE rhs_fmapFC_imapFC #-}
rhs_fmapFC_imapFC :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
rhs_fmapFC_imapFC arr = imapFC (\idx -> twaddle . itwaddle idx) arr

-- Specialization: generateA/Identity

{-# NOINLINE lhs_generateA_Identity #-}
lhs_generateA_Identity :: Ctx.Size Ctx3 -> (forall tp. Index Ctx3 tp -> Identity (V tp)) -> Identity (SmallArrayF V Ctx3)
lhs_generateA_Identity sz fn = SAF.generateA sz fn

{-# NOINLINE rhs_generateA_Identity #-}
rhs_generateA_Identity :: Ctx.Size Ctx3 -> (forall tp. Index Ctx3 tp -> Identity (V tp)) -> Identity (SmallArrayF V Ctx3)
rhs_generateA_Identity sz fn = Identity (SAF.generate sz (runIdentity . fn))

-- Identity: fmapFC_/id

{-# NOINLINE lhs_fmapFC_id #-}
lhs_fmapFC_id :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
lhs_fmapFC_id arr = fmapFC (\x -> x) arr

{-# NOINLINE rhs_fmapFC_id #-}
rhs_fmapFC_id :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
rhs_fmapFC_id arr = arr

-- Cancellation: fromAssignment/toAssignment

{-# NOINLINE lhs_fromTo #-}
lhs_fromTo :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
lhs_fromTo a = SAF.fromAssignment (SAF.toAssignment a)

{-# NOINLINE rhs_fromTo #-}
rhs_fromTo :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
rhs_fromTo a = a

-- Cancellation: toAssignment/fromAssignment

{-# NOINLINE lhs_toFrom #-}
lhs_toFrom :: Ctx.Assignment V Ctx3 -> Ctx.Assignment V Ctx3
lhs_toFrom a = SAF.toAssignment (SAF.fromAssignment a)

{-# NOINLINE rhs_toFrom #-}
rhs_toFrom :: Ctx.Assignment V Ctx3 -> Ctx.Assignment V Ctx3
rhs_toFrom a = a

-- Specialization: traverseFC/ST

{-# NOINLINE lhs_traverseFC_ST #-}
lhs_traverseFC_ST :: SmallArrayF V Ctx3 -> ST s (SmallArrayF V Ctx3)
lhs_traverseFC_ST arr = traverseFC stTwiddle arr

{-# NOINLINE rhs_traverseFC_ST #-}
rhs_traverseFC_ST :: SmallArrayF V Ctx3 -> ST s (SmallArrayF V Ctx3)
rhs_traverseFC_ST arr = SAF.traverseFCST stTwiddle arr

-- Specialization: traverseFC/IO

{-# NOINLINE lhs_traverseFC_IO #-}
lhs_traverseFC_IO :: SmallArrayF V Ctx3 -> IO (SmallArrayF V Ctx3)
lhs_traverseFC_IO arr = traverseFC ioTwiddle arr

{-# NOINLINE rhs_traverseFC_IO #-}
rhs_traverseFC_IO :: SmallArrayF V Ctx3 -> IO (SmallArrayF V Ctx3)
rhs_traverseFC_IO arr = SAF.traverseFCIO ioTwiddle arr

-- Specialization: itraverseFC/ST

{-# NOINLINE lhs_itraverseFC_ST #-}
lhs_itraverseFC_ST :: SmallArrayF V Ctx3 -> ST s (SmallArrayF V Ctx3)
lhs_itraverseFC_ST arr = itraverseFC istTwiddle arr

{-# NOINLINE rhs_itraverseFC_ST #-}
rhs_itraverseFC_ST :: SmallArrayF V Ctx3 -> ST s (SmallArrayF V Ctx3)
rhs_itraverseFC_ST arr = SAF.itraverseFCST istTwiddle arr

-- Specialization: itraverseFC/IO

{-# NOINLINE lhs_itraverseFC_IO #-}
lhs_itraverseFC_IO :: SmallArrayF V Ctx3 -> IO (SmallArrayF V Ctx3)
lhs_itraverseFC_IO arr = itraverseFC ioiTwiddle arr

{-# NOINLINE rhs_itraverseFC_IO #-}
rhs_itraverseFC_IO :: SmallArrayF V Ctx3 -> IO (SmallArrayF V Ctx3)
rhs_itraverseFC_IO arr = SAF.itraverseFCIO ioiTwiddle arr

-- Specialization: zipWithMFC/ST

{-# NOINLINE lhs_zipWithMFC_ST #-}
lhs_zipWithMFC_ST :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3 -> ST s (SmallArrayF V Ctx3)
lhs_zipWithMFC_ST a b = SAF.zipWithMFC stZipFn a b

{-# NOINLINE rhs_zipWithMFC_ST #-}
rhs_zipWithMFC_ST :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3 -> ST s (SmallArrayF V Ctx3)
rhs_zipWithMFC_ST a b = SAF.zipWithMFCST stZipFn a b

-- Specialization: zipWithMFC/IO

{-# NOINLINE lhs_zipWithMFC_IO #-}
lhs_zipWithMFC_IO :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3 -> IO (SmallArrayF V Ctx3)
lhs_zipWithMFC_IO a b = SAF.zipWithMFC ioZipFn a b

{-# NOINLINE rhs_zipWithMFC_IO #-}
rhs_zipWithMFC_IO :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3 -> IO (SmallArrayF V Ctx3)
rhs_zipWithMFC_IO a b = SAF.zipWithMFCIO ioZipFn a b

-- Cancellation: take/append

{-# NOINLINE lhs_take_append #-}
lhs_take_append :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
lhs_take_append a b = SAF.take (SAF.size a) (SAF.size b) (SAF.append a b)

{-# NOINLINE rhs_take_append #-}
rhs_take_append :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
rhs_take_append a _ = a

-- Cancellation: drop/append

{-# NOINLINE lhs_drop_append #-}
lhs_drop_append :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
lhs_drop_append a b = SAF.drop (SAF.size a) (SAF.size b) (SAF.append a b)

{-# NOINLINE rhs_drop_append #-}
rhs_drop_append :: SmallArrayF V Ctx3 -> SmallArrayF V Ctx3 -> SmallArrayF V Ctx3
rhs_drop_append _ b = b

------------------------------------------------------------------------
-- Test tree

tests :: TT.TestTree
tests = TT.testGroup "SmallArrayF RULES (inspection)"
  [ $(inspectTest $ 'lhs_generateA_Identity ==~ 'rhs_generateA_Identity)
  , $(inspectTest $ 'lhs_fmapFC_id ==~ 'rhs_fmapFC_id)
  , $(inspectTest $ 'lhs_fmapFC_fmapFC ==~ 'rhs_fmapFC_fmapFC)
  , $(inspectTest $ 'lhs_traverseFC_fmapFC ==~ 'rhs_traverseFC_fmapFC)
  , $(inspectTest $ 'lhs_itraverseFC_fmapFC ==~ 'rhs_itraverseFC_fmapFC)
  , $(inspectTest $ 'lhs_itraverseFC_imapFC ==~ 'rhs_itraverseFC_imapFC)
  , $(inspectTest $ 'lhs_imapFC_fmapFC ==~ 'rhs_imapFC_fmapFC)
  , $(inspectTest $ 'lhs_imapFC_imapFC ==~ 'rhs_imapFC_imapFC)
  , $(inspectTest $ 'lhs_fmapFC_imapFC ==~ 'rhs_fmapFC_imapFC)
  , $(inspectTest $ 'lhs_fromTo ==~ 'rhs_fromTo)
  , $(inspectTest $ 'lhs_toFrom ==~ 'rhs_toFrom)
  , $(inspectTest $ 'lhs_traverseFC_ST ==~ 'rhs_traverseFC_ST)
  , $(inspectTest $ 'lhs_traverseFC_IO ==~ 'rhs_traverseFC_IO)
  , $(inspectTest $ 'lhs_itraverseFC_ST ==~ 'rhs_itraverseFC_ST)
  , $(inspectTest $ 'lhs_itraverseFC_IO ==~ 'rhs_itraverseFC_IO)
  , $(inspectTest $ 'lhs_zipWithMFC_ST ==~ 'rhs_zipWithMFC_ST)
  , $(inspectTest $ 'lhs_zipWithMFC_IO ==~ 'rhs_zipWithMFC_IO)
  , $(inspectTest $ 'lhs_take_append ==~ 'rhs_take_append)
  , $(inspectTest $ 'lhs_drop_append ==~ 'rhs_drop_append)
  ]

#else

tests :: TT.TestTree
tests = TT.testGroup "SmallArrayF RULES (inspection)" []

#endif
