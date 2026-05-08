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
-- Inspection tests require GHC >= 9.8 to match LHS/RHS Core reliably.
-- Semantic correctness is still covered by RulesSemantics on all versions.

module Test.Context.Rules (tests) where

import qualified Test.Tasty as TT

#if __GLASGOW_HASKELL__ >= 908

import           Data.Functor.Identity (Identity(Identity))
import           Data.Kind (Type)
import qualified Data.Parameterized.Context as C
import           Data.Parameterized.Context (Index)
import           Data.Parameterized.TraversableFC
import           Data.Parameterized.TraversableFC.WithIndex
import           Test.Tasty.Inspection

import           Data.Parameterized.Ctx (EmptyCtx, type (::>))
import           Data.Parameterized.Context (knownSize)

------------------------------------------------------------------------
-- Payload type

newtype V (tp :: Type) = V Int
  deriving (Show, Eq)

type Ctx3 = EmptyCtx ::> Int ::> Bool ::> Char

------------------------------------------------------------------------
-- NOINLINE element-level functions so rules fire on the container
-- combinators while payloads stay opaque.

{-# NOINLINE twiddle #-}
twiddle :: V tp -> V tp
twiddle (V n) = V (n + 1)

{-# NOINLINE twaddle #-}
twaddle :: V tp -> V tp
twaddle (V n) = V (n * 2)

{-# NOINLINE itwiddle #-}
itwiddle :: Index ctx tp -> V tp -> V tp
itwiddle idx (V n) = V (n + C.indexVal idx)

{-# NOINLINE itwaddle #-}
itwaddle :: Index ctx tp -> V tp -> V tp
itwaddle idx (V n) = V (n * (1 + C.indexVal idx))

------------------------------------------------------------------------
-- Identity: fmapFC/id

{-# NOINLINE lhs_fmapFC_id #-}
lhs_fmapFC_id :: C.Assignment V Ctx3 -> C.Assignment V Ctx3
lhs_fmapFC_id asgn = fmapFC (\x -> x) asgn

{-# NOINLINE rhs_fmapFC_id #-}
rhs_fmapFC_id :: C.Assignment V Ctx3 -> C.Assignment V Ctx3
rhs_fmapFC_id asgn = asgn

------------------------------------------------------------------------
-- Fusion rules: fmapFC/fmapFC

{-# NOINLINE lhs_fmapFC_fmapFC #-}
lhs_fmapFC_fmapFC :: C.Assignment V Ctx3 -> C.Assignment V Ctx3
lhs_fmapFC_fmapFC asgn = fmapFC twaddle (fmapFC twiddle asgn)

{-# NOINLINE rhs_fmapFC_fmapFC #-}
rhs_fmapFC_fmapFC :: C.Assignment V Ctx3 -> C.Assignment V Ctx3
rhs_fmapFC_fmapFC asgn = fmapFC (twaddle . twiddle) asgn

------------------------------------------------------------------------
-- Fusion rules: traverseFC/fmapFC

{-# NOINLINE lhs_traverseFC_fmapFC #-}
lhs_traverseFC_fmapFC :: C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
lhs_traverseFC_fmapFC asgn = traverseFC (Identity . twaddle) (fmapFC twiddle asgn)

{-# NOINLINE rhs_traverseFC_fmapFC #-}
rhs_traverseFC_fmapFC :: C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
rhs_traverseFC_fmapFC asgn = traverseFC (Identity . twaddle . twiddle) asgn

------------------------------------------------------------------------
-- Fusion rules: traverseFC/imapFC

{-# NOINLINE lhs_traverseFC_imapFC #-}
lhs_traverseFC_imapFC :: C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
lhs_traverseFC_imapFC asgn = traverseFC (Identity . twaddle) (imapFC itwaddle asgn)

{-# NOINLINE rhs_traverseFC_imapFC #-}
rhs_traverseFC_imapFC :: C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
rhs_traverseFC_imapFC asgn = C.traverseWithIndex (\idx -> Identity . twaddle . itwaddle idx) asgn

------------------------------------------------------------------------
-- Fusion rules: itraverseFC/fmapFC

{-# NOINLINE lhs_itraverseFC_fmapFC #-}
lhs_itraverseFC_fmapFC :: C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
lhs_itraverseFC_fmapFC asgn = itraverseFC (\idx x -> Identity (itwiddle idx x)) (fmapFC twiddle asgn)

{-# NOINLINE rhs_itraverseFC_fmapFC #-}
rhs_itraverseFC_fmapFC :: C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
rhs_itraverseFC_fmapFC asgn = itraverseFC (\idx -> Identity . itwiddle idx . twiddle) asgn

------------------------------------------------------------------------
-- Fusion rules: itraverseFC/imapFC

{-# NOINLINE lhs_itraverseFC_imapFC #-}
lhs_itraverseFC_imapFC :: C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
lhs_itraverseFC_imapFC asgn = itraverseFC (\idx x -> Identity (itwiddle idx x)) (imapFC itwaddle asgn)

{-# NOINLINE rhs_itraverseFC_imapFC #-}
rhs_itraverseFC_imapFC :: C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
rhs_itraverseFC_imapFC asgn = itraverseFC (\idx -> Identity . itwiddle idx . itwaddle idx) asgn

------------------------------------------------------------------------
-- Fusion rules: imapFC/fmapFC

{-# NOINLINE lhs_imapFC_fmapFC #-}
lhs_imapFC_fmapFC :: C.Assignment V Ctx3 -> C.Assignment V Ctx3
lhs_imapFC_fmapFC asgn = imapFC itwiddle (fmapFC twiddle asgn)

{-# NOINLINE rhs_imapFC_fmapFC #-}
rhs_imapFC_fmapFC :: C.Assignment V Ctx3 -> C.Assignment V Ctx3
rhs_imapFC_fmapFC asgn = imapFC (\idx -> itwiddle idx . twiddle) asgn

------------------------------------------------------------------------
-- Fusion rules: imapFC/imapFC

{-# NOINLINE lhs_imapFC_imapFC #-}
lhs_imapFC_imapFC :: C.Assignment V Ctx3 -> C.Assignment V Ctx3
lhs_imapFC_imapFC asgn = imapFC itwiddle (imapFC itwaddle asgn)

{-# NOINLINE rhs_imapFC_imapFC #-}
rhs_imapFC_imapFC :: C.Assignment V Ctx3 -> C.Assignment V Ctx3
rhs_imapFC_imapFC asgn = imapFC (\idx -> itwiddle idx . itwaddle idx) asgn

------------------------------------------------------------------------
-- Fusion rules: fmapFC/imapFC

{-# NOINLINE lhs_fmapFC_imapFC #-}
lhs_fmapFC_imapFC :: C.Assignment V Ctx3 -> C.Assignment V Ctx3
lhs_fmapFC_imapFC asgn = fmapFC twaddle (imapFC itwaddle asgn)

{-# NOINLINE rhs_fmapFC_imapFC #-}
rhs_fmapFC_imapFC :: C.Assignment V Ctx3 -> C.Assignment V Ctx3
rhs_fmapFC_imapFC asgn = imapFC (\idx -> twaddle . itwaddle idx) asgn

------------------------------------------------------------------------
-- Fusion rules: fmapFC/generate

{-# NOINLINE lhs_fmapFC_generate #-}
lhs_fmapFC_generate :: (forall tp. Index Ctx3 tp -> V tp) -> C.Assignment V Ctx3
lhs_fmapFC_generate g = fmapFC twiddle (C.generate knownSize g)

{-# NOINLINE rhs_fmapFC_generate #-}
rhs_fmapFC_generate :: (forall tp. Index Ctx3 tp -> V tp) -> C.Assignment V Ctx3
rhs_fmapFC_generate g = C.generate knownSize (\idx -> twiddle (g idx))

------------------------------------------------------------------------
-- Fusion rules: imapFC/generate

{-# NOINLINE lhs_imapFC_generate #-}
lhs_imapFC_generate :: (forall tp. Index Ctx3 tp -> V tp) -> C.Assignment V Ctx3
lhs_imapFC_generate g = imapFC itwiddle (C.generate knownSize g)

{-# NOINLINE rhs_imapFC_generate #-}
rhs_imapFC_generate :: (forall tp. Index Ctx3 tp -> V tp) -> C.Assignment V Ctx3
rhs_imapFC_generate g = C.generate knownSize (\idx -> itwiddle idx (g idx))

------------------------------------------------------------------------
-- Fusion rules: traverseFC/generate

{-# NOINLINE lhs_traverseFC_generate #-}
lhs_traverseFC_generate :: (forall tp. Index Ctx3 tp -> V tp) -> Identity (C.Assignment V Ctx3)
lhs_traverseFC_generate g = traverseFC (Identity . twiddle) (C.generate knownSize g)

{-# NOINLINE rhs_traverseFC_generate #-}
rhs_traverseFC_generate :: (forall tp. Index Ctx3 tp -> V tp) -> Identity (C.Assignment V Ctx3)
rhs_traverseFC_generate g = C.generateM knownSize (Identity . twiddle . g)

------------------------------------------------------------------------
-- Fusion rules: traverseWithIndex/generate

{-# NOINLINE lhs_traverseWithIndex_generate #-}
lhs_traverseWithIndex_generate :: (forall tp. Index Ctx3 tp -> V tp) -> Identity (C.Assignment V Ctx3)
lhs_traverseWithIndex_generate g = C.traverseWithIndex (\idx x -> Identity (itwiddle idx x)) (C.generate knownSize g)

{-# NOINLINE rhs_traverseWithIndex_generate #-}
rhs_traverseWithIndex_generate :: (forall tp. Index Ctx3 tp -> V tp) -> Identity (C.Assignment V Ctx3)
rhs_traverseWithIndex_generate g = C.generateM knownSize (\idx -> Identity (itwiddle idx (g idx)))

------------------------------------------------------------------------
-- Fusion rules: (!)/generate

{-# NOINLINE lhs_index_generate #-}
lhs_index_generate :: (forall tp. Index Ctx3 tp -> V tp) -> Index Ctx3 Int -> V Int
lhs_index_generate g idx = C.generate knownSize g C.! idx

{-# NOINLINE rhs_index_generate #-}
rhs_index_generate :: (forall tp. Index Ctx3 tp -> V tp) -> Index Ctx3 Int -> V Int
rhs_index_generate g idx = g idx

------------------------------------------------------------------------
-- Fusion rules: (!)/fmapFC

{-# NOINLINE lhs_index_fmapFC #-}
lhs_index_fmapFC :: C.Assignment V Ctx3 -> Index Ctx3 Int -> V Int
lhs_index_fmapFC asgn idx = fmapFC twiddle asgn C.! idx

{-# NOINLINE rhs_index_fmapFC #-}
rhs_index_fmapFC :: C.Assignment V Ctx3 -> Index Ctx3 Int -> V Int
rhs_index_fmapFC asgn idx = twiddle (asgn C.! idx)

------------------------------------------------------------------------
-- Fusion rules: (!)/imapFC

{-# NOINLINE lhs_index_imapFC #-}
lhs_index_imapFC :: C.Assignment V Ctx3 -> Index Ctx3 Int -> V Int
lhs_index_imapFC asgn idx = imapFC itwiddle asgn C.! idx

{-# NOINLINE rhs_index_imapFC #-}
rhs_index_imapFC :: C.Assignment V Ctx3 -> Index Ctx3 Int -> V Int
rhs_index_imapFC asgn idx = itwiddle idx (asgn C.! idx)

------------------------------------------------------------------------
-- Fusion rules: zipWithM/fmapFC_l

{-# NOINLINE lhs_zipWithM_fmapFC_l #-}
lhs_zipWithM_fmapFC_l :: C.Assignment V Ctx3 -> C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
lhs_zipWithM_fmapFC_l a b = C.zipWithM (\x _ -> Identity (twiddle x)) (fmapFC twaddle a) b

{-# NOINLINE rhs_zipWithM_fmapFC_l #-}
rhs_zipWithM_fmapFC_l :: C.Assignment V Ctx3 -> C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
rhs_zipWithM_fmapFC_l a b = C.zipWithM (\x _ -> Identity (twiddle (twaddle x))) a b

------------------------------------------------------------------------
-- Fusion rules: zipWithM/fmapFC_r

{-# NOINLINE lhs_zipWithM_fmapFC_r #-}
lhs_zipWithM_fmapFC_r :: C.Assignment V Ctx3 -> C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
lhs_zipWithM_fmapFC_r a b = C.zipWithM (\_ y -> Identity (twiddle y)) a (fmapFC twaddle b)

{-# NOINLINE rhs_zipWithM_fmapFC_r #-}
rhs_zipWithM_fmapFC_r :: C.Assignment V Ctx3 -> C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
rhs_zipWithM_fmapFC_r a b = C.zipWithM (\_ y -> Identity (twiddle (twaddle y))) a b

------------------------------------------------------------------------
-- Fusion rules: zipWithM/generate_l

{-# NOINLINE lhs_zipWithM_generate_l #-}
lhs_zipWithM_generate_l :: (forall tp. Index Ctx3 tp -> V tp) -> C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
lhs_zipWithM_generate_l g b = C.zipWithM (\x _ -> Identity (twiddle x)) (C.generate knownSize g) b

{-# NOINLINE rhs_zipWithM_generate_l #-}
rhs_zipWithM_generate_l :: (forall tp. Index Ctx3 tp -> V tp) -> C.Assignment V Ctx3 -> Identity (C.Assignment V Ctx3)
rhs_zipWithM_generate_l g _ = C.generateM knownSize (\idx -> Identity (twiddle (g idx)))

------------------------------------------------------------------------
-- Fusion rules: zipWithM/generate_r

{-# NOINLINE lhs_zipWithM_generate_r #-}
lhs_zipWithM_generate_r :: C.Assignment V Ctx3 -> (forall tp. Index Ctx3 tp -> V tp) -> Identity (C.Assignment V Ctx3)
lhs_zipWithM_generate_r a g = C.zipWithM (\_ y -> Identity (twiddle y)) a (C.generate knownSize g)

{-# NOINLINE rhs_zipWithM_generate_r #-}
rhs_zipWithM_generate_r :: C.Assignment V Ctx3 -> (forall tp. Index Ctx3 tp -> V tp) -> Identity (C.Assignment V Ctx3)
rhs_zipWithM_generate_r _ g = C.generateM knownSize (\idx -> Identity (twiddle (g idx)))

------------------------------------------------------------------------
-- Test tree

tests :: TT.TestTree
tests = TT.testGroup "Assignment RULES (inspection)"
  [ -- Identity: fmapFC/id
    $(inspectTest $ 'lhs_fmapFC_id ==~ 'rhs_fmapFC_id)
    -- Fusion rules: fmapFC/fmapFC
  , $(inspectTest $ 'lhs_fmapFC_fmapFC ==~ 'rhs_fmapFC_fmapFC)
    -- Fusion rules: traverseFC/fmapFC
  , $(inspectTest $ 'lhs_traverseFC_fmapFC ==~ 'rhs_traverseFC_fmapFC)
    -- Fusion rules: traverseFC/imapFC
  , $(inspectTest $ 'lhs_traverseFC_imapFC ==~ 'rhs_traverseFC_imapFC)
    -- Fusion rules: itraverseFC/fmapFC
  , $(inspectTest $ 'lhs_itraverseFC_fmapFC ==~ 'rhs_itraverseFC_fmapFC)
    -- Fusion rules: itraverseFC/imapFC
  , $(inspectTest $ 'lhs_itraverseFC_imapFC ==~ 'rhs_itraverseFC_imapFC)
    -- Fusion rules: imapFC/fmapFC
  , $(inspectTest $ 'lhs_imapFC_fmapFC ==~ 'rhs_imapFC_fmapFC)
    -- Fusion rules: imapFC/imapFC
  , $(inspectTest $ 'lhs_imapFC_imapFC ==~ 'rhs_imapFC_imapFC)
    -- Fusion rules: fmapFC/imapFC
  , $(inspectTest $ 'lhs_fmapFC_imapFC ==~ 'rhs_fmapFC_imapFC)
    -- Fusion rules: fmapFC/generate
  , $(inspectTest $ 'lhs_fmapFC_generate ==~ 'rhs_fmapFC_generate)
    -- Fusion rules: imapFC/generate
  , $(inspectTest $ 'lhs_imapFC_generate ==~ 'rhs_imapFC_generate)
    -- Fusion rules: traverseFC/generate
  , $(inspectTest $ 'lhs_traverseFC_generate ==~ 'rhs_traverseFC_generate)
    -- Fusion rules: traverseWithIndex/generate
  , $(inspectTest $ 'lhs_traverseWithIndex_generate ==~ 'rhs_traverseWithIndex_generate)
    -- Fusion rules: (!)/generate
  , $(inspectTest $ 'lhs_index_generate ==~ 'rhs_index_generate)
    -- Fusion rules: (!)/fmapFC
  , $(inspectTest $ 'lhs_index_fmapFC ==~ 'rhs_index_fmapFC)
    -- Fusion rules: (!)/imapFC
  , $(inspectTest $ 'lhs_index_imapFC ==~ 'rhs_index_imapFC)
    -- Fusion rules: zipWithM/fmapFC_l
  , $(inspectTest $ 'lhs_zipWithM_fmapFC_l ==~ 'rhs_zipWithM_fmapFC_l)
    -- Fusion rules: zipWithM/fmapFC_r
  , $(inspectTest $ 'lhs_zipWithM_fmapFC_r ==~ 'rhs_zipWithM_fmapFC_r)
    -- Fusion rules: fmapFC/traverseFC
    -- (no inspection test: fmap @Identity specialises to coerce before the rule
    --  can match; semantic correctness is covered by RulesSemantics)
    -- Fusion rules: zipWithM/generate_l
  , $(inspectTest $ 'lhs_zipWithM_generate_l ==~ 'rhs_zipWithM_generate_l)
    -- Fusion rules: zipWithM/generate_r
  , $(inspectTest $ 'lhs_zipWithM_generate_r ==~ 'rhs_zipWithM_generate_r)
  ]

#else

tests :: TT.TestTree
tests = TT.testGroup "Assignment RULES (inspection)" []

#endif
