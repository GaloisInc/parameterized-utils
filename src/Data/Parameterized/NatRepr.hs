{-|
Copyright        : (c) Galois, Inc 2014-2018
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines a type 'NatRepr' for representing a type-level natural
at runtime.  This can be used to branch on a type-level value.  For
each @n@, @NatRepr n@ contains a single value containing the value
@n@.  This can be used to help use type-level variables on code
with data dependendent types.

The @TestEquality@ and @DecidableEq@ instances for 'NatRepr'
are implemented using 'unsafeCoerce', as is the `isZeroNat` function. This
should be typesafe because we maintain the invariant that the integer value
contained in a NatRepr value matches its static type.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeApplications #-}
#if MIN_VERSION_base(4,9,0)
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
#endif
#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE NoStarIsType #-}
#endif
module Data.Parameterized.NatRepr
  ( NatRepr
  , natValue
  , intValue
  , knownNat
  , withKnownNat
  , IsZeroNat(..)
  , isZeroNat
  , isZeroOrGT1
  , NatComparison(..)
  , compareNat
  , decNat
  , predNat
  , incNat
  , addNat
  , subNat
  , divNat
  , halfNat
  , withDivModNat
  , natMultiply
  , someNat
  , mkNatRepr
  , maxNat
  , natRec
  , natRecStrong
  , natRecBounded
  , natForEach
  , natFromZero
  , NatCases(..)
  , testNatCases
    -- * Strict order
  , lessThanIrreflexive
  , lessThanAsymmetric
    -- * Bitvector utilities
  , widthVal
  , minUnsigned
  , maxUnsigned
  , minSigned
  , maxSigned
  , toUnsigned
  , toSigned
  , unsignedClamp
  , signedClamp
    -- * LeqProof
  , LeqProof(..)
  , decideLeq
  , testLeq
  , testStrictLeq
  , leqRefl
  , leqTrans
  , leqAdd2
  , leqSub2
  , leqMulCongr
    -- * LeqProof combinators
  , leqProof
  , withLeqProof
  , isPosNat
  , leqAdd
  , leqSub
  , leqMulPos
  , leqAddPos
  , addIsLeq
  , withAddLeq
  , addPrefixIsLeq
  , withAddPrefixLeq
  , addIsLeqLeft1
  , dblPosIsPos
  , leqMulMono
    -- * Arithmetic proof
  , plusComm
  , mulComm
  , plusMinusCancel
  , minusPlusCancel
  , addMulDistribRight
  , withAddMulDistribRight
  , withSubMulDistribRight
  , mulCancelR
  , mul2Plus
  , lemmaMul
    -- * Re-exports typelits basics
--  , NatK
  , type (+)
  , type (-)
  , type (*)
  , type (<=)
  , Equality.TestEquality(..)
  , (Equality.:~:)(..)
  , Data.Parameterized.Some.Some
  ) where

import Data.Type.Equality as Equality
import GHC.TypeLits

import Data.Parameterized.NatRepr.Internal
import Data.Parameterized.Some
