{-|
Description : A solver for type-level equations in monoids
Copyright   : (c) Galois, Inc 2021
Maintainer  : Langston Barrett

Implementation of section 6 of \"A well-known representation of monoids and its
application to the function \'vector reverse\'\" by Wouter Swierstra.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Parameterized.MonoidSolver
  ( solve
  , solveNat
  ) where

import Data.Kind (Type)
import Data.Proxy (Proxy(..))
import Data.Type.Equality (type (:~:)(Refl))
import GHC.TypeLits (Nat)

import Data.Parameterized.NatRepr (NatRepr, type (+), plusAssoc)

-- | 'Op' corresponds to @Add@ from the paper.
type family Op k (m1 :: k) (m2 :: k) :: k
-- | 'Unit' corresponds to @Add@ from the paper.
type family Unit k :: k

type instance Op Nat n1 n2 = n1 + n2
type instance Unit Nat = 0

-- | Type level only
data MonoidExpr k
  = EUnit
  | EVar k
  | EOp (MonoidExpr k) (MonoidExpr k)

data MERepr (k :: Type) (f :: k -> Type) (me :: MonoidExpr k) where
  EUnitRepr :: MERepr k f 'EUnit
  EVarRepr :: f n -> MERepr k f ('EVar n)
  EOpRepr ::
    MERepr k f me1 ->
    MERepr k f me2 ->
    MERepr k f ('EOp me1 me2)

type family Eval (k :: Type) (me :: MonoidExpr k) :: k where
  Eval k 'EUnit = Unit k
  Eval k ('EVar m) = m
  Eval k ('EOp me1 me2) = Op k (Eval k me1) (Eval k me2)

-- | Defunctionalization - inspired by \"singletons\", and with a similar naming
-- scheme
data TyFun a b
type a ~> b = TyFun a b -> Type
type family Apply (f :: a ~> b) (x :: a) :: b

data IdSym1 :: MonoidExpr m ~> MonoidExpr m
data EOpSym0 :: MonoidExpr m ~> (MonoidExpr m ~> MonoidExpr m)
data EOpSym1 (me :: MonoidExpr m) :: MonoidExpr m ~> MonoidExpr m
data ComposeDiffSym0 :: MonoidExpr m ~> (MonoidExpr m ~> (MonoidExpr m ~> MonoidExpr m))
data ComposeDiffSym1 (me :: MonoidExpr m) :: MonoidExpr m ~> (MonoidExpr m ~> MonoidExpr m)
data ComposeDiffSym2 (me1 :: MonoidExpr m) (me2 :: MonoidExpr m) :: MonoidExpr m ~> MonoidExpr m

type instance Apply IdSym1 me = me
type instance Apply EOpSym0 me = EOpSym1 me
type instance Apply (EOpSym1 me1) (me2 :: MonoidExpr m) = 'EOp me1 me2
-- TODO: generalize to (higher-order) compose?
type instance Apply ComposeDiffSym0 me = ComposeDiffSym1 me
type instance Apply (ComposeDiffSym1 me1) me2 = ComposeDiffSym2 me1 me2
type instance Apply (ComposeDiffSym2 me1 me2) me3 = Apply (Diff me1) (Apply (Diff me2) me3)

-- | The \"difference list\"/Caley embedding representation of monoid
-- expressions, corresponds to the bracket operator in the paper.
type family Diff (me :: MonoidExpr m) :: MonoidExpr m ~> MonoidExpr m where
  Diff ('EOp me1 me2) = ComposeDiffSym2 me1 me2
  Diff 'EUnit = IdSym1
  Diff ('EVar m) = EOpSym1 ('EVar m)

-- | 'UnDiff' corresponds to "reify" from the paper.
type family UnDiff (diff :: MonoidExpr m ~> MonoidExpr m) :: MonoidExpr m where
  UnDiff diff = Apply diff 'EUnit

type family Normalize (me :: MonoidExpr m) :: MonoidExpr m where
  Normalize me = UnDiff (Diff me)

-- | Note on termination: The one recursive call to this function is strictly
-- decreasing on its first argument. This function is mutually recursive with
-- 'normalizeSound' and recursive calls to that function are made on the second
-- argument, but calls to this function *from* 'normalizeSound' are on strict
-- subexpressions of its argument.
normalizeLemma ::
  forall k f me1 me2.
  (forall proxy n. proxy n -> f (Op k (Unit k) n) :~: f n) ->
  (forall proxy n. proxy n -> f (Op k n (Unit k)) :~: f n) ->
  (forall proxy n m l. proxy n -> proxy m -> proxy l -> f (Op k n (Op k m l)) :~: f (Op k (Op k n m) l)) ->
  MERepr k f me1 ->
  MERepr k f me2 ->
  f (Eval k (Apply (Diff me1) (Apply (Diff me2) 'EUnit))) :~:
    f (Op k (Eval k me1) (Eval k me2))
normalizeLemma idl idr assoc mer1 mer2 =
  case mer1 of
    EUnitRepr ->
      case idl (Proxy :: Proxy (Eval k me2)) of
        Refl ->
          case norm mer2 of
            Refl -> Refl
    EVarRepr {} ->
      case norm mer2 of
        Refl -> Refl
    EOpRepr (mer1' :: MERepr k f me1') (mer2' :: MERepr k f me2') ->
      case normalizeLemma idl idr assoc mer1' (EOpRepr mer2' mer2) of
        Refl ->
              assoc (Proxy :: Proxy (Eval k me1')) (Proxy :: Proxy (Eval k me2')) (Proxy :: Proxy (Eval k me2))
  where
    norm :: MERepr k f me -> f (Eval k (Normalize me)) :~: f (Eval k me)
    norm = normalizeSound idl idr assoc

normalizeSound ::
  (forall proxy n. proxy n -> f (Op k (Unit k) n) :~: f n) ->
  (forall proxy n. proxy n -> f (Op k n (Unit k)) :~: f n) ->
  (forall proxy n m l. proxy n -> proxy m -> proxy l -> f (Op k n (Op k m l)) :~: f (Op k (Op k n m) l)) ->
  MERepr k f me ->
  f (Eval k (Normalize me)) :~: f (Eval k me)
normalizeSound idl idr assoc =
  \case
    EUnitRepr -> Refl
    EVarRepr (sing :: f n) -> idr sing
    EOpRepr (mer1 :: MERepr k f me1) (mer2 :: MERepr k f me2) ->
      normalizeLemma idl idr assoc mer1 mer2

solve ::
  (forall proxy n. proxy n -> f (Op k (Unit k) n) :~: f n) ->
  (forall proxy n. proxy n -> f (Op k n (Unit k)) :~: f n) ->
  (forall proxy n m l. proxy n -> proxy m -> proxy l -> f (Op k n (Op k m l)) :~: f (Op k (Op k n m) l)) ->
  MERepr k f me1 ->
  MERepr k f me2 ->
  f (Eval k (Normalize me1)) :~: f (Eval k (Normalize me2)) ->
  f (Eval k me1) :~: f (Eval k me2)
solve idl idr assoc repr1 repr2 Refl =
  case (normalizeSound idl idr assoc repr1, normalizeSound idl idr assoc repr2) of
    (Refl, Refl) -> Refl

solveNat ::
  MERepr Nat proxy me1 ->
  MERepr Nat proxy me2 ->
  proxy (Eval Nat (Normalize me1)) :~: proxy (Eval Nat (Normalize me2)) ->
  proxy (Eval Nat me1) :~: proxy (Eval Nat me2)
solveNat =
  solve
    (const Refl)
    (const Refl)
    (\proxy1 proxy2 proxy3 ->
       case plusAssoc proxy1 proxy2 proxy3 of
         Refl -> Refl)

----------------------------------------------------------------------
-- Examples
--

_ex ::
  NatRepr n ->
  NatRepr m ->
  NatRepr l ->
  NatRepr (n + (m + l)) :~: NatRepr ((n + m) + l)
_ex n m l =
  let e1 = EOpRepr (EVarRepr n) (EOpRepr (EVarRepr m) (EVarRepr l))
      e2 = EOpRepr (EOpRepr (EVarRepr n) (EVarRepr m)) (EVarRepr l)
  in solveNat e1 e2 Refl

assoc5 ::
  proxy a ->
  proxy b ->
  proxy c ->
  proxy d ->
  proxy e ->
  proxy (a + (b + (c + (d + e)))) :~: proxy ((((a + b) + c) + d) + e)
assoc5 a b c d e =
  let e1 = EOpRepr (EVarRepr a) (EOpRepr (EVarRepr b) (EOpRepr (EVarRepr c) (EOpRepr (EVarRepr d) (EVarRepr e))))
      e2 = EOpRepr (EOpRepr (EOpRepr (EOpRepr (EVarRepr a) (EVarRepr b)) (EVarRepr c)) (EVarRepr d)) (EVarRepr e)
  in solveNat e1 e2 Refl

_assoc5Nat ::
  proxy a ->
  proxy b ->
  proxy c ->
  proxy d ->
  proxy e ->
  (a + (b + (c + (d + e)))) :~: ((((a + b) + c) + d) + e)
_assoc5Nat a b c d e =
  case assoc5 a b c d e of
    Refl -> Refl

-- Doesn't typecheck:
--
-- _assoc5Nat' ::
--   proxy a ->
--   proxy b ->
--   proxy c ->
--   proxy d ->
--   proxy e ->
--   (a + (b + (c + (d + e)))) :~: ((((a + b) + c) + d) + e)
-- _assoc5Nat' _ _ _ _ _ = Refl
