{-|
Module           : Data.Parameterized.Context
Copyright        : (c) Galois, Inc 2014-2019
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This module reexports either "Data.Parameterized.Context.Safe"
or "Data.Parameterized.Context.Unsafe" depending on the
the unsafe-operations compile-time flag.

It also defines some utility typeclasses for transforming
between curried and uncurried versions of functions over contexts.

The 'Assignment' type is isomorphic to the
'Data.Parameterized.List' type, except 'Assignment's construct
lists from the right-hand side, and instead of using type-level
@'[]@-style lists, an 'Assignment' is indexed by a type-level
'Data.Parameterized.Context.Ctx'. The implementation of
'Assignment's is also more efficent than 'Data.Parameterized.List'
for lists of many elements, as it uses a balanced binary tree
representation rather than a linear-time list.

= Motivating example - the 'Data.Parameterized.Context.Assignment' type

For this example, we need the following extensions:

@
\{\-\# LANGUAGE DataKinds \#\-\}
\{\-\# LANGUAGE GADTs \#\-\}
\{\-\# LANGUAGE KindSignatures \#\-\}
\{\-\# LANGUAGE TypeOperators \#\-\}
@

We also require the following imports:

@
import Data.Parameterized
import Data.Parameterized.Context
import GHC.TypeLits
@

Suppose we have a bitvector type:

@
data BitVector (w :: Nat) :: * where
  BV :: NatRepr w -> Integer -> BitVector w
@

This type contains a 'Data.Parameterized.NatRepr.NatRepr', a value-level
representative of the vector width, and an 'Integer', containing the
actual value of the bitvector. We can create values of this type as
follows:

@
BV (knownNat @8) 0xAB
@

We can also create a smart constructor to handle the
'Data.Parameterized.NatRepr.NatRepr' automatically, when the width is known
from the type context:

@
bitVector :: KnownNat w => Integer -> BitVector w
bitVector x = BV knownNat x
@

Note that this does not check that the value can be represented in the
given number of bits; that is not important for this example.

If we wish to construct a list of @BitVector@s of a particular length,
we can do:

@
[bitVector 0xAB, bitVector 0xFF, bitVector 0] :: BitVector 8
@

However, what if we wish to construct a list of 'BitVector's of
different lengths? We could try:

@
[bitVector 0xAB :: BitVector 8, bitVector 0x1234 :: BitVector 16]
@

However, this gives us an error:

@
\<interactive\>:3:33: error:
    • Couldn't match type ‘16’ with ‘8’
      Expected type: BitVector 8
        Actual type: BitVector 16
    • In the expression: bitVector 0x1234 :: BitVector 16
      In the expression:
        [bitVector 0xAB :: BitVector 8, bitVector 0x1234 :: BitVector 16]
      In an equation for ‘it’:
          it
            = [bitVector 0xAB :: BitVector 8, bitVector 0x1234 :: BitVector 16]
@

A vanilla Haskell list cannot contain two elements of different types,
and even though the two elements here are both @BitVector@s, they do
not have the same type! One solution is to use the
'Data.Parameterized.Some.Some' type:

@
[Some (bitVector 0xAB :: BitVector 8), Some (bitVector 0x1234 :: BitVector 16)]
@

The type of the above expression is @[Some BitVector]@, which may be
perfectly acceptable. However, there is nothing in this type that
tells us what the widths of the bitvectors are. If we want to actually
track that information on the type level, we can use the 'Assignment'
type from this module.

@
empty :> (bitVector 0xAB :: BitVector 8) :> (bitVector 0x1234 :: BitVector 16)
@

The type of the above expression is @Assignment BitVector ((EmptyCtx
'::> 8) '::> 16)@ -- That is, a two-element list of @BitVector@s,
where the first element has width 8 and the second has width 16.

== Summary

In general, if we have a type constructor @Foo@ of kind @k -> *@ (in
our example, @Foo@ is just @BitVector@, and we want to create a list
of @Foo@s where the parameter @k@ varies, /and/ we wish to keep track
of what each value of @k@ is inside the list at compile time, we can
use the 'Data.Parameterized.Context.Assignment' type for this purpose.

-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Parameterized.Context
 (
#ifdef UNSAFE_OPS
    module Data.Parameterized.Context.Unsafe
#else
    module Data.Parameterized.Context.Safe
#endif
  , singleton
  , toVector
  , pattern (:>)
  , pattern Empty
  , decompose
  , Data.Parameterized.Context.null
  , Data.Parameterized.Context.init
  , Data.Parameterized.Context.last
  , Data.Parameterized.Context.view
  , Data.Parameterized.Context.take
  , forIndexM
  , generateSome
  , generateSomeM
  , fromList
  , traverseAndCollect
  , traverseWithIndex_

    -- * Context extension and embedding utilities
  , CtxEmbedding(..)
  , ExtendContext(..)
  , ExtendContext'(..)
  , ApplyEmbedding(..)
  , ApplyEmbedding'(..)
  , identityEmbedding
  , extendEmbeddingRightDiff
  , extendEmbeddingRight
  , extendEmbeddingBoth
  , appendEmbedding
  , ctxeSize
  , ctxeAssignment

    -- * Static indexing and lenses for assignments
  , Idx
  , field
  , natIndex
  , natIndexProxy
    -- * Currying and uncurrying for assignments
  , CurryAssignment
  , CurryAssignmentClass(..)
    -- * Size and Index values
  , size1, size2, size3, size4, size5, size6
  , i1of2, i2of2
  , i1of3, i2of3, i3of3
  , i1of4, i2of4, i3of4, i4of4
  , i1of5, i2of5, i3of5, i4of5, i5of5
  , i1of6, i2of6, i3of6, i4of6, i5of6, i6of6
  ) where

import           Control.Applicative (liftA2)
import           Control.Lens hiding (Index, (:>), Empty)
import           Data.Functor (void)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import           GHC.TypeLits (Nat, type (-))
import           Data.Monoid ((<>))

import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC

#ifdef UNSAFE_OPS
import           Data.Parameterized.Context.Unsafe
#else
import           Data.Parameterized.Context.Safe
#endif


-- | Create a single element context.
singleton :: f tp -> Assignment f (EmptyCtx ::> tp)
singleton = (empty :>)

-- |'forIndexM sz f' calls 'f' on indices '[0..sz-1]'.
forIndexM :: forall ctx m
           . Applicative m
          => Size ctx
          -> (forall tp . Index ctx tp -> m ())
          -> m ()
forIndexM sz f = forIndexRange 0 sz (\i r -> f i *> r) (pure ())

-- | Generate an assignment with some context type that is not known.
generateSome :: forall f
              . Int
             -> (Int -> Some f)
             -> Some (Assignment f)
generateSome n f = go n
  where go :: Int -> Some (Assignment f)
        go 0 = Some empty
        go i = (\(Some a) (Some e) -> Some (a `extend` e)) (go (i-1)) (f (i-1))

-- | Generate an assignment with some context type that is not known.
generateSomeM :: forall m f
              .  Applicative m
              => Int
              -> (Int -> m (Some f))
              -> m (Some (Assignment f))
generateSomeM n f = go n
  where go :: Int -> m (Some (Assignment f))
        go 0 = pure (Some empty)
        go i = (\(Some a) (Some e) -> Some (a `extend` e)) <$> go (i-1) <*> f (i-1)

-- | Convert the assignment to a vector.
toVector :: Assignment f tps -> (forall tp . f tp -> e) -> V.Vector e
toVector a f = V.create $ do
  vm <- MV.new (sizeInt (size a))
  forIndexM (size a) $ \i -> do
    MV.write vm (indexVal i) (f (a ! i))
  return vm
{-# INLINABLE toVector #-}

--------------------------------------------------------------------------------
-- Patterns

-- | Pattern synonym for the empty assignment
pattern Empty :: () => ctx ~ EmptyCtx => Assignment f ctx
pattern Empty <- (viewAssign -> AssignEmpty)
  where Empty = empty

infixl :>

-- | Pattern synonym for extending an assignment on the right
pattern (:>) :: () => ctx' ~ (ctx ::> tp) => Assignment f ctx -> f tp -> Assignment f ctx'
pattern (:>) a v <- (viewAssign -> AssignExtend a v)
  where a :> v = extend a v

-- The COMPLETE pragma was not defined until ghc 8.2.*
#if MIN_VERSION_base(4,10,0)
{-# COMPLETE (:>), Empty :: Assignment  #-}
#endif

--------------------------------------------------------------------------------
-- Views

-- | Return true if assignment is empty.
null :: Assignment f ctx -> Bool
null a =
  case viewAssign a of
    AssignEmpty -> True
    AssignExtend{} -> False

decompose :: Assignment f (ctx ::> tp) -> (Assignment f ctx, f tp)
decompose x = (Data.Parameterized.Context.init x, Data.Parameterized.Context.last x)

-- | Return assignment with all but the last block.
init :: Assignment f (ctx '::> tp) -> Assignment f ctx
init x =
  case viewAssign x of
    AssignExtend t _ -> t

-- | Return the last element in the assignment.
last :: Assignment f (ctx '::> tp) -> f tp
last x =
  case viewAssign x of
    AssignExtend _ e -> e

{-# DEPRECATED view "Use viewAssign or the Empty and :> patterns instead." #-}
-- | View an assignment as either empty or an assignment with one appended.
view :: forall f ctx . Assignment f ctx -> AssignView f ctx
view = viewAssign

take :: forall f ctx ctx'. Size ctx -> Size ctx' -> Assignment f (ctx <+> ctx') -> Assignment f ctx
take sz sz' asgn =
  let diff = appendDiff sz' in
  generate sz (\i -> asgn ! extendIndex' diff i)

--------------------------------------------------------------------------------
-- Context embedding.

-- | This datastructure contains a proof that the first context is
-- embeddable in the second.  This is useful if we want to add extend
-- an existing term under a larger context.

data CtxEmbedding (ctx :: Ctx k) (ctx' :: Ctx k)
  = CtxEmbedding { _ctxeSize       :: Size ctx'
                 , _ctxeAssignment :: Assignment (Index ctx') ctx
                 }

-- Alternate encoding?
-- data CtxEmbedding ctx ctx' where
--   EIdentity  :: CtxEmbedding ctx ctx
--   ExtendBoth :: CtxEmbedding ctx ctx' -> CtxEmbedding (ctx ::> tp) (ctx' ::> tp)
--   ExtendOne  :: CtxEmbedding ctx ctx' -> CtxEmbedding ctx (ctx' ::> tp)

ctxeSize :: Simple Lens (CtxEmbedding ctx ctx') (Size ctx')
ctxeSize = lens _ctxeSize (\s v -> s { _ctxeSize = v })

ctxeAssignment :: Lens (CtxEmbedding ctx1 ctx') (CtxEmbedding ctx2 ctx')
                       (Assignment (Index ctx') ctx1) (Assignment (Index ctx') ctx2)
ctxeAssignment = lens _ctxeAssignment (\s v -> s { _ctxeAssignment = v })

class ApplyEmbedding (f :: Ctx k -> *) where
  applyEmbedding :: CtxEmbedding ctx ctx' -> f ctx -> f ctx'

class ApplyEmbedding' (f :: Ctx k -> k' -> *) where
  applyEmbedding' :: CtxEmbedding ctx ctx' -> f ctx v -> f ctx' v

class ExtendContext (f :: Ctx k -> *) where
  extendContext :: Diff ctx ctx' -> f ctx -> f ctx'

class ExtendContext' (f :: Ctx k -> k' -> *) where
  extendContext' :: Diff ctx ctx' -> f ctx v -> f ctx' v

instance ApplyEmbedding' Index where
  applyEmbedding' ctxe idx = (ctxe ^. ctxeAssignment) ! idx

instance ExtendContext' Index where
  extendContext' = extendIndex'

-- -- This is the inefficient way of doing things.  A better way is to
-- -- just have a map between indices.
-- applyEmbedding :: CtxEmbedding ctx ctx'
--                -> Index ctx tp -> Index ctx' tp
-- applyEmbedding ctxe idx = (ctxe ^. ctxeAssignment) ! idx

identityEmbedding :: Size ctx -> CtxEmbedding ctx ctx
identityEmbedding sz = CtxEmbedding sz (generate sz id)

-- emptyEmbedding :: CtxEmbedding EmptyCtx EmptyCtx
-- emptyEmbedding = identityEmbedding knownSize

extendEmbeddingRightDiff :: forall ctx ctx' ctx''.
                            Diff ctx' ctx''
                            -> CtxEmbedding ctx ctx'
                            -> CtxEmbedding ctx ctx''
extendEmbeddingRightDiff diff (CtxEmbedding sz' assgn) = CtxEmbedding (extSize sz' diff) updated
  where
    updated :: Assignment (Index ctx'') ctx
    updated = fmapFC (extendIndex' diff) assgn

extendEmbeddingRight :: CtxEmbedding ctx ctx' -> CtxEmbedding ctx (ctx' ::> tp)
extendEmbeddingRight = extendEmbeddingRightDiff knownDiff

appendEmbedding :: Size ctx -> Size ctx' -> CtxEmbedding ctx (ctx <+> ctx')
appendEmbedding sz sz' = CtxEmbedding (addSize sz sz') (generate sz (extendIndex' diff))
  where
  diff = appendDiff sz'

extendEmbeddingBoth :: forall ctx ctx' tp. CtxEmbedding ctx ctx' -> CtxEmbedding (ctx ::> tp) (ctx' ::> tp)
extendEmbeddingBoth ctxe = updated & ctxeAssignment %~ flip extend (nextIndex (ctxe ^. ctxeSize))
  where
    updated :: CtxEmbedding ctx (ctx' ::> tp)
    updated = extendEmbeddingRight ctxe

--------------------------------------------------------------------------------
-- Static indexing based on type-level naturals

-- | Get a lens for an position in an 'Assignment' by zero-based, left-to-right position.
-- The position must be specified using @TypeApplications@ for the @n@ parameter.
field :: forall n ctx f r. Idx n ctx r => Lens' (Assignment f ctx) (f r)
field = ixF' (natIndex @n)

-- | Constraint synonym used for getting an 'Index' into a 'Ctx'.
-- @n@ is the zero-based, left-counted index into the list of types
-- @ctx@ which has the type @r@.
type Idx n ctx r = (ValidIx n ctx, Idx' (FromLeft ctx n) ctx r)

-- | Compute an 'Index' value for a particular position in a 'Ctx'. The
-- @TypeApplications@ extension will be needed to disambiguate the choice
-- of the type @n@.
natIndex :: forall n ctx r. Idx n ctx r => Index ctx r
natIndex = natIndex' @_ @(FromLeft ctx n)

-- | This version of 'natIndex' is suitable for use without the @TypeApplications@
-- extension.
natIndexProxy :: forall n ctx r proxy. Idx n ctx r => proxy n -> Index ctx r
natIndexProxy _ = natIndex @n

------------------------------------------------------------------------
-- Implementation
------------------------------------------------------------------------

-- | Class for computing 'Index' values for positions in a 'Ctx'.
class KnownContext ctx => Idx' (n :: Nat) (ctx :: Ctx k) (r :: k) | n ctx -> r where
  natIndex' :: Index ctx r

-- | Base-case
instance KnownContext xs => Idx' 0 (xs '::> x) x where
  natIndex' = lastIndex knownSize

-- | Inductive-step
instance {-# Overlaps #-} (KnownContext xs, Idx' (n-1) xs r) =>
  Idx' n (xs '::> x) r where

  natIndex' = skipIndex (natIndex' @_ @(n-1))


--------------------------------------------------------------------------------
-- * CurryAssignment

-- | This type family is used to define currying\/uncurrying operations
-- on assignments.  It is best understood by seeing its evaluation on
-- several examples:
--
-- > CurryAssignment EmptyCtx f x = x
-- > CurryAssignment (EmptyCtx ::> a) f x = f a -> x
-- > CurryAssignment (EmptyCtx ::> a ::> b) f x = f a -> f b -> x
-- > CurryAssignment (EmptyCtx ::> a ::> b ::> c) f x = f a -> f b -> f c -> x
type family CurryAssignment (ctx :: Ctx k) (f :: k -> *) (x :: *) :: * where
   CurryAssignment EmptyCtx    f x = x
   CurryAssignment (ctx ::> a) f x = CurryAssignment ctx f (f a -> x)

-- | This class implements two methods that witness the isomorphism between
--   curried and uncurried functions.
class CurryAssignmentClass (ctx :: Ctx k) where

  -- | Transform a function that accepts an assignment into one with a separate
  --   variable for each element of the assignment.
  curryAssignment   :: (Assignment f ctx -> x) -> CurryAssignment ctx f x

  -- | Transform a curried function into one that accepts an assignment value.
  uncurryAssignment :: CurryAssignment ctx f x -> (Assignment f ctx -> x)

instance CurryAssignmentClass EmptyCtx where
  curryAssignment k = k empty
  uncurryAssignment k _ = k

instance CurryAssignmentClass ctx => CurryAssignmentClass (ctx ::> a) where
  curryAssignment k = curryAssignment (\asgn a -> k (asgn :> a))
  uncurryAssignment k asgn =
    case viewAssign asgn of
      AssignExtend asgn' x -> uncurryAssignment k asgn' x

-- | Create an assignment from a list of values.
fromList :: [Some f] -> Some (Assignment f)
fromList = go empty
  where go :: Assignment f ctx -> [Some f] -> Some (Assignment f)
        go prev [] = Some prev
        go prev (Some g:next) = (go $! prev `extend` g) next


newtype Collector m w a = Collector { runCollector :: m w }
instance Functor (Collector m w) where
  fmap _ (Collector x) = Collector x
instance (Applicative m, Monoid w) => Applicative (Collector m w) where
  pure _ = Collector (pure mempty)
  Collector x <*> Collector y = Collector (liftA2 (<>) x y)

-- | Visit each of the elements in an @Assignment@ in order
--   from left to right and collect the results using the provided @Monoid@.
traverseAndCollect ::
  (Monoid w, Applicative m) =>
  (forall tp. Index ctx tp -> f tp -> m w) ->
  Assignment f ctx ->
  m w
traverseAndCollect f =
  runCollector . traverseWithIndex (\i x -> Collector (f i x))

-- | Visit each of the elements in an @Assignment@ in order
--   from left to right, executing an action with each.
traverseWithIndex_ :: Applicative m
                   => (forall tp . Index ctx tp -> f tp -> m ())
                   -> Assignment f ctx
                   -> m ()
traverseWithIndex_ f = void . traverseAndCollect f

--------------------------------------------------------------------------------
-- Size and Index values

size1 :: Size (EmptyCtx ::> a)
size1 = incSize zeroSize

size2 :: Size (EmptyCtx ::> a ::> b)
size2 = incSize size1

size3 :: Size (EmptyCtx ::> a ::> b ::> c)
size3 = incSize size2

size4 :: Size (EmptyCtx ::> a ::> b ::> c ::> d)
size4 = incSize size3

size5 :: Size (EmptyCtx ::> a ::> b ::> c ::> d ::> e)
size5 = incSize size4

size6 :: Size (EmptyCtx ::> a ::> b ::> c ::> d ::> e ::> f)
size6 = incSize size5

i1of2 :: Index (EmptyCtx ::> a ::> b) a
i1of2 = skipIndex baseIndex

i2of2 :: Index (EmptyCtx ::> a ::> b) b
i2of2 = nextIndex size1

i1of3 :: Index (EmptyCtx ::> a ::> b ::> c) a
i1of3 = skipIndex i1of2

i2of3 :: Index (EmptyCtx ::> a ::> b ::> c) b
i2of3 = skipIndex i2of2

i3of3 :: Index (EmptyCtx ::> a ::> b ::> c) c
i3of3 = nextIndex size2

i1of4 :: Index (EmptyCtx ::> a ::> b ::> c ::> d) a
i1of4 = skipIndex i1of3

i2of4 :: Index (EmptyCtx ::> a ::> b ::> c ::> d) b
i2of4 = skipIndex i2of3

i3of4 :: Index (EmptyCtx ::> a ::> b ::> c ::> d) c
i3of4 = skipIndex i3of3

i4of4 :: Index (EmptyCtx ::> a ::> b ::> c ::> d) d
i4of4 = nextIndex size3

i1of5 :: Index (EmptyCtx ::> a ::> b ::> c ::> d ::> e) a
i1of5 = skipIndex i1of4

i2of5 :: Index (EmptyCtx ::> a ::> b ::> c ::> d ::> e) b
i2of5 = skipIndex i2of4

i3of5 :: Index (EmptyCtx ::> a ::> b ::> c ::> d ::> e) c
i3of5 = skipIndex i3of4

i4of5 :: Index (EmptyCtx ::> a ::> b ::> c ::> d ::> e) d
i4of5 = skipIndex i4of4

i5of5 :: Index (EmptyCtx ::> a ::> b ::> c ::> d ::> e) e
i5of5 = nextIndex size4

i1of6 :: Index (EmptyCtx ::> a ::> b ::> c ::> d ::> e ::> f) a
i1of6 = skipIndex i1of5

i2of6 :: Index (EmptyCtx ::> a ::> b ::> c ::> d ::> e ::> f) b
i2of6 = skipIndex i2of5

i3of6 :: Index (EmptyCtx ::> a ::> b ::> c ::> d ::> e ::> f) c
i3of6 = skipIndex i3of5

i4of6 :: Index (EmptyCtx ::> a ::> b ::> c ::> d ::> e ::> f) d
i4of6 = skipIndex i4of5

i5of6 :: Index (EmptyCtx ::> a ::> b ::> c ::> d ::> e ::> f) e
i5of6 = skipIndex i5of5

i6of6 :: Index (EmptyCtx ::> a ::> b ::> c ::> d ::> e ::> f) f
i6of6 = nextIndex size5
