{-# LANGUAGE CPP #-}
#define Induction
{-# LANGUAGE GADTs, KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables, Rank2Types, InstanceSigs, ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-} -- experiment
{-# LANGUAGE UndecidableInstances #-}  -- See below

#include "AbsTy.inc"
AbsTyPragmas

#ifdef Induction
{-# LANGUAGE ConstraintKinds, PatternGuards #-}
#endif

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.RTree
-- Copyright   :  (c) 2012 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Right-folded trees. For now, just binary.
----------------------------------------------------------------------

module Circat.RTree
  ( RTree(..),Tree,unL,toB,unB,inB,inB2,fromList
  , tree0, tree1, tree2, tree3, tree4, tree5, tree6
  , get, (!), subtree, update
  , butterfly, butterfly'
  , tmerge, bottomSplit
  -- Temporary:
  , asG'
  ) where

import Prelude hiding (id,(.),uncurry,zipWith,reverse)

-- import Data.Monoid (Monoid(..))
-- import Data.Functor ((<$),(<$>))
import Control.Applicative ({-Applicative(..),-}liftA2)
import Control.Monad (join)
-- import Data.Foldable
-- import Data.Traversable (Traversable(..))
import Data.Typeable (Typeable)
import Test.QuickCheck (Gen,Arbitrary(..),CoArbitrary(..))
import GHC.Generics (Generic1(..),Par1(..),(:.:)(..))

#ifdef Induction
import Data.Constraint (Dict(..))
#endif

import TypeUnary.Nat hiding ((:*:))
import TypeUnary.Vec (Vec(..))

import Circat.Misc (Unop,(<~),Reversible(..),transpose,inTranspose,Sized(..),genericSize,twoNat)
import Circat.Show (showsApp1)
import Circat.Category
-- import Circat.Classes
import Circat.Pair hiding (get,update)
import qualified Circat.Pair as P
-- import Circat.State (pureState,StateFun,StateExp)
-- import Circat.Rep
-- import Circat.If
import Circat.Scan

AbsTyImports

-- TODO: Use the generalization from numbers-vectors-trees, factoring out Pair

data RTree :: * -> * -> * where
  L :: a -> Tree Z a
  B :: Pair (Tree n a) -> Tree (S n) a

type Tree = RTree

instance Generic1 (Tree Z) where
  type Rep1 (Tree Z) = Par1
  from1 = Par1 . unL
  to1   = L . unPar1

instance Generic1 (Tree (S n)) where
  type Rep1 (Tree (S n)) = Pair :.: Tree n
  from1 = Comp1 . unB
  to1   = B . unComp1

deriving instance Eq a => Eq (Tree n a)
deriving instance Typeable Tree

instance (IsNat n, Arbitrary a) => Arbitrary (Tree n a) where
  arbitrary = arb' nat
   where
     arb' :: Nat m -> Gen (Tree m a)
     arb' Zero     = L <$> arbitrary
     arb' (Succ _) = B <$> arbitrary
  shrink = shrink' nat
   where
     shrink' :: Nat m -> Tree m a -> [Tree m a]
     shrink' Zero     = \ (L a ) -> L <$> shrink a
     shrink' (Succ _) = \ (B ts) -> B <$> shrink ts

instance (CoArbitrary a) => CoArbitrary (Tree n a) where
  coarbitrary (L a ) = coarbitrary a
  coarbitrary (B ts) = coarbitrary ts

instance HasRep (Tree Z a) where
  type Rep (Tree Z a) = a
  repr (L a) = a
  abst a = L a

#if 1
instance HasRep (Tree (S n) a) where
  type Rep (Tree (S n) a) = Pair (Tree n a)
  repr (B ts) = ts
  abst ts = B ts
#else
-- Two steps:
-- type instance Rep (Tree (S n) a) = Rep (Pair (Tree n a))
type instance Rep (Tree (S n) a) = (Tree n a , Tree n a)
instance HasRep (Tree (S n) a) where
  repr (B ts) = repr ts
  abst ts = B (abst ts)
#endif

instance Ord a => Ord (Tree n a) where
  compare (L a ) = \ (L b)  -> a  `compare` b 
  compare (B us) = \ (B vs) -> us `compare` vs

-- TODO: Maybe use IsNat for Ord

instance Show a => Show (Tree n a) where
  showsPrec p (L a)  = showsApp1 "L" p a
  showsPrec p (B ts) = showsApp1 "B" p ts

toL :: a -> Tree Z a
toL a     = L a
unL :: Tree Z a -> a
unL (L a) = a

toB :: Pair (Tree n a) -> Tree (S n) a
toB p     = (B p)
unB :: Tree (S n) a -> Pair (Tree n a)
unB (B p) = p

inL :: (a -> b) -> (Tree Z a -> Tree Z b)
inL = toL <~ unL

inB :: (Pair (Tree m a) -> Pair (Tree n b))
    -> (Tree (S m) a -> Tree (S n) b)
inB = toB <~ unB

inL2 :: (a -> b -> c) -> (Tree Z a -> Tree Z b -> Tree Z c)
inL2 = inL <~ unL

inB2 :: (Pair (Tree m a) -> Pair (Tree n b) -> Pair (Tree o c))
     -> (Tree (S m) a -> Tree (S n) b -> Tree (S o) c)
inB2 = inB <~ unB

-- instance IsNat n => Functor (Tree n) where
--   fmap = fmap' nat
--    where
--      fmap' :: Nat m -> (a -> b) -> (Tree m a -> Tree m b)
--      fmap' Zero     = inL
--      fmap' (Succ n) = inB . fmap . fmap' n
--   {-# INLINE fmap #-}

instance Functor (Tree n) where
  fmap f (L a ) = L (f a)
  fmap f (B ts) = B ((fmap.fmap) f ts)
  {-# INLINE fmap #-}

-- TODO: Categorical generalization (easy)

instance IsNat n => Applicative (Tree n) where
  -- pure a = a <$ units nat
  pure = pureT nat
  (<*>)  = apT
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

apT :: Tree m (a -> b) -> Tree m a -> Tree m b
apT (L f ) = inL (\ x -> f x)
apT (B fs) = inB (\ xs -> liftA2 apT fs xs)
{-# INLINE apT #-}

-- units :: Nat n -> Tree n ()
-- units Zero     = L ()
-- units (Succ n) = B (pure (units n))
-- {-# INLINE units #-}

-- pureT :: Nat n -> a -> Tree n a
-- pureT Zero     = L
-- pureT (Succ m) = B . pure . pureT m
-- {- INLINE pureT -}

-- The definition above doesn't yield an unfolding, but the following does.

pureT :: Nat n -> a -> Tree n a
pureT Zero     a = L a
pureT (Succ m) a = B (pure (pureT m a))
{-# INLINE pureT #-}

#if 1

instance Foldable (Tree n) where
  foldMap f (L a ) = f a
  foldMap f (B ts) = (foldMap.foldMap) f ts
  {-# INLINE foldMap #-}

instance Traversable (Tree n) where
  traverse f (L a ) = L <$> f a
  traverse f (B ts) = B <$> (traverse.traverse) f ts
  {-# INLINE traverse #-}

instance IsNat n => Monad (Tree n) where
  return = pure
  m >>= f = joinT (fmap f m)
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}

joinT :: Tree n (Tree n a) -> Tree n a
joinT (L t)  = t
joinT (B ts) = B . fmap joinT . join . fmap sequenceA . (fmap . fmap) unB $ ts

#if 0

-- Type derivation:
B ts :: Tree (S n) (Tree (S n) a)
ts :: Pair (Tree n (Tree (S n) a))
(fmap.fmap) unB ts :: Pair (Tree n (Pair (Tree n a)))
sequenceA <$> ((fmap.fmap) unB ts) :: Pair (Pair (Tree n (Tree n a)))
joinT' (sequenceA <$> ((fmap.fmap) unB ts)) :: Pair (Tree n (Tree n a))
joinT' <$> joinT' (sequenceA <$> ((fmap.fmap) unB ts)) :: Pair (Tree n a)
B (joinT' <$> joinT' (sequenceA <$> ((fmap.fmap) unB ts))) :: Tree (S n) a

#endif

#else

instance IsNat n => Foldable (Tree n) where
  foldMap = foldMap' nat

foldMap' :: Monoid o => Nat m -> (a -> o) -> Tree m a -> o
foldMap' Zero     f = f . unL
foldMap' (Succ m) f = foldMap (foldMap' m f) . unB
{-# INLINE foldMap' #-}

instance IsNat n => Traversable (Tree n) where
  traverse :: forall a f b. Applicative f => (a -> f b) -> Tree n a -> f (Tree n b)
  traverse f = traverse' nat
   where
     traverse' :: Nat m -> Tree m a -> f (Tree m b)
--      traverse' Zero = \ (L a ) -> L <$> f a
--      traverse' (Succ m) = \ (B ts) -> B <$> traverse (traverse' m) ts
     traverse' Zero     = fmap L . f . unL
     traverse' (Succ m) = fmap B . traverse (traverse' m) . unB
  {-# INLINE traverse #-}

instance IsNat n => Monad (Tree n) where
  return = pure
  m >>= f = joinT nat (fmap f m)
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}

joinT :: Nat n -> Tree n (Tree n a) -> Tree n a
-- joinT Zero = \ (L t) -> t
-- joinT (Succ m) = \ (B ts) -> B . fmap (joinT m) . join . fmap sequenceA . (fmap . fmap) unB $ ts
joinT Zero = unL
joinT (Succ m) = B . fmap (joinT m) . join . fmap sequenceA . (fmap . fmap) unB . unB
#endif

{-# INLINE joinT #-}

-- TODO: Revisit joinT. Make sure it suits Tree as trie, matching the function
-- (reader) monad. Should be derivable.

-- TODO: fmap with IsNat

{-

-- joinT (B ts) = B . joinMMT . (fmap . fmap) unB $ ts

-- TODO: Generalize this construction past (->). Rework def without sequenceA.
-- TODO: Generalize past Tree. Use pack/unpack?

-- TODO: joinT' to use inB

joinT' :: Nat n -> Tree n (Tree n a) -> Tree n a
joinT' Zero = unL
joinT' (Succ m) = B . fmap (joinT' m) . join . fmap sequenceA . unB . fmap unB

-- ts :: P (Tree m (Tree (S m) a))

-- (fmap . fmap) unB $ ts :: P (Tree m (P (Tree m a)))

-- fmap sequenceA $ '' :: P (P (Tree m (Tree m a)))
-- join $ '' :: P (Tree m (Tree m a))
-- fmap join $ '' :: P (Tree m a)
-- B $ '' :: Tree (S m) a

--   B
-- . fmap join
-- . join
-- . fmap sequenceA
-- . (fmap . fmap) unB

-}

-- Bottom-up merge, preserving ordering
tmerge :: Tree n (Pair a) -> Tree (S n) a
tmerge (L (a :# b)) = B (L a :# L b)
tmerge (B ts)       = B (tmerge <$> ts)

-- ts :: Pair (Tree m (Pair a))
-- pmerge <$> ts : Pair (Tree (S m) a)
-- B (pmerge <$> ts) : Tree (S (S m)) a

butterfly :: (IsNat n, Ord a) => Unop (Pair a) -> Unop (Tree n a)
butterfly = butterfly' nat

butterfly' :: Ord a => Nat n -> Unop (Pair a) -> Unop (Tree n a)
butterfly' Zero     _ = id
butterfly' (Succ m) f = inB (fmap (butterfly' m f) . (inTranspose.fmap) f)
{-# INLINE butterfly' #-}

#if 0
butterfly' (Succ m) f = B . fmap (butterfly' m f) . transpose . fmap f . transpose . unB

unB                   :: RTree (S m) a -> Pair (RTree m a)
transpose             :: Pair (RTree m a) ->  RTree m (Pair a)
fmap f                :: RTree m (Pair a) -> RTree m (Pair a)
transpose             :: RTree m (Pair a) -> Pair (RTree m a)
fmap (butterfly' m f) :: Pair (RTree m a) -> Pair (RTree m a)
B                     :: Pair (RTree m a) -> RTree (S m) a
#endif

-- Equivalently,
-- 
--   butterfly' (Succ m) f = inB $ fmap (butterfly' m f) . inTranspose (fmap f)
--     
--   butterfly' (Succ m) f = inB $ \ ts -> butterfly' m f <$> inTranspose (fmap f) ts
--     
--   butterfly' (Succ m) f = \ (B ts) -> B (butterfly' m f <$> inTranspose (fmap f) ts)
--     
--   butterfly' (Succ m) f = \ (B ts) -> B (butterfly' m f <$> transpose (f <$> transpose ts))

-- Split into evens & odds
bottomSplit :: IsNat n => Tree (S n) a -> Pair (Tree n a)
bottomSplit = split' nat
 where
   split' :: Nat n -> Tree (S n) a -> Pair (Tree n a)
   split' Zero     = unB
   split' (Succ m) = fmap B . transpose . fmap (split' m) . unB
   {-# INLINE split' #-}

--    split' Zero     =  \ (B (L a :# L b)) -> L a :# L b
--    split' (Succ m) = \ (B ts) -> B <$> ptranspose (split' m <$> ts)

-- Maybe I really want Tree (S n) a -> Tree n (Pair a)

-- fmap (split' m) :: Pair (Tree (S m) a) -> Pair (Pair (Tree m a))
-- transpose :: Pair (Pair (Tree m a)) -> Pair (Pair (Tree m a))
-- fmap transpose :: Pair (Pair (Tree m a)) -> Pair (Tree (Pair m a))
-- fmap B :: Pair (Tree (Pair m a)) -> Pair (Tree (S m) a)

#if 0

unB :: Tree (S (S m)) a -> Pair (Tree (S m) a)
fmap (split' m) :: Pair (Tree (S m) a) -> Pair (Pair (Tree m a))
ptranspose :: Pair (Pair (Tree m a)) -> Pair (Pair (Tree m a))
fmap B :: Pair (Pair (Tree m a)) -> Pair (Tree (S m) a)

#endif

-- > toList (unriffle (fromList [1..16] :: Tree N4 Int))
-- [1,3,5,7,9,11,13,15,2,4,6,8,10,12,14,16]

-- transposeT :: Unop (Tree (S (S m)) a)
-- transposeT = B . fmap B . ptranspose . fmap unB . unB

-- fmap unB . unB :: Tree (S (S m)) a -> Pair (Pair (Tree m a))
-- ptranspose :: Pair (Pair (Tree m a)) -> Pair (Pair (Tree m a))
-- B . fmap B :: Pair (Pair (Tree m a)) -> Tree (S (S m)) a

-- unriffleA :: IsNat n => Unop (Tree (S n) a)
-- unriffleA = riff' nat
--  where
--    riff' :: Nat n -> Unop (Tree (S n) a)
--    riff' Zero     = id
--    riff' (Succ m) = 

#if 0

instance Zippable (Tree Z) where
  L a `zip` L b = L (a,b)
  {-# INLINE zipWith #-}

instance Zippable (Tree n) => Zippable (Tree (S n)) where
  B u `zip` B v = B (uncurry zip <$> (u `zip` v))
  {-# INLINE zipWith #-}

#if 0
B u :: Tree (S n) a
B v :: Tree (S n) b
u :: Pair (Tree n a)
v :: Pair (Tree n b)
u `zip` v :: Pair (Tree n a :* Tree n b)
uncurry zip <$> (u `zip` v) :: Pair (Tree n (a :* b))
B (uncurry zip <$> (u `zip` v)) :: Tree (S n) (a :* b)
#endif

#else

instance Zippable (Tree Z) where
  -- zipWith f = \ (L a) (L b) -> L (f a b)
  -- zipWith f = inL2 f
  zipWith = inL2
  {-# INLINE zipWith #-}

instance Zippable (Tree n) => Zippable (Tree (S n)) where
  -- zipWith f = \ (B u) (B v) -> B (zipWith (zipWith f) u v)
  -- zipWith f = inB2 (zipWith (zipWith f))
  zipWith = inB2.zipWith.zipWith
  {-# INLINE zipWith #-}

#if 0
f :: a -> b -> c
B u :: Tree (S n) a
B v :: Tree (S n) b
u :: Pair (Tree n a)
v :: Pair (Tree n b)
zipWith f :: Tree n a -> Tree n b -> Tree n c
zipWith (zipWith f) :: Pair (Tree n a) -> Pair (Tree n b) -> Pair (Tree n c)
zipWith (zipWith f) u v :: Pair (Tree n c)
B (zipWith (zipWith f) u v) :: Tree (S n) c
#endif

#endif

type D n = Dict (Generic1 (Tree n), Sized (Rep1 (Tree n)), LScan (Rep1 (Tree n)))

asG :: IsNat n => D n
asG = asG' nat

asG' :: Nat n -> D n
asG' Zero                  = Dict
asG' (Succ (asG' -> Dict)) = Dict
{-# INLINE asG' #-}

instance IsNat n => Sized (Tree n) where
#if 1
  size = const (twoNat (nat :: Nat n))
#else
  size | Dict <- asG :: D n = genericSize
#endif
  {-# INLINE size #-}

#if 0
instance IsNat n => LScan (Tree n) where
  lscan | Dict <- asG :: D n = genericLscan
  {-# INLINE lscan #-}
#elif 0
instance (Generic1 (Tree n), LScan (Rep1 (Tree n)))
      => LScan (Tree n) where lscan = genericLscan
                              {-# INLINE lscan #-}
#elif 0
instance LScan (Tree Z) where lscan = genericLscan

instance (IsNat n, LScan (Tree n)) => LScan (Tree (S n)) where
  lscan = genericLscan
  {-# INLINE lscan #-}
#elif 1
instance IsNat n => LScan (Tree n) where
  lscan = lscan' nat
  {-# INLINE lscan #-}

lscan' :: Monoid a => Nat n -> Tree n a -> (Tree n a, a)
lscan' Zero     = \ (L a)  -> (L mempty, a)
lscan' (Succ m) = \ (B ts) -> first B (lscanComp' lscan (lscan' m) ts)
{-# INLINE lscan' #-}
#else
instance LScan (Tree Z) where
  lscan (L a) = (L mempty, a)

instance LScan (Tree n) => LScan (Tree (S n)) where
  lscan (B ts)  = first B (lscanComp ts)
  {-# INLINE lscan #-}
#endif

#if 0

#if 0
instance (HasIf (Rep (Tree n a)), HasRep (Tree n a)) => HasIf (Tree n a) where
  if_then_else = repIf

--     Constraint is no smaller than the instance head
--       in the constraint: HasIf (Rep (Vec n a))
--     (Use UndecidableInstances to permit this)
#else
#define RepIf(ab,re) \
instance HasIf (re) => HasIf (ab) where \
{ if_then_else c a a' = abst (if_then_else c (repr a) (repr a') :: re) ;\
  {-# INLINE if_then_else #-} \
}
RepIf(Tree Z a,a)
-- RepIf(Tree (S n) a,Pair (Tree n a))
-- Leaves behind some casts. See journal notes 2014-10-03.

instance HasIf (Tree n a) => HasIf (Tree (S n) a) where
  if_then_else c a a' =
    (abst.abst) (if_then_else c ((repr.repr) a) ((repr.repr) a') :: (Tree n a,Tree n a))
  {-# INLINE if_then_else #-}

-- Works now, but breaks parametrizing out `Pair`.

#endif

#endif

instance Reversible (Tree n) where
  reverse (L a)  = L a
  reverse (B ts) = B (reverse (reverse <$> ts))
  {-# INLINE reverse #-}

fromList :: IsNat n => [a] -> Tree n a
fromList = fromList' nat

fromList' :: Nat n -> [a] -> Tree n a
fromList' Zero     [a] = L a
fromList' Zero     _   = error "fromList': length mismatch"
fromList' (Succ n) as  = B (fromList' n <$> halves as)
{-# INLINE fromList' #-}

halves :: [a] -> Pair [a]
halves as = toP (splitAt (length as `div` 2) as)

{--------------------------------------------------------------------
    Construction (for examples)
--------------------------------------------------------------------}

tree0 :: a -> Tree N0 a
tree0 = L
{-# INLINE tree0 #-}

tree1 :: a -> a -> Tree N1 a
tree1 a b = B (tree0 a :# tree0 b)
{-# INLINE tree1 #-}

tree2 :: a -> a -> a -> a -> Tree N2 a
tree2 a b c d = B (tree1 a b :# tree1 c d)
{-# INLINE tree2 #-}

tree3 :: a -> a -> a -> a -> a -> a -> a -> a -> Tree N3 a
tree3 a b c d e f g h = B (tree2 a b c d :# tree2 e f g h)
{-# INLINE tree3 #-}

tree4 :: a -> a -> a -> a -> a -> a -> a -> a
      -> a -> a -> a -> a -> a -> a -> a -> a
      -> Tree N4 a
tree4 a b c d e f g h i j k l m n o p =
  B (tree3 a b c d e f g h :# tree3 i j k l m n o p)
{-# INLINE tree4 #-}

tree5 :: a -> a -> a -> a -> a -> a -> a -> a
      -> a -> a -> a -> a -> a -> a -> a -> a
      -> a -> a -> a -> a -> a -> a -> a -> a
      -> a -> a -> a -> a -> a -> a -> a -> a
      -> Tree N5 a
tree5 a  b  c  d  e  f  g  h  i  j  k  l  m  n  o  p
      a' b' c' d' e' f' g' h' i' j' k' l' m' n' o' p' =
  B (  tree4 a  b  c  d  e  f  g  h  i  j  k  l  m  n  o  p 
    :# tree4 a' b' c' d' e' f' g' h' i' j' k' l' m' n' o' p')
{-# INLINE tree5 #-}

tree6 :: a -> a -> a -> a -> a -> a -> a -> a
      -> a -> a -> a -> a -> a -> a -> a -> a
      -> a -> a -> a -> a -> a -> a -> a -> a
      -> a -> a -> a -> a -> a -> a -> a -> a
      -> a -> a -> a -> a -> a -> a -> a -> a
      -> a -> a -> a -> a -> a -> a -> a -> a
      -> a -> a -> a -> a -> a -> a -> a -> a
      -> a -> a -> a -> a -> a -> a -> a -> a
      -> Tree N6 a
tree6 a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 n1 o1 p1
      a2 b2 c2 d2 e2 f2 g2 h2 i2 j2 k2 l2 m2 n2 o2 p2
      a3 b3 c3 d3 e3 f3 g3 h3 i3 j3 k3 l3 m3 n3 o3 p3
      a4 b4 c4 d4 e4 f4 g4 h4 i4 j4 k4 l4 m4 n4 o4 p4 =
  B (  tree5 a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 n1 o1 p1
             a2 b2 c2 d2 e2 f2 g2 h2 i2 j2 k2 l2 m2 n2 o2 p2
    :# tree5 a3 b3 c3 d3 e3 f3 g3 h3 i3 j3 k3 l3 m3 n3 o3 p3
             a4 b4 c4 d4 e4 f4 g4 h4 i4 j4 k4 l4 m4 n4 o4 p4 )
{-# INLINE tree6 #-}

{--------------------------------------------------------------------
    Lookup and update
--------------------------------------------------------------------}

subtree :: Vec n Bool -> Tree (n :+: m) a -> Tree m a
subtree ZVec      = id
subtree (b :< bs) = subtree bs . P.get b . unB

#ifdef Induction

get :: forall n a. IsNat n => Vec n Bool -> Tree n a -> a
get bs | Dict <- (plusZero :: Dict (PlusZero n)) = unL . subtree bs

(!) :: IsNat n => Tree n a -> Vec n Bool -> a
(!) = flip get

#else

get :: Vec n Bool -> Tree n a -> a
get ZVec      = unL
get (b :< bs) = get bs . P.get b . unB

(!) :: Tree n a -> Vec n Bool -> a
(!) = flip get

#endif

update :: Vec n Bool -> Unop a -> Unop (Tree n a)
update ZVec      = inL
update (b :< bs) = inB . P.update b . update bs

{-# INLINE get #-}
{-# INLINE update #-}

_t1,_t1' :: Tree N1 Int
_t1 = tree1 3 5
_t1' = update (False :< ZVec) succ _t1

{--------------------------------------------------------------------
    Circuit support
--------------------------------------------------------------------}

AbsTy(Tree Z a)
AbsTy(Tree (S n) a)

{--------------------------------------------------------------------
    Numeric instances via the applicative-numbers package
--------------------------------------------------------------------}

-- Generate bogus (error-producing) Enum
#define INSTANCE_Enum

#define CONSTRAINTS IsNat n, 

#define APPLICATIVE Tree n
#include "ApplicativeNumeric-inc.hs"
