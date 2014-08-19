{-# LANGUAGE GADTs, KindSignatures, CPP #-}
{-# LANGUAGE ScopedTypeVariables, Rank2Types, InstanceSigs, ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-} -- experiment

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

module Circat.RTree (Tree(..) {-,TreeCat(..) -}) where

import Prelude hiding (id,(.),uncurry,zip)

import Data.Monoid (Monoid(..),(<>))
import Data.Functor ((<$),(<$>))
import Control.Applicative (Applicative(..),liftA2)
import Control.Monad (join)
import Data.Foldable
import Data.Traversable (Traversable(..))
import Control.Arrow (arr,Kleisli)
import Data.Typeable (Typeable)

import TypeUnary.Nat hiding ((:*:))

import Circat.Misc ((<~)) -- Unop,(:*)
import Circat.Show (showsApp1)
import Circat.Category
import Circat.Classes
import Circat.Pair -- (Pair(..),PairCat(..))
-- import Circat.State (pureState,StateFun,StateExp)
import Circat.Rep
import Circat.Scan

-- TODO: Use the generalization from numbers-vectors-trees, factoring out Pair

data Tree :: * -> * -> * where
  L :: a -> Tree Z a
  B :: Pair (Tree n a) -> Tree (S n) a

deriving instance Eq a => Eq (Tree n a)
deriving instance Typeable Tree

type instance Rep (Tree Z a) = a
instance HasRep (Tree Z a) where
  repr (L a) = a
  abst a = L a

#if 1
type instance Rep (Tree (S n) a) = Pair (Tree n a)
instance HasRep (Tree (S n) a) where
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

-- The two-step formulation makes for simpler Core.

cant :: String -> a
cant str = error $ str ++ ": GHC doesn't know this case can't happen."

cantT :: String -> a
cantT str = cant (str ++ " on Tree")

instance Ord a => Ord (Tree n a) where
  L a  `compare` L b  = a  `compare` b
  B us `compare` B vs = us `compare` vs
  _    `compare` _   = cantT "compare"

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
  pure a = a <$ units nat
  (<*>)  = ap' nat
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

--   (<*>)  = ap' nat
--    where
--      ap' :: Nat m -> Tree m (a -> b) -> Tree m a -> Tree m b
--      ap' Zero     = inL2 ($)
--      ap' (Succ n) = inB2 (liftA2 (ap' n))
--      {-# INLINE ap' #-}

--   L f  <*> L x  = L (f x)
--   B fs <*> B xs = B (liftA2 (<*>) fs xs)

--   (<*>)  = ap

-- ap :: Tree n (a -> b) -> Tree n a -> Tree n b
-- L f  `ap` L x  = L (f x)
-- B fs `ap` B xs = B (liftA2 ap fs xs)
-- _    `ap` _    = error "(<*>) on Tree n: impossible case"
-- {-# INLINE ap #-}

ap' :: Nat m -> Tree m (a -> b) -> Tree m a -> Tree m b
ap' Zero     = inL2 ($)
ap' (Succ n) = inB2 (liftA2 (ap' n))
{-# INLINE ap' #-}

units :: Nat n -> Tree n ()
units Zero     = L ()
units (Succ n) = B (pure (units n))
{-# INLINE units #-}

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

joinT' :: Tree n (Tree n a) -> Tree n a
joinT' (L t)  = t
joinT' (B (u :# v)) = B (joinT' ((fstP . unB) <$> u) :# joinT' ((sndP . unB) <$> v))

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
{-
  foldMap :: forall a o. Monoid o => (a -> o) -> Tree n a -> o
  foldMap f = foldMap' nat
   where
     foldMap' :: Nat m -> Tree m a -> o
--      foldMap' Zero     = \ (L a ) -> f a
--      foldMap' (Succ m) = \ (B ts) -> foldMap (foldMap' m) ts
     foldMap' Zero     = f . unL
     foldMap' (Succ m) = foldMap (foldMap' m) . unB
-}
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
     traverse' Zero = fmap L . f . unL
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

instance Zippable (Tree Z) where
  L a `zip` L b = L (a,b)

instance Zippable (Tree n) => Zippable (Tree (S n)) where
  B u `zip` B v = B (uncurry zip <$> (u `zip` v))

#if 1
instance LScan (Tree Z) where
  lscan (L a) = (L mempty, a)

instance LScan (Tree n) => LScan (Tree (S n)) where
  lscan (B ts)  = first B (lscanGF ts)
#elif 1
instance LScan (Tree Z) where lscan = lscan' nat

lscan' :: Monoid a => Nat n -> Tree n a -> (Tree n a, a)
lscan' Zero     = \ (L a)  -> (L mempty, a)
lscan' (Succ m) = \ (B ts) -> first B (lscanGF' lscan (lscan' m) ts)
{-# INLINE lscan' #-}
#else
instance LScan (Tree Z) where lscan = lscan' nat

lscan' :: Monoid a => Nat n -> Tree n a -> (Tree n a, a)
lscan' Zero     = \ (L a)  -> (L mempty, a)
lscan' (Succ m) = lscanS m

## working here ##

lscanS :: Monoid a => Nat n -> Tree (S n) a -> (Tree (S n) a, a)
-- lscanS m = \ (B ts) -> first B (lscanGF' lscan (lscan' m) ts)

lscanS Zero (B (L a :# L b)) = (B 

{-# INLINE lscanS #-}
#endif

-- Or
-- reverseT = retree id (fmap reverseT . swapP)

fromList :: IsNat n => [a] -> Tree n a
fromList = fromList' nat

fromList' :: Nat n -> [a] -> Tree n a
fromList' Zero     [a] = L a
fromList' Zero     _   = error "fromList': length mismatch"
fromList' (Succ n) as  = B (fromList' n <$> halves as)

halves :: [a] -> Pair [a]
halves as = toPair (splitAt (length as `div` 2) as)


{--------------------------------------------------------------------
    Numeric instances via the applicative-numbers package
--------------------------------------------------------------------}

-- Generate bogus (error-producing) Enum
#define INSTANCE_Enum

#define CONSTRAINTS IsNat n, 

#define APPLICATIVE Tree n
#include "ApplicativeNumeric-inc.hs"
