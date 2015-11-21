{-# LANGUAGE DeriveFunctor, DeriveDataTypeable, CPP #-}
{-# LANGUAGE TypeOperators, TypeFamilies, ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE UndecidableInstances #-}  -- See below

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Pair
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Pair functor
----------------------------------------------------------------------

module Circat.Pair
  ( Pair(..)
  , curryP, uncurryP, toP, fromP, inP
  , fstP, sndP, firstP, secondP
  , sortP
  , get, update
  ) where

import Prelude hiding (id,(.),curry,uncurry,reverse)

import Data.Monoid (Monoid(..),(<>))
import Data.Functor ((<$>))
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
import Control.Applicative (Applicative(..),liftA2)
import Data.Ord (comparing)
import Data.Typeable (Typeable)
import Data.Data (Data)
import Test.QuickCheck (Arbitrary(..),CoArbitrary(..))

-- More in FunctorCombo.Pair

import Circat.Misc (Unop,(:*),Reversible(..))
import Circat.Category  -- (ProductCat(..))
-- import Circat.State (pureState,StateFun,StateExp)
-- import Circat.If
import Circat.Scan

{--------------------------------------------------------------------
    Pair representation and basic instances
--------------------------------------------------------------------}

-- Stolen from FunctorCombo.Pair in functor-combo. Fix that package for GHC 7.8,
-- and use it here.

infixl 1 :#
-- | Uniform pairs
data Pair a = a :# a deriving (Functor,Eq,Show,Typeable,Data)

instance Arbitrary a => Arbitrary (Pair a) where
  arbitrary = liftA2 (:#) arbitrary arbitrary
  shrink (x :# y) = [ x' :# y'  | (x',y') <- shrink (x,y) ]

instance CoArbitrary a => CoArbitrary (Pair a) where
  coarbitrary (x :# y) = coarbitrary x . coarbitrary y

type instance Rep (Pair a) = a :* a
instance HasRep (Pair a) where
  repr (a :# a') = (a,a')
  abst (a,a') = (a :# a')

instance Ord a => Ord (Pair a) where
  compare = comparing fromP

-- The derived foldMap inserts a mempty (in GHC 7.0.4).
instance Foldable Pair where
  foldMap f (a :# b) = f a `mappend` f b
  {-# INLINE foldMap #-}

instance Applicative Pair where
  pure a = a :# a
  (f :# g) <*> (a :# b) = (f a :# g b)
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

instance Monad Pair where
  return = pure
  m >>= f = joinP (f <$> m)
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}

joinP :: Pair (Pair a) -> Pair a
joinP ((a :# _) :# (_ :# d)) = a :# d
{-# INLINE joinP #-}

-- instance Zippable Pair where
--   (a :# b) `zip` (a' :# b') = (a,a') :# (b,b')

instance Zippable Pair where
  zipWith f (a :# b) (a' :# b') = f a a' :# f b b'
  {-# INLINE zipWith #-}

-- so
--
--   (a :# b) >>= f = (c :# d)
--    where
--      (c :# _) = f a
--      (_ :# d) = f b

instance Traversable Pair where
  traverse h (fa :# fb) = liftA2 (:#) (h fa) (h fb)
  -- sequenceA (fa :# fb) = liftA2 (:#) fa fb
  {-# INLINE traverse #-}

instance LScan Pair where
  lscan (a :# b) = (mempty :# a, a <> b)
  {-# INLINE lscan #-}

instance Reversible Pair where
  reverse (a :# b) = b :# a
  {-# INLINE reverse #-}

sortP :: Ord a => Unop (Pair a)
sortP (a :# b) = if a <= b then a :# b else b :# a
{-# INLINE sortP #-}

#if 0

instance (HasIf (Rep (Pair a)), HasRep (Pair a)) => HasIf (Pair a) where
  if_then_else = repIf

--     Constraint is no smaller than the instance head
--       in the constraint: HasIf (Rep (Vec n a))
--     (Use UndecidableInstances to permit this)

#endif

curryP :: (Pair a -> b) -> (a -> a -> b)
curryP g = curry (g . toP)

uncurryP :: (a -> a -> b) -> (Pair a -> b)
uncurryP f = uncurry f . fromP

toP :: (a,a) -> Pair a
toP (a,b) = a :# b

fromP :: Pair a -> (a,a)
fromP (a :# b) = (a,b)

inP :: ((a, a) -> (a, a)) -> Pair a -> Pair a
inP g = toP . g . fromP

fstP :: Pair a -> a
fstP (a :# _) = a

sndP :: Pair a -> a
sndP (_ :# b) = b

firstP :: Unop a -> Unop (Pair a)
firstP f (a :# b) = f a :# b

secondP :: Unop a -> Unop (Pair a)
secondP f (a :# b) = a :# f b

{--------------------------------------------------------------------
    Lookup and update
--------------------------------------------------------------------}

-- TODO: Class interface

get :: Bool -> Pair a -> a
get b (f :# t) = if b then t else f

update :: Bool -> Unop a -> Unop (Pair a)
update False f (a :# b) = (f a :# b)
update True  f (a :# b) = (a :# f b)

{-# INLINE get #-}
{-# INLINE update #-}

{--------------------------------------------------------------------
    Numeric instances via the applicative-numbers package
--------------------------------------------------------------------}

-- Generate bogus (error-producing) Enum
#define INSTANCE_Enum

#define CONSTRAINTS
#define APPLICATIVE Pair

#include "ApplicativeNumeric-inc.hs"
