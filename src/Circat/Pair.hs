{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

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
  , pairIf
  ) where

import Prelude hiding (id,(.),curry,uncurry,reverse)

import Data.Monoid ({-Monoid(..),-}(<>))
-- import Data.Functor ((<$>))
-- import Data.Foldable (Foldable(..))
-- import Data.Traversable (Traversable(..))
import Control.Applicative ({-Applicative(..),-}liftA2)
import Data.Ord (comparing)
import Data.Typeable (Typeable)
import Data.Data (Data)
import GHC.Generics (Generic,Generic1) 
import Test.QuickCheck (Arbitrary(..),CoArbitrary(..))

-- More in FunctorCombo.Pair

import Circat.Misc (Unop,(:*),Reversible(..),Sized(..))
import Circat.Category  -- (ProductCat(..))
import Circat.Category (Uncurriable(..),twiceP,(***),(&&&),second)
import Circat.Classes (BottomCat(..),IfCat(..),IfT)
import Circat.Scan
import Circat.Circuit
#include "AbsTy.inc"

{--------------------------------------------------------------------
    Pair representation and basic instances
--------------------------------------------------------------------}

-- Stolen from FunctorCombo.Pair in functor-combo. Fix that package for GHC 7.8,
-- and use it here.

infixl 1 :#
-- | Uniform pairs
data Pair a = a :# a deriving (Functor,Eq,Show,Typeable,Data,Generic,Generic1)

instance Arbitrary a => Arbitrary (Pair a) where
  arbitrary = liftA2 (:#) arbitrary arbitrary
  shrink (x :# y) = [ x' :# y'  | (x',y') <- shrink (x,y) ]

instance CoArbitrary a => CoArbitrary (Pair a) where
  coarbitrary (x :# y) = coarbitrary x . coarbitrary y

instance HasRep (Pair a) where
  type Rep (Pair a) = a :* a
  repr (a :# a') = (a,a')
  abst (a,a') = (a :# a')
  {-# INLINE repr #-}
  {-# INLINE abst #-}

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

instance Sized Pair where
  size = const 2
  {-# INLINE size #-}

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
    Circuit support
--------------------------------------------------------------------}

instance GenBuses q_q => Uncurriable (:>) q_q (Pair a) where
  uncurries = id

instance GenBuses a => GenBuses (Pair a) where
  genBuses' prim ins = abstB <$> (PairB <$> gb <*> gb)
   where
     gb :: BusesM (Buses a)
     gb = genBuses' prim ins
     {-# NOINLINE gb #-}
  delay (a :# b) = abstC . (del a *** del b) . reprC
   where
     del :: a -> (a :> a)
     del = delay
     {-# NOINLINE del #-}
  ty = const (PairT t t)
   where
     t = ty (undefined :: a)
     {-# NOINLINE t #-}

-- Without these NOINLINE pragmas, GHC's typechecker does exponential work for
-- binary trees. I'll want to do something similar for Vec as well so that n-ary
-- trees don't blow up.

instance BottomCat (:>) a => BottomCat (:>) (Pair a) where
  bottomC = abstC . (bc &&& bc)
   where
     bc :: () :> a
     bc = bottomC
     {-# NOINLINE bc #-}

instance IfCat (:>) a => IfCat (:>) (Pair a)
 where
   ifC = abstC . pairIf . second (twiceP reprC)

-- Specialization of prodPair
pairIf :: forall k a. (ProductCat k, IfCat k a) => IfT k (a :* a)
pairIf = half exl &&& half exr
  where
    half :: (u `k` a) -> ((Bool :* (u :* u)) `k` a)
    half f = ifC . second (twiceP f)
    {-# NOINLINE half #-}

{--------------------------------------------------------------------
    Numeric instances via the applicative-numbers package
--------------------------------------------------------------------}

-- Generate bogus (error-producing) Enum
#define INSTANCE_Enum

#define CONSTRAINTS
#define APPLICATIVE Pair

#include "ApplicativeNumeric-inc.hs"
