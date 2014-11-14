{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs, FlexibleInstances, FlexibleContexts, Rank2Types #-}
{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Scan
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Parallel scan
----------------------------------------------------------------------

module Circat.Scan
  ( Zippable(..)
  , LScanTy, LScan(..), lscanInc
  , lsums, lproducts, lsums', lproducts', iota
  , lscanProd, lscanProd', lscanComp, lscanComp'
  ) where

import Prelude hiding (zip,unzip,zipWith)

import Data.Monoid (Monoid(..),(<>),Sum(..),Product(..))
import Data.Functor ((<$>))
import Control.Arrow ((***))
import Data.Traversable (Traversable(..)) -- ,mapAccumR
import Control.Applicative (Applicative(..),liftA2)

import TypeUnary.Vec (Vec,IsNat)

import Circat.Misc (Unop,(:*))
import Circat.Shift (shiftR)

type LScanTy f = forall a. Monoid a => f a -> f a :* a

class Functor f => LScan f where
  lscan :: LScanTy f
  -- Temporary hack to avoid newtype-like representation.
  lscanDummy :: f a
  lscanDummy = undefined

-- | Scan a product of functors. See also 'lscanProd'.
lscanProd' :: (Functor g, Monoid a)
           => LScanTy f -> LScanTy g
           -> f a :* g a -> (f a :* g a) :* a
lscanProd' lscanF lscanG (fa,ga) = ((fa', adjust <$> ga'), adjust gx)
 where
   (fa',fx) = lscanF fa
   (ga',gx) = lscanG ga
   adjust   = (fx <>)

-- | Scan a product of functors. See also 'lscanProd''.
lscanProd :: (Functor g, Monoid a, LScan f, LScan g)
          => (f a :* g a) -> (f a :* g a) :* a
lscanProd = lscanProd' lscan lscan

-- | Variant of 'lscanComp' useful with size-indexed functors
lscanComp' :: (Zippable g, Functor g, Functor f, Monoid a) =>
              LScanTy g -> LScanTy f
           -> g (f a) -> g (f a) :* a
lscanComp' lscanG lscanF gfa  = (zipWith adjustl tots' gfa', tot)
 where
   (gfa' ,tots)  = unzip (lscanF <$> gfa)
   (tots',tot)   = lscanG tots

adjustl :: (Monoid a, Functor t) => a -> t a -> t a
adjustl p = fmap (p <>)

-- | Scan a composition of functors
lscanComp :: (LScan g, LScan f, Zippable g, Monoid a) =>
             g (f a) -> g (f a) :* a
lscanComp = lscanComp' lscan lscan

-- lscanComp gfa  = (zipWith adjust tots' gfa', tot)
--  where
--    (gfa' ,tots)  = unzip (lscan <$> gfa)
--    (tots',tot)   = lscan tots
--    adjust (p,t)  = (p <>) <$> t

lscanInc :: (LScan f, Traversable f, Monoid b) => Unop (f b)
lscanInc = snd . shiftR . lscan

-- lsums :: (LScan f, Num b) => f b -> (f b, b)
lsums :: (LScan f, Num b) => f b -> (f b, b)
lsums = (fmap getSum *** getSum) . lscan . fmap Sum

lproducts :: (LScan f, Traversable f, Num b) => f b -> f b :* b
lproducts = (fmap getProduct *** getProduct) . lscan . fmap Product

-- Variants 

-- | Numbers from 0 to n-1. Named for APL iota operation (but 0 based).
iota :: (LScan f, Traversable f, Applicative f, Num b) => f b
iota = lsums' (pure 1)

lsums' :: (LScan f, Traversable f, Num b) => Unop (f b)
lsums' = snd . shiftR . lsums
-- lsums' = fmap getSum . lscanInc . fmap Sum

lproducts' :: (LScan f, Traversable f, Num b) => Unop (f b)
lproducts' = snd . shiftR . lproducts
-- lproducts' = fmap getProduct . lscanInc . fmap Product

class Functor f => Zippable f where
  zipWith :: (a -> b -> c) -> f a -> f b -> f c
  zipWith h as bs = uncurry h <$> zip as bs
  zip :: f a -> f b -> f (a,b)
  zip = zipWith (,)
  {-# MINIMAL zip | zipWith #-}

instance IsNat n => Zippable (Vec n) where zipWith = liftA2

-- zipA :: Applicative f => (f a, f b) -> f (a,b)
-- zipA = uncurry (liftA2 (,))

unzip :: Functor f => f (a :* b) -> f a :* f b
unzip ps = (fst <$> ps, snd <$> ps)
