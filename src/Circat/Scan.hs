{-# LANGUAGE GADTs, FlexibleInstances, FlexibleContexts, Rank2Types #-}
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
  ( LScan(..), Zippable(..), lsums, lproducts
  , lscanGF, lscanGF'
  ) where

import Prelude hiding (zip,unzip)

import Data.Monoid (Monoid(..),Sum(..),Product(..))
import Data.Functor ((<$>))
import Control.Arrow ((***))

class Functor f => LScan f where
  lscan :: Monoid a => f a -> (f a, a)
  -- Temporary hack to avoid newtype-like representation.
  lscanDummy :: f a
  lscanDummy = undefined

type LScanTy f = forall a. Monoid a => f a -> (f a, a)

-- | Variant of 'lscanGF' useful with size-indexed functors
lscanGF' :: (Zippable g, Functor g, Functor f, Monoid a) =>
            LScanTy g -> LScanTy f
         -> g (f a) -> (g (f a), a)
lscanGF' lscanG lscanF gfa  = (adjust <$> zip tots' gfa', tot)
 where
   (gfa' ,tots)  = unzip (lscanF <$> gfa)
   (tots',tot)   = lscanG tots
   adjust (p,t)  = (p `mappend`) <$> t

lscanGF :: (LScan g, LScan f, Zippable g, Monoid a) =>
           g (f a) -> (g (f a), a)
lscanGF = lscanGF' lscan lscan

-- lscanGF gfa  = (adjust <$> zip tots' gfa', tot)
--  where
--    (gfa' ,tots)  = unzip (lscan <$> gfa)
--    (tots',tot)   = lscan tots
--    adjust (p,t)  = (p `mappend`) <$> t

lsums :: (LScan f, Num b) => f b -> (f b, b)
lsums = (fmap getSum *** getSum) . lscan . fmap Sum

lproducts :: (LScan f, Num b) => f b -> (f b, b)
lproducts = (fmap getProduct *** getProduct) . lscan . fmap Product

class Zippable f where
  zip :: f a-> f b -> f (a,b)
  -- Temporary hack to avoid newtype-like representation.
  zippableDummy :: f a
  zippableDummy = undefined

-- zipA :: Applicative f => (f a, f b) -> f (a,b)
-- zipA = uncurry (liftA2 (,))

unzip :: Functor f => f (a,b) -> (f a, f b)
unzip ps = (fst <$> ps, snd <$> ps)
