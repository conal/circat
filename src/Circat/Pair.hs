{-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators, TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Pair
-- Copyright   :  (c) 2013 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Pair functor
----------------------------------------------------------------------

module Circat.Pair (Pair(..),PairCat(..),inPair) where

-- TODO: consider using standard names like fst, snd & curry.

import Data.Monoid ((<>))
import Data.Functor ((<$>))
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
import Control.Applicative (Applicative(..),liftA2)
import Control.Arrow (arr,Kleisli)
import Data.Typeable (Typeable)
import Data.Data (Data)

import Circat.Misc ((:*),(<~))
import Circat.Category -- (ProductCat(..))

infixl 1 :#
-- | Uniform pairs
data Pair a = a :# a deriving (Functor,Eq,Show,Typeable,Data)

-- Interpreting Pair a as Bool -> a or as Vec2 a, the instances follow
-- inevitably from the principle of type class morphisms.

-- instance Functor Pair where
--   fmap f (a :# b) = (f a :# f b)

-- The derived foldMap inserts a mempty (in GHC 7.0.4).
instance Foldable Pair where
  foldMap f (a :# b) = f a <> f b

instance Applicative Pair where
  pure a = a :# a
  (f :# g) <*> (a :# b) = (f a :# g b)

instance Monad Pair where
  return = pure
  m >>= f = joinP (f <$> m)

joinP :: Pair (Pair a) -> Pair a
joinP ((a :# _) :# (_ :# d)) = a :# d

-- so
--
--   (a :# b) >>= f = (c :# d)
--    where
--      (c :# _) = f a
--      (_ :# d) = f b

instance Traversable Pair where
  traverse h (fa :# fb) = liftA2 (:#) (h fa) (h fb)
  -- sequenceA (fa :# fb) = liftA2 (:#) fa fb

class ProductCat (~>) => PairCat (~>) where
  toPair :: (a :* a) ~> Pair a
  unPair :: Pair a ~> (a :* a)

instance PairCat (->) where
  toPair (a,b) = a :# b
  unPair (a :# b) = (a,b)

instance Monad m => PairCat (Kleisli m) where
  toPair = arr toPair
  unPair = arr unPair

instance (UnitCat (~>), PairCat (~>)) => PairCat (FState (~>) s) where
  toPair = pureState toPair
  unPair = pureState unPair

inPair :: PairCat (~>) =>
          ((a :* a) ~> (b :* b)) -> (Pair a ~> Pair b)
inPair = toPair <~ unPair
