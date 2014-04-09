{-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators, TypeFamilies, ConstraintKinds #-}

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

module Circat.Pair (Pair(..),PairCat(..),inPair) where

-- TODO: consider using standard names like fst, snd & curry.

import Data.Monoid (Monoid(..))
import Control.Arrow (arr,Kleisli)
import Data.Functor ((<$>))
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
import Control.Applicative (Applicative(..),liftA2)
import Data.Typeable (Typeable)
import Data.Data (Data)

-- import FunctorCombo.Pair (Pair(..))

import Circat.Misc ((:*),(<~))
import Circat.Category -- (ProductCat(..))
import Circat.State (pureState,StateFun,StateExp)

{--------------------------------------------------------------------
    Pair representation and basic instances
--------------------------------------------------------------------}

-- Stolen from FunctorCombo.Pair in functor-combo. Fix that package for GHC 7.8,
-- and use it here.

infixl 1 :#
-- | Uniform pairs
data Pair a = a :# a deriving (Functor,Eq,Show,Typeable,Data)

-- The derived foldMap inserts a mempty (in GHC 7.0.4).
instance Foldable Pair where
  foldMap f (a :# b) = f a `mappend` f b

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

{--------------------------------------------------------------------
    
--------------------------------------------------------------------}


class ProductCat k => PairCat k where
  toPair :: (a :* a) `k` Pair a
  unPair :: Pair a `k` (a :* a)

instance PairCat (->) where
  toPair (a,b) = a :# b
  unPair (a :# b) = (a,b)

instance Monad m => PairCat (Kleisli m) where
  toPair = arr toPair
  unPair = arr unPair

instance (TerminalCat k, PairCat k) => PairCat (StateFun k s) where
  toPair = pureState toPair
  unPair = pureState unPair

instance (ClosedCat k, TerminalCat k, PairCat k) => PairCat (StateExp k s) where
  toPair = pureState toPair
  unPair = pureState unPair

inPair :: PairCat k =>
          ((a :* a) `k` (b :* b)) -> (Pair a `k` Pair b)
inPair = toPair <~ unPair
