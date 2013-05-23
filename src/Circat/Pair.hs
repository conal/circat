{-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators, TypeFamilies, ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-} -- see below

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

import Control.Arrow (arr,Kleisli)

import FunctorCombo.Pair (Pair(..))

import Circat.Misc ((:*),(<~))
import Circat.Category -- (ProductCat(..))
import Circat.State (pureState,StateFun,StateExp)

-- From FunctorCombo.Pair:
-- 
--   data Pair a = a :# a deriving (Functor,Eq,Show,Typeable,Data)
-- 
-- plus many more instances

class ProductCat k => PairCat k where
  toPair :: (a :* a) `k` Pair a
  unPair :: Pair a `k` (a :* a)

instance PairCat (->) where
  toPair (a,b) = a :# b
  unPair (a :# b) = (a,b)

instance Monad m => PairCat (Kleisli m) where
  toPair = arr toPair
  unPair = arr unPair

instance (UnitCat k, PairCat k) => PairCat (StateFun k s) where
  toPair = pureState toPair
  unPair = pureState unPair

instance (ClosedCatWith k s, UnitCat k, PairCat k)
      => PairCat (StateExp k s) where
  toPair = pureState toPair
  unPair = pureState unPair

--     Illegal irreducible constraint ClosedKon k s
--     in superclass/instance head context (Use -XUndecidableInstances to permit this)

inPair :: PairCat k =>
          ((a :* a) `k` (b :* b)) -> (Pair a `k` Pair b)
inPair = toPair <~ unPair
