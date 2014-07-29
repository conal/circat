{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Rep
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Convert to and from standard representations
----------------------------------------------------------------------

module Circat.Rep (Rep,HasRep(..)) where

import Data.Monoid (Sum(..))
-- TODO: more

import Circat.Misc ((:*))
import TypeUnary.TyNat (Z,S)
import TypeUnary.Vec (Vec(..))

type family Rep a

class HasRep a where
  repr :: Rep a ~ a' => a -> a'
  abst :: Rep a ~ a' => a' -> a

-- Note types:
-- 
--   repr :: forall a. HasRep a => forall a'. Rep a ~ a' => a' -> a
--   abst :: forall a. HasRep a => forall a'. Rep a ~ a' => a -> a'
-- 
-- Note: Using Rep a ~ a' rather than the reverse to make the calls a little to
-- construct (using normaliseType and no mkSymCo).

type instance Rep (Vec Z a) = ()
instance HasRep (Vec Z a) where
  repr ZVec = ()
  abst () = ZVec

type instance Rep (Vec (S n) a) = a :* Vec n a
instance HasRep (Vec (S n) a) where
  repr (a :< as) = (a, as)
  abst (a, as) = (a :< as)

type instance Rep (Sum a) = a
instance HasRep (Sum a) where
  repr (Sum a) = a
  abst a = Sum a
