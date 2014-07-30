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

import Data.Monoid
-- TODO: more

import Circat.Misc ((:*))
import TypeUnary.TyNat (Z,S)
import TypeUnary.Nat (Nat(..),IsNat(..))
import TypeUnary.Vec (Vec(..))

type family Rep a

-- | Convert to and from standard representations. Used for transforming case
-- expression scrutinees and constructor applications. The 'repr' method should
-- convert to a standard representation (unit, products, sums), or closer to
-- such a representation, via another type with a 'HasRep' instance. The 'abst'
-- method should reveal a constructor so that we can perform the
-- case-of-known-constructor transformation.
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

#define WrapRep(abstT,reprT,con) \
type instance Rep (abstT) = reprT; \
instance HasRep (abstT) where { repr (con a) = a ; abst a = con a }

WrapRep(Sum a,a,Sum)
WrapRep(Product a,a,Product)
WrapRep(All,Bool,All)
WrapRep(Any,Bool,Any)

-- TODO: Generate these dictionaries on the fly during compilation, so we won't
-- have to list them here.

type instance Rep (Nat Z) = ()
instance HasRep (Nat Z) where
  repr Zero = ()
  abst () = Zero

type instance Rep (Nat (S n)) = () :* Nat n
instance IsNat n => HasRep (Nat (S n)) where
  repr (Succ n) = ((),n)
  abst ((),n) = Succ n
-- The IsNat constraint comes from Succ.
-- TODO: See about eliminating that constructor constraint.
