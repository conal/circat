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

import Circat.Misc ((:*))
import TypeUnary.TyNat (Z,S)
import TypeUnary.Vec (Vec(..),unConsV)

type family Rep a

class HasRep a where
  repr :: a' ~ Rep a => a -> a'
  abst :: a' ~ Rep a => a' -> a

-- Note types:
-- 
--   repr :: forall a. HasRep a => forall a'. a' ~ Rep a => EP (a' -> a)
--   abst :: forall a. HasRep a => forall a'. a' ~ Rep a => EP (a -> a')

-- TODO: maybe switch to Rep a ~ a' across the board, to make the calls a little
-- to construct (using normaliseType and no mkSymCo).

type instance Rep (Vec Z a) = ()
instance HasRep (Vec Z a) where
  repr ZVec = ()
  abst () = ZVec

type instance Rep (Vec (S n) a) = a :* Vec n a
instance HasRep (Vec (S n) a) where
  repr (a :< as) = (a, as)
  abst (a, as) = (a :< as)
