{-# LANGUAGE TypeOperators, TypeFamilies, ConstraintKinds #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Classes
-- Copyright   :  (c) 2013 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Additional type classes for circuit-friendly operations
----------------------------------------------------------------------

module Circat.Classes where

-- TODO: explicit exports

import GHC.Prim (Constraint)

import Circat.Misc ((:*))

class BoolCat (~>) where
  type Bit (~>)
  notC :: Bit (~>) ~> Bit (~>)
  andC, orC :: (Bit (~>) :* Bit (~>)) ~> Bit (~>)

instance BoolCat (->) where
  type Bit (->) = Bool
  notC = not
  andC = uncurry (&&)
  orC  = uncurry (||)

class BoolCat (~>) => EqCat (~>) where
  type EqConstraint (~>) a :: Constraint
  type EqConstraint (~>) a = () ~ () -- or just (), if it works
  eq, neq :: (Eq a, EqConstraint (~>) a) => (a :* a) ~> Bit (~>)

-- TODO: Revisit the type constraints for EqCat.

instance EqCat (->) where
  eq  = uncurry (==)
  neq = uncurry (/=)
