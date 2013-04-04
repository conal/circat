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

class BoolC (~>) where
  andC, orC :: (Bool :* Bool) ~> Bool
  notC :: Bool ~> Bool

instance BoolC (->) where
  andC = uncurry (&&)
  orC  = uncurry (||)
  notC = not

class EqC (~>) where
  type EqConstraint a :: Constraint
  type EqConstraint a = () ~ () -- or just (), if it works
  eq, neq :: (Eq a, EqConstraint a) => (a :* a) ~> Bool

instance EqC (->) where
  eq  = uncurry (==)
  neq = uncurry (/=)
