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
  notC :: Bool ~> Bool
  andC, orC :: (Bool :* Bool) ~> Bool

instance BoolCat (->) where
  notC = not
  andC = uncurry (&&)
  orC  = uncurry (||)

class EqCat (~>) where
  type EqConstraint a :: Constraint
  type EqConstraint a = () ~ () -- or just (), if it works
  eq, neq :: (Eq a, EqConstraint a) => (a :* a) ~> Bool

instance EqCat (->) where
  eq  = uncurry (==)
  neq = uncurry (/=)
