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

import Prelude hiding (id,(.),const,not,and,or)
import qualified Prelude as P

import GHC.Prim (Constraint)

import TypeUnary.Vec (Vec,Z,S)

import Circat.Misc ((:*))
import Circat.Category (Category(..),ProductCat(..),inRassocP,UnitCat(..))

-- | Category with boolean operations.
-- The 'ProductCat' superclass is just for convenient use.
class ProductCat (~>) => BoolCat (~>) where
  type BoolT (~>)
  not :: BoolT (~>) ~> BoolT (~>)
  and, or, xor :: (BoolT (~>) :* BoolT (~>)) ~> BoolT (~>)

-- | Convenient notational alternative
type BCat (~>) b = (BoolCat (~>), b ~ BoolT (~>))

-- The Category superclass is just for convenience.

instance BoolCat (->) where
  type BoolT (->) = Bool
  not = P.not
  and = uncurry (&&)
  or  = uncurry (||)
  xor = uncurry (/=)

class BoolCat (~>) => EqCat (~>) where
  type EqConstraint (~>) a :: Constraint
  type EqConstraint (~>) a = () ~ () -- or just (), if it works
  eq, neq :: (Eq a, EqConstraint (~>) a) => (a :* a) ~> BoolT (~>)
  neq = not . eq

-- TODO: Revisit the type constraints for EqCat.

-- | Convenient notational alternative
type ECat (~>) b = (EqCat (~>), b ~ BoolT (~>))

instance EqCat (->) where
  type EqConstraint (->) a = ()         -- why needed??
  eq  = uncurry (==)
  neq = uncurry (/=)

class (UnitCat (~>), ProductCat (~>)) => VecCat (~>) where
  toVecZ :: () ~> Vec Z a
  unVecZ :: Vec Z a ~> ()
  toVecS :: (a :* Vec n a) ~> Vec (S n) a
  unVecS :: Vec (S n) a ~> (a :* Vec n a)

class ProductCat (~>) => AddCat (~>) where
  fullAdd :: b ~ BoolT (~>) => ((b :* b) :* b) ~> (b :* b)

instance AddCat (->) where
  fullAdd ((a,b),cin) = (axb /= cin, anb || cin && axb)
   where
     axb = a /= b
     anb = a && b

-- TODO: Experiment with interfaces simpler than AddCat, including none at all,
-- defining fullAdd via BoolCat etc. Better yet, give a default definition.

-- fullAdd' :: (ProductCat (~>), b ~ BoolT (~>), (~>) ~ (->)) =>
--             ((b :* b) :* b) ~> (b :* b)

-- fullAdd' ((a,b),cin) = (axb /= cin, anb || cin && axb)
--  where
--    axb = a /= b
--    anb = a && b

-- fullAdd' ((a,b),cin) = (neq (axb,cin), or (anb,and(cin,axb)))
--  where
--    axb = xor (a,b)
--    anb = and (a,b)

-- fullAdd' (ab,cin) = (neq (axb,cin), or (anb, and(cin,axb)))
--  where
--    axb = xor ab
--    anb = and ab

-- fullAdd' (ab,cin) = (neq (axb,cin), or (anb, and(cin,axb)))
--  where
--    (axb,anb) = (xor &&& and) ab

-- | Half adder: addends in; carry and sum out.
halfAdd :: BCat (~>) b => (b :* b) ~> (b :* b)
halfAdd = xor &&& and

-- halfAdd :: Bool :* Bool -> Bool :* Bool


-- fullAdd' (ab,cin) = (s2, or (c1,c2))
--  where
--    (s1,c1) = halfAdd ab
--    (s2,c2) = halfAdd (s1,cin)

{-

first halfAdd  :: A * C       -> (C * S) * C
rassocP        :: (C * S) * C -> C * (S * C)
second halfAdd :: C * (S * C) -> C * (C * S)
lassocP        :: C * (C * S) -> (C * C) * S
first or       :: (C * C) * S -> C * S

-}

-- fullAdd' = first or . lassocP . second halfAdd . rassocP . first halfAdd

fullAdd' :: BCat (~>) b => ((b :* b) :* b) ~> (b :* b)
fullAdd' = first or . inRassocP (second halfAdd) . first halfAdd
