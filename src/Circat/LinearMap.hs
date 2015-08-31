{-# LANGUAGE TypeOperators, TypeSynonymInstances #-}
{-# LANGUAGE GADTs, KindSignatures #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.LinearMap
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Linear maps as GADT
----------------------------------------------------------------------

module Circat.LinearMap where

-- TODO: explicit exports

import Circat.Misc ((:*))

import Data.AdditiveGroup (AdditiveGroup(..))

infixr 1 :-*

data (:-*) :: * -> * -> * where
  Scale :: Num a => a -> (a :-* a)
  (:&&&) :: (a :-* c) -> (a :-* d) -> (a :-* c :* d)
  (:|||) :: AdditiveGroup c =>
            (a :-* c) -> (b :-* c) -> (a :* b :-* c)

-- infixl 9 @$

-- Scale s    @$ x     = s * x
-- (f :&&& g) @$ a     = (f @$ a, g @$ a)
-- (f :||| g) @$ (a,b) = f @$ a ^+^ f @$ b

-- mu = (@$) -- for prefix

mu :: (u :-* v) -> u -> v
mu (Scale s)  x     = s * x
mu (f :&&& g) a     = (mu f a, mu g a)
mu (f :||| g) (a,b) = mu f a ^+^ mu g b

{- Note the homomorphisms:

> mu (f :&&& g) = mu f &&& mu g
> mu (f :||| g) = mu f ||| mu g

if the RHSs are interpreted in **Vect**.

To do: make a clear notational distinction between the representation and the model of linear maps.

-}

class HasZero z where zeroL :: a :-* z

instance (HasZero u, HasZero v) => HasZero (u :* v) where
  zeroL = (zeroL,zeroL)

-- instance AdditiveGroup v => AdditiveGroup (u :-* v) where
--   zeroV = 

-- infixr 9 @.
-- (@.) :: (b :-* c) -> (a :- b) -> (a :-* c)


-- Specification: mu (g @. f) == mu g . mu f

