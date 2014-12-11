{-# LANGUAGE CPP, TypeFamilies, TypeOperators, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Incremental
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Incremental computation category
----------------------------------------------------------------------

module Circat.Incremental where

-- TODO: explicit exports

import Prelude hiding (id,(.),curry,uncurry)

import Circat.Category

-- Try a type class with associated type for changes and their application:

class Changeable a where
  type Ch a
  (+~) :: a -> Ch a -> a
  zeroCh :: a -> Ch a  -- identity for (+~). ignores argument.

-- A type of incremental functions:

data a :~> b = IFun { applyIF :: a -> (b, Ch a -> Ch b) }

-- The `Category` instance can be exactly as for differentiable functions:

instance Category (:~>) where
  id = IFun (\ a -> (a, id))
  IFun k . IFun h = IFun (\ a -> let ( fa, dfa) = h  a
                                     (gfa,dgfa) = k fa
                                 in
                                     (gfa, dgfa . dfa))

-- For `ProductCat`, we'll need changes of pairs, which I'll take to be pairs of changes:

instance (Changeable a, Changeable b) => Changeable (a,b) where
  type Ch (a,b) = (Ch a, Ch b)
  (a,b) +~ (da,db) = (a +~ da, b +~ db)
  zeroCh ~(a,b) = (zeroCh a, zeroCh b)

-- Since `Ch` distributes over products, I think `ProductCat` for differentiable
-- functions also works for incremental functions:

instance ProductCat (:~>) where
  exl = IFun (\ a -> (exl a, exl))
  exr = IFun (\ a -> (exr a, exr))
  IFun f &&& IFun g = IFun (\ a -> let (fa,dfa) = f a
                                       (ga,dga) = g a
                                   in
                                       ((fa,ga), dfa &&& dga))

-- Alternatively, we might want a more sophisticated version of `Ch` allowing
-- more compact representations of no change.

-- Could we generalize to an arrow transformer?

-- Now functions:

instance (Changeable a, Changeable b) => Changeable (a -> b) where
  type Ch (a -> b) = a -> Ch a -> Ch b
  (f +~ df) a = f a +~ df a (zeroCh (undefined :: a))
  zeroCh f = \ _a _da -> zeroCh (f undefined)

instance ClosedCat (:~>) where
  apply = IFun (\ (f,a) -> (f a, \ (df,da) -> df a da))
  curry (IFun h) = IFun (\ a -> let g = curry h a in
                                  (fst . g, \ da b db -> snd (g b) (da,db)))
  uncurry (IFun g) = IFun (\ (a,b) -> let (f,df) = g a in
                                        (f b, \ (da,db) -> df da b db))

-- For typings, see notes from 2014-12-10.
-- Note also concern about duplicating g in curry.

