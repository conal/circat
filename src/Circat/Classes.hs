{-# LANGUAGE TypeOperators, TypeFamilies, ConstraintKinds, GADTs, CPP #-}
{-# LANGUAGE ScopedTypeVariables, Rank2Types, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-} -- see below

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Classes
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Additional type classes for circuit-friendly operations
----------------------------------------------------------------------

module Circat.Classes where

-- TODO: explicit exports

import Prelude hiding (id,(.),const,not,and,or,curry,uncurry)
import qualified Prelude as P
import Control.Arrow (arr,Kleisli)

import Circat.Misc ((:*))
import Circat.Category

-- | Category with boolean operations.
class ProductCat k => BoolCat k where
  not :: Bool `k` Bool
  and, or, xor :: (Bool :* Bool) `k` Bool

-- The Category superclass is just for convenience.

instance BoolCat (->) where
  not = P.not
  and = P.uncurry (&&)
  or  = P.uncurry (||)
  xor = P.uncurry (/=)

-- HACK: generalize/replace/...
class NumCat k a where
  add, mul :: (a :* a) `k` a

instance Num a => NumCat (->) a where
  add = uncurry (+)
  mul = uncurry (*)

instance (Monad m, Num a) => NumCat (Kleisli m) a where
  add = arr add
  mul = arr mul

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- | One-bit mux
class MuxCat k where
  muxB :: (Bool :* (Bool :* Bool)) `k` Bool
  muxI :: (Bool :* (Int  :* Int )) `k` Int

-- TODO: Simplify & generalize. How to keep MuxCat having only one parameter, as
-- needed for the HasUnitArrow k Prim instance in LambdaCCC.Prim?

muxF :: (Bool :* (a :* a)) -> a
muxF (i,(e,t)) = if i then t else e

instance MuxCat (->) where
  muxB = muxF
  muxI = muxF

#if 0

-- Experiment
class Muxy a where
  mux :: (ClosedCat k, MuxCat k) => (Bool :* (a :* a)) `k` a

-- The ClosedCat constraint is unfortunate here. I need ProductCat for the
-- product Muxy instance and ClosedCat for the function Muxy instance.
-- TODO: Find an alternative. Maybe Muxy k a.

instance Muxy Int  where mux = muxI
instance Muxy Bool where mux = muxB

instance (Muxy a, Muxy b) => Muxy (a :* b) where
  mux = half exl &&& half exr
   where
     half f = mux . second (twiceP f)

instance (Muxy a, Muxy b) => Muxy (a -> b) where
 mux = curry (mux . (exl . exl &&& (half exl &&& half exr)))
  where
    half h = apply . first (h . exr)

repMux :: (ClosedCat k, MuxCat k, RepCat k, HasRep a, Muxy (Rep a)) =>
          (Bool :* (a :* a)) `k` a
repMux = abstC . mux . second (twiceP reprC)

-- I can't give a single instance around repMux, because it would overlap
-- everything else. Instead, write instances via repMux. For instance,
-- 
--   instance Muxy a            => Muxy (Pair  a) where mux = repMux
--   instance (IsNat n, Muxy a) => Muxy (Vec n a) where mux = repMux

#endif

#if 0

class IfCat k a where ifA :: IfT k a

instance IfCat (->) a where
  ifA (i,(t,e)) = if i then t else e

prodIf :: forall k a b. (ProductCat k, IfCat k a, IfCat k b) => IfT k (a :* b)
prodIf = half exl &&& half exr
  where
    half :: IfCat k c => (u `k` c) -> ((Bool :* (u :* u)) `k` c)
    half f = ifA . second (twiceP f)

#if 0

   prodIf
== \ (c,((a,b),(a',b'))) -> (ifA (c,(a,a')), ifA (c,(b,b')))
== (\ (c,((a,b),(a',b'))) -> ifA (c,(a,a'))) &&& ...
== (ifA . (\ (c,((a,b),(a',b'))) -> (c,(a,a')))) &&& ...
== (ifA . first (\ ((a,b),(a',b')) -> (a,a'))) &&& ...
== (ifA . first (twiceP exl)) &&& (ifA . first (twiceP exr))

#endif

funIf :: forall k a b. (ClosedCat k, IfCat k b) => IfT k (a -> b)
funIf = curry (ifA . (exl . exl &&& (half exl &&& half exr)))
 where
   half :: (u `k` (a -> b)) -> (((_Bool :* u) :* a) `k` b)
   half h = apply . first (h . exr)

-- funIf = curry (ifA . (exl . exl &&& (apply . first (exl . exr) &&& apply . first (exr . exr))))

#if 0

   funIf
== \ (c,(f,f')) -> \ a -> ifA (c,(f a,f' a))
== curry (\ ((c,(f,f')),a) -> ifA (c,(f a,f' a)))
== curry (ifA . \ ((c,(f,f')),a) -> (c,(f a,f' a)))
== curry (ifA . ((exl.exl) &&& \ ((c,(f,f')),a) -> (f a,f' a)))
== curry (ifA . ((exl.exl) &&& ((\ ((c,(f,f')),a) -> f a) &&& (\ ((c,(f,f')),a) -> f' a))))
== curry (ifA . ((exl.exl) &&& (apply (first (exl.exr)) &&& (apply (first (exl.exr))))))

#endif

repIf :: (RepCat k, ProductCat k, HasRep a, IfCat k (Rep a)) => IfT k a
repIf = abstC . ifA . second (twiceP reprC)

#if 0
   repIf
== \ (c,(a,a')) -> abstC (ifA (c,(reprC a,reprC a')))
== \ (c,(a,a')) -> abstC (ifA (c,(twiceP reprC (a,a'))))
== \ (c,(a,a')) -> abstC (ifA (second (twiceP reprC) (c,((a,a')))))
== abstC . ifA . second (twiceP reprC)
#endif

#endif
