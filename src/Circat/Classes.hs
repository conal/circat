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

import Prelude hiding (id,(.),curry,uncurry)
import qualified Prelude as P
import Control.Arrow (arr,Kleisli)
-- import GHC.Prim (Constraint)

import Circat.Misc ((:*),Unit)
import Circat.Category

-- | Category with boolean operations.
class ProductCat k => BoolCat k where
  notC :: Bool `k` Bool
  andC, orC, xorC :: (Bool :* Bool) `k` Bool

-- The Category superclass is just for convenience.

instance BoolCat (->) where
  notC = not
  andC = P.uncurry (&&)
  orC  = P.uncurry (||)
  xorC = P.uncurry (/=)

-- HACK: generalize/replace/...
class NumCat k a where
  add, mul :: (a :* a) `k` a

instance Num a => NumCat (->) a where
  add = uncurry (+)
  mul = uncurry (*)

instance (Monad m, Num a) => NumCat (Kleisli m) a where
  add = arr add
  mul = arr mul

#if 1
class BottomCat k a where
  bottomC :: Unit `k` a

instance BottomCat (->) a where bottomC = error "bottom"

#else
#if 0
class BottomCat k where
  type BottomKon k a :: Constraint
  type BottomKon k a = Yes a
  bottomC :: BottomKon k a => Unit `k` a
-- The constraint is problematic for the HasUnitArrow instance on Prim in
-- LambdaCCC.Prim. Drop the constraint, and add BotB in Circat.Circuit.
#else
class BottomCat k where
  bottomC :: Unit `k`a
instance BottomCat (->) where bottom = error "bottom"
#endif
#endif

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

#if 0

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

#endif

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

type IfT k a = (Bool :* (a :* a)) `k` a

class IfCat k a where ifC :: IfT k a

instance IfCat (->) a where
  ifC (i,(t,e)) = if i then t else e

unitIf :: TerminalCat k => IfT k ()
unitIf = it

prodIf :: forall k a b. (ProductCat k, IfCat k a, IfCat k b) => IfT k (a :* b)
prodIf = half exl &&& half exr
  where
    half :: IfCat k c => (u `k` c) -> ((Bool :* (u :* u)) `k` c)
    half f = ifC . second (twiceP f)

#if 0

   prodIf
== \ (c,((a,b),(a',b'))) -> (ifC (c,(a,a')), ifC (c,(b,b')))
== (\ (c,((a,b),(a',b'))) -> ifC (c,(a,a'))) &&& ...
== (ifC . (\ (c,((a,b),(a',b'))) -> (c,(a,a')))) &&& ...
== (ifC . first (\ ((a,b),(a',b')) -> (a,a'))) &&& ...
== (ifC . first (twiceP exl)) &&& (ifC . first (twiceP exr))

#endif

funIf :: forall k a b. (ClosedCat k, IfCat k b) => IfT k (a -> b)
funIf = curry (ifC . (exl . exl &&& (half exl &&& half exr)))
 where
   half :: (u `k` (a -> b)) -> (((_Bool :* u) :* a) `k` b)
   half h = apply . first (h . exr)

-- funIf = curry (ifC . (exl . exl &&& (apply . first (exl . exr) &&& apply . first (exr . exr))))

#if 0

   funIf
== \ (c,(f,f')) -> \ a -> ifC (c,(f a,f' a))
== curry (\ ((c,(f,f')),a) -> ifC (c,(f a,f' a)))
== curry (ifC . \ ((c,(f,f')),a) -> (c,(f a,f' a)))
== curry (ifC . ((exl.exl) &&& \ ((c,(f,f')),a) -> (f a,f' a)))
== curry (ifC . ((exl.exl) &&& ((\ ((c,(f,f')),a) -> f a) &&& (\ ((c,(f,f')),a) -> f' a))))
== curry (ifC . ((exl.exl) &&& (apply (first (exl.exr)) &&& (apply (first (exl.exr))))))

#endif

repIf :: (RepCat k, ProductCat k, HasRep a, IfCat k (Rep a)) => IfT k a
repIf = abstC . ifC . second (twiceP reprC)

#if 0
   repIf
== \ (c,(a,a')) -> abstC (ifC (c,(reprC a,reprC a')))
== \ (c,(a,a')) -> abstC (ifC (c,(twiceP reprC (a,a'))))
== \ (c,(a,a')) -> abstC (ifC (second (twiceP reprC) (c,((a,a')))))
== abstC . ifC . second (twiceP reprC)
#endif
