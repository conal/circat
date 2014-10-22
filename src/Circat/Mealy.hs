{-# LANGUAGE CPP #-}
{-# LANGUAGE ExistentialQuantification, TupleSections, TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables, Arrows #-}
{-# LANGUAGE ConstraintKinds, TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

#define CircuitConstraint

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Mealy
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Mealy machines
----------------------------------------------------------------------

module Circat.Mealy (Mealy(..),ArrowCircuit(..),ArrowCircuitT) where

import Prelude hiding (id,(.))
import Control.Category
import Control.Applicative ((<$>), Applicative(..))
import Data.Tuple (swap)
import GHC.Prim (Constraint)

import Control.Arrow

import Circat.Misc (dup) -- ,Unit,(:*)

#ifdef CircuitConstraint
import Circat.Circuit (GenBuses(..)) -- , Machine, unitizeMachine
#endif

{--------------------------------------------------------------------
    Experiment with constraining s
--------------------------------------------------------------------}

#ifdef CircuitConstraint

type C = GenBuses

#else

class C s

instance C ()
instance (C a, C b) => C (a,b)
instance C Bool
instance C Int

#endif

--------------------------------------------------------------------

data Mealy a b = forall s. C s => Mealy ((a,s) -> (b,s)) s

-- We could probably generalize Mealy to an arrow transformer.

instance Category Mealy where
  id = Mealy id ()
  Mealy g t0 . Mealy f s0 = Mealy h (s0,t0)
   where
     h (a,(s,t)) = (c,(s',t'))
      where
        (b,s') = f (a,s)
        (c,t') = g (b,t)
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance Arrow Mealy where
  arr f = Mealy (first f) ()
  Mealy f s0 *** Mealy g t0 = Mealy h (s0,t0)
   where
     h ((a,b),(s,t)) = ((c,d),(s',t'))
      where
        (c,s') = f (a,s)
        (d,t') = g (b,t)
  first  f = f *** id
  second g = id *** g
  {-# INLINE arr #-}
  {-# INLINE (***) #-}
  {-# INLINE first #-}
  {-# INLINE second #-}

instance ArrowChoice Mealy where
  Mealy f s0 +++ Mealy g t0 = Mealy h (s0,t0)
   where
     h (Left  a,(s,t)) = (Left  c,(s',t)) where (c,s') = f (a,s)
     h (Right b,(s,t)) = (Right d,(s,t')) where (d,t') = g (b,t)
  left  f = f +++ id
  right g = id +++ g
  {-# INLINE (+++) #-}
  {-# INLINE left #-}
  {-# INLINE right #-}

instance ArrowLoop Mealy where
  loop (Mealy f s0) = Mealy (loop (rot . f . rot)) s0
   where
     rot :: ((p,q),r) -> ((p,r),q)
     rot ((p,q),r) = ((p,r),q)

class ArrowLoop k => ArrowCircuit k where
  type CircuitKon k a :: Constraint
  type CircuitKon k a = ()
  delay :: CircuitKon k a => a -> k a a

instance ArrowCircuit Mealy where
  type CircuitKon Mealy a = C a
  delay = Mealy swap
  {-# INLINE delay #-}

-- delay a = Mealy (\ (s,a) -> (a,s)) a

type ArrowCircuitT k a = (ArrowCircuit k, CircuitKon k a)

-- A sort of semantic function.
runMealy :: Mealy a b -> [a] -> [b]
runMealy (Mealy f s0) = go s0
 where
   go _ []     = []
   go s (a:as) = b : go s' as where (b,s') = f (a,s)

{--------------------------------------------------------------------
    Some other standard instances for arrows
--------------------------------------------------------------------}

instance Functor (Mealy a) where
  fmap = flip (>>^)
  {-# INLINE fmap #-}

instance Applicative (Mealy a) where
  pure b = arr (const b)
  fs <*> xs = uncurry ($) <$> (fs &&& xs)
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

{--------------------------------------------------------------------
    Circuit graph generation
--------------------------------------------------------------------}

-- Working here

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

-- Counter

counter0 :: (C a, Num a) => Mealy () a
counter0 = Mealy (\ ((),n) -> (n,n+1)) 0

counter1 :: (ArrowCircuitT k a, Num a) => k () a
counter1 = loop (arr (\ ((),n) -> (n,n+1)) . second (delay 0))

-- Also works when the composed functions are swapped

counter2 :: (ArrowCircuitT k a, Num a) => k () a
counter2 = proc () -> do rec old <- delay 0 -< new
                             new <- returnA -< old + 1
                         returnA -< old

-- [0,1,2,3,4,5,6,7,8,9]
_mc0 :: [Int]
_mc0 = runMealy counter0 (replicate 10 ())

-- [0,1,2,3,4,5,6,7,8,9]
_mc1 :: [Int]
_mc1 = runMealy counter1 (replicate 10 ())

-- [0,1,2,3,4,5,6,7,8,9]
_mc2 :: [Int]
_mc2 = runMealy counter2 (replicate 10 ())

adder0 :: (C a, Num a) => Mealy a a
adder0 = Mealy (\ (old,a) -> dup (old+a)) 0

adder1 :: (ArrowCircuitT k a, Num a) => k a a
adder1 = loop (arr (\ (a,tot) -> dup (tot+a)) . second (delay 0))

-- With arrow notation. Oops. Exclusive.
adder2 :: (ArrowCircuitT k a, Num a) => k a a
adder2 = proc a -> do rec tot <- delay 0 -< tot + a
                      returnA -< tot

-- With arrow notation. Inclusive.
adder3 :: (ArrowCircuitT k a, Num a) => k a a
adder3 = proc a -> do rec old <- delay 0 -< new
                          new <- returnA -< old + a
                      returnA -< new

-- Using let. Inclusive.
adder4 :: (ArrowCircuitT k a, Num a) => k a a
adder4 = proc a -> do rec old <- delay 0 -< new
                          let new = old + a
                      returnA -< new

-- [1,3,6,10,15,21,28,36,45,55]
_ms0 :: [Int]
_ms0 = runMealy adder0 [1..10]

-- [1,3,6,10,15,21,28,36,45,55]
_ms1 :: [Int]
_ms1 = runMealy adder1 [1..10]

-- [0,1,3,6,10,15,21,28,36,45]
_ms2 :: [Int]
_ms2 = runMealy adder2 [1..10]

-- [1,3,6,10,15,21,28,36,45,55]
_ms3 :: [Int]
_ms3 = runMealy adder3 [1..10]

-- [1,3,6,10,15,21,28,36,45,55]
_ms4 :: [Int]
_ms4 = runMealy adder4 [1..10]
