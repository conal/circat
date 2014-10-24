{-# LANGUAGE CPP #-}
{-# LANGUAGE ExistentialQuantification, TupleSections, TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables, Arrows #-}
{-# LANGUAGE ConstraintKinds, TypeFamilies #-}
{-# LANGUAGE Rank2Types #-} -- for tests
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

#define CircuitConstraint

-- #define Semantics

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

module Circat.Mealy
  ( Mealy(..),ArrowCircuit(..),ArrowCircuitT
#ifdef Semantics
  , asStreamFun, asArrow
#endif
  ) where

import Prelude hiding (id,(.))
import Control.Category
import Control.Arrow
import Control.Applicative ((<$>), Applicative(..))
import Data.Tuple (swap)
import GHC.Prim (Constraint)

import Circat.Misc (dup) -- ,Unit,(:*)

#ifdef CircuitConstraint
import Circat.Circuit (GenBuses(..)) -- , Machine, unitizeMachine
#endif

#ifdef Semantics
import Data.Stream (Stream(..))
import qualified Control.Arrow.Operations as Op
import Control.Arrow.Transformer.Stream
#endif

{--------------------------------------------------------------------
    Experiment with constraining s
--------------------------------------------------------------------}

#ifdef CircuitConstraint

-- type C = GenBuses
type C a = (GenBuses a, Show a)

-- The Show constraint is helpful for debugging. Perhaps remove later.

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
     rot :: ((x,y),z) -> ((x,z),y)
     rot ((x,y),z) = ((x,z),y)

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

#ifdef Semantics

type StreamFun = StreamArrow (->)

asStreamFun :: Mealy a b -> StreamFun a b
asStreamFun (Mealy f s0) = StreamArrow (go s0)
 where
   go s (Cons a as) = Cons b (go s' as) where (b,s') = f (a,s)

asArrow :: Op.ArrowCircuit k =>
           Mealy a b -> (a `k` b)
asArrow (Mealy f s0) = loop (arr f . second (Op.delay s0))

#endif

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

counter1 :: (ArrowCircuitT k a, Num a) => () `k` a
counter1 = loop (arr (\ ((),n) -> (n,n+1)) . second (delay 0))

-- Also works when the composed functions are swapped.

counter2 :: (ArrowCircuitT k a, Num a) => () `k` a
counter2 = proc () -> do rec old <- delay 0 -< new
                             new <- returnA -< old + 1
                         returnA -< old

testCounter :: Mealy () Int -> [Int]
testCounter counter = runMealy counter (replicate 10 ())

_testCounters :: [[Int]]
_testCounters = testCounter <$> [counter0,counter1,counter2]

-- *Circat.Mealy> _testCounters
-- [[0,1,2,3,4,5,6,7,8,9],[0,1,2,3,4,5,6,7,8,9],[0,1,2,3,4,5,6,7,8,9]]

adder0 :: (C a, Num a) => Mealy a a
adder0 = Mealy (\ (old,a) -> dup (old+a)) 0

adder1 :: (ArrowCircuitT k a, Num a) => a `k` a
adder1 = loop (arr (\ (a,tot) -> dup (tot+a)) . second (delay 0))

-- With arrow notation. Oops. Exclusive.
adder2 :: (ArrowCircuitT k a, Num a) => a `k` a
adder2 = proc a -> do rec tot <- delay 0 -< tot + a
                      returnA -< tot

-- With arrow notation. Inclusive.
adder3 :: (ArrowCircuitT k a, Num a) => a `k` a
adder3 = proc a -> do rec old <- delay 0 -< new
                          new <- returnA -< old + a
                      returnA -< new

-- Using let. Inclusive.
adder4 :: (ArrowCircuitT k a, Num a) => a `k` a
adder4 = proc a -> do rec old <- delay 0 -< new
                          let new = old + a
                      returnA -< new

testAdder :: Mealy Int Int -> [Int]
testAdder adder = runMealy adder [1..10]

_testAdders :: [[Int]]
_testAdders = testAdder <$> [adder0,adder1,adder2,adder3,adder4]

fibL1 :: Num a => [a]
fibL1 = fib' (0,1)
 where
   fib' (a,b) = a : fib' (b,a+b)

fibL2 :: Num a => [a]
fibL2 = 0 : 1 : zipWith (+) fibL2 (tail fibL2)

fib0 :: (C a, Num a) => Mealy () a
fib0 = Mealy (\ ((),(a,b)) -> (a,(b,a+b))) (0,1)

fib1 :: (C a, Num a) => Mealy () a
fib1 = loop (arr (\ ((),(a,b)) -> (a,(b,a+b))) . second (delay (0,1)))

fib2 :: (C a, Num a) => Mealy () a
fib2 = proc () -> do rec (a,b) <- delay (0,1) -< (b,a+b)
                     returnA -< a

fib3 :: (C a, Num a) => Mealy () a
fib3 = proc () -> do rec a <- delay 0 -< b
                         b <- delay 1 -< c
                         c <- returnA -< a+b
                     returnA -< a

testFib :: (C a, Num a) => Mealy () a -> [a]
testFib fib = runMealy fib (replicate 10 ())


_testFibs :: [[Int]]
_testFibs = (take 10 <$> [fibL1,fibL2]) ++ (testFib <$> [fib0,fib1,fib2,fib3])
