{-# LANGUAGE CPP #-}
{-# LANGUAGE ExistentialQuantification, TupleSections, TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables, Arrows #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

module Circat.Mealy (Mealy(..)) where

import Prelude hiding (id,(.))
import Control.Category
import Control.Applicative ((<$>), Applicative(..))
import Data.Tuple (swap)

import Control.Arrow
import Control.Arrow.Operations

import Circat.Misc ((:*))

data Mealy a b = forall s. Mealy ((s,a) -> (s,b)) s

-- TODO: Perhaps generalize Mealy to an arrow transformer.

instance Category Mealy where
  id = Mealy id ()
  Mealy g t0 . Mealy f s0 = Mealy h (s0,t0)
   where
     h ((s,t),a) = ((s',t'),c)
      where
        (s',b) = f (s,a)
        (t',c) = g (t,b)

instance Arrow Mealy where
  arr f = Mealy (second f) ()
  Mealy f s0 *** Mealy g t0 = Mealy h (s0,t0)
   where
     h = transP2 . (f *** g) . transP2
  first  f = f *** id
  second g = id *** g

transP2 :: ((p :* q) :* (r :* s)) -> ((p :* r) :* (q :* s))
transP2 ((p,q),(r,s)) = ((p,r),(q,s))

instance ArrowChoice Mealy where
  Mealy f s0 +++ Mealy g t0 = Mealy h (s0,t0)
   where
     h ((s,t),Left  a) = ((s',t), Left  c) where (s',c) = f (s,a)
     h ((s,t),Right b) = ((s,t'), Right d) where (t',d) = g (t,b)
  left  f = f +++ id
  right g = id +++ g

instance ArrowLoop Mealy where
  loop (Mealy f s0) = Mealy (loop (lassocP . f . rassocP)) s0

lassocP :: (a,(b,c)) -> ((a,b),c)
lassocP (a,(b,c)) = ((a,b),c)
rassocP :: ((a,b),c) -> (a,(b,c))
rassocP ((a,b),c) = (a,(b,c))

instance ArrowCircuit Mealy where
  delay = Mealy swap

-- delay a = Mealy (\ (s,a) -> (a,s)) a

runMealy :: Mealy a b -> [a] -> [b]
runMealy (Mealy f s0) = go s0
 where
   go _ []     = []
   go s (a:as) = b : go s' as where (s',b) = f (s,a)

{--------------------------------------------------------------------
    Standard instances for arrows
--------------------------------------------------------------------}

instance Functor (Mealy a) where fmap = flip (>>^)
instance Applicative (Mealy a) where
  pure b = arr (const b)
  fs <*> xs = uncurry ($) <$> (fs &&& xs)

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

dup :: Arrow k => a `k` (a :* a)
dup = id &&& id

serialSum0 :: Num a => Mealy a a
serialSum0 = Mealy (\ (old,a) -> dup (old+a)) 0

serialSum1 :: (ArrowCircuit k, Num a) => k a a
serialSum1 = loop (arr (\ (a,tot) -> dup (tot+a)) . second (delay 0))

-- With arrow notation. Oops. Exclusive.
serialSum2 :: (ArrowCircuit k, Num a) => k a a
serialSum2 = proc a -> do rec tot <- delay 0 -< tot + a
                          returnA -< tot

-- With arrow notation. Inclusive.
serialSum3 :: (ArrowCircuit k, Num a) => k a a
serialSum3 = proc a -> do rec old <- delay 0 -< new
                              new <- returnA -< old + a
                          returnA -< new

-- Using let. Inclusive.
serialSum4 :: (ArrowCircuit k, Num a) => k a a
serialSum4 = proc a -> do rec old <- delay 0 -< new
                              let new = old + a
                          returnA -< new

-- [1,3,6,10,15,21,28,36,45,55]
_ms0 :: [Int]
_ms0 = runMealy serialSum0 [1..10]

-- [1,3,6,10,15,21,28,36,45,55]
_ms1 :: [Int]
_ms1 = runMealy serialSum1 [1..10]

-- [0,1,3,6,10,15,21,28,36,45]
_ms2 :: [Int]
_ms2 = runMealy serialSum2 [1..10]

-- [1,3,6,10,15,21,28,36,45,55]
_ms3 :: [Int]
_ms3 = runMealy serialSum3 [1..10]

-- [1,3,6,10,15,21,28,36,45,55]
_ms4 :: [Int]
_ms4 = runMealy serialSum4 [1..10]

-- Counter

counter0 :: Num a => Mealy () a
counter0 = Mealy (\ (old,()) -> dup (old+1)) 0

counter1 :: (ArrowCircuit k, Num a) => k () a
counter1 = loop (arr (\ ((),tot) -> dup (tot+1)) . second (delay 0))

counter2 :: (ArrowCircuit k, Num a) => k () a
counter2 = proc () -> do rec old <- delay 0 -< new
                             new <- returnA -< old + 1
                         returnA -< new

-- [1,2,3,4,5,6,7,8,9,10]
_mc0 :: [Int]
_mc0 = runMealy counter0 (replicate 10 ())

-- [1,2,3,4,5,6,7,8,9,10]
_mc1 :: [Int]
_mc1 = runMealy counter1 (replicate 10 ())

-- [1,2,3,4,5,6,7,8,9,10]
_mc2 :: [Int]
_mc2 = runMealy counter2 (replicate 10 ())

