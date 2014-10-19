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

module Circat.Mealy where

-- TODO: explicit exports

import Prelude hiding (id,(.))
import Control.Category
import Data.Tuple (swap)

import Control.Arrow
import Control.Arrow.Operations
import Control.Arrow.Transformer.Automaton

import Circat.Misc ((:*),(:+))

data Mealy a b = forall s. Mealy ((s,a) -> (s,b)) s

counter :: Mealy () Int
counter = Mealy (\ (n,()) -> (n+1,n)) 0

instance Category Mealy where
  id = Mealy id ()
  Mealy g t0 . Mealy f s0 = Mealy h (s0,t0)
   where
     h ((s,t),a) = ((s',t'),c)
      where
        (s',b) = f (s,a)
        (t',c) = g (t,b)

exl :: Arrow k => (a :* b) `k` a
exl = arr fst
exr :: Arrow k => (a :* b) `k` b
exr = arr snd

inl :: ArrowChoice k => a `k` (a :+ b)
inl = arr Left
inr :: ArrowChoice k => b `k` (a :+ b)
inr = arr Right

dup :: Arrow k => a `k` (a :* a)
dup = id &&& id

lassocP :: Arrow k => (a :* (b :* c)) `k` ((a :* b) :* c)
lassocP =  second exl &&& (exr . exr)
rassocP :: Arrow k => ((a :* b) :* c) `k` (a :* (b :* c))
rassocP =  (exl . exl) &&& first  exr

instance Arrow Mealy where
  arr f = Mealy (second f) ()
  Mealy f s0 *** Mealy g t0 = Mealy h (s0,t0)
   where
     h = transP2 . (f *** g) . transP2
  first  f = f *** id
  second g = id *** g

instance ArrowChoice Mealy where
  Mealy f s0 +++ Mealy g t0 = Mealy h (s0,t0)
   where
     h ((s,t),Left  a) = ((s',t), Left  c) where (s',c) = f (s,a)
     h ((s,t),Right b) = ((s,t'), Right d) where (t',d) = g (t,b)
  left  f = f +++ id
  right g = id +++ g

instance ArrowLoop Mealy where
  loop (Mealy f s0) = Mealy (loop (lassocP . f . rassocP)) s0

instance ArrowCircuit Mealy where
  delay = Mealy swap

-- delay a = Mealy (\ (s,a) -> (a,s)) a

transP2 :: ((p :* q) :* (r :* s)) -> ((p :* r) :* (q :* s))
transP2 ((p,q),(r,s)) = ((p,r),(q,s))

-- TODO: Rewritten with just categorical vocabulary

transP2' :: ((p :* q) :* (r :* s)) -> ((p :* r) :* (q :* s))
transP2' = (exl.exl &&& exl.exr) &&& (exr.exl &&& exr.exr)

transS2 :: ((p :+ q) :+ (r :+ s)) -> ((p :+ r) :+ (q :+ s))
transS2 (Left  (Left  p)) = Left  (Left  p)
transS2 (Left  (Right q)) = Right (Left  q)
transS2 (Right (Left  r)) = Left  (Right r)
transS2 (Right (Right s)) = Right (Right s)

-- TODO: Rewritten with just categorical vocabulary

transS2' :: ((p :+ q) :+ (r :+ s)) -> ((p :+ r) :+ (q :+ s))
transS2' = (inl.inl ||| inr.inl) ||| (inl.inr ||| inr.inr)

runMealy :: Mealy a b -> [a] -> [b]
runMealy (Mealy f s0) = go s0
 where
   go _ []     = []
   go s (a:as) = b : go s' as where (s',b) = f (s,a)

-- For comparison
type Aut = Automaton (->)

runAut :: Aut a b -> [a] -> [b]
runAut _ [] = []
runAut (Automaton f) (a:as) = b : runAut aut' as
 where
   (b,aut') = f a

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

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
m1 :: [Int]
m1 = runMealy serialSum1 [1..10]

-- [0,1,3,6,10,15,21,28,36,45]
m2 :: [Int]
m2 = runMealy serialSum2 [1..10]

-- [1,3,6,10,15,21,28,36,45,55]
m3 :: [Int]
m3 = runMealy serialSum3 [1..10]

-- [1,3,6,10,15,21,28,36,45,55]
m4 :: [Int]
m4 = runMealy serialSum4 [1..10]

-- [1,3,6,10,15,21,28,36,45,55]
a1 :: [Int]
a1 = runAut serialSum1 [1..10]

-- [0,1,3,6,10,15,21,28,36,45]
a2 :: [Int]
a2 = runAut serialSum2 [1..10]

-- [1,3,6,10,15,21,28,36,45,55]
a3 :: [Int]
a3 = runAut serialSum3 [1..10]

-- [1,3,6,10,15,21,28,36,45,55]
a4 :: [Int]
a4 = runAut serialSum4 [1..10]
