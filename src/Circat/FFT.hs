{-# LANGUAGE CPP, Rank2Types, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds, ParallelListComp #-}
{-# LANGUAGE FlexibleContexts, TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}

{-# LANGUAGE UndecidableInstances #-} -- See below

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.FFT
-- Copyright   :  (c) 2015 Conal Elliott
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Generic FFT
----------------------------------------------------------------------

module Circat.FFT where

-- TODO: explicit exports

import Prelude hiding (sum)

import Data.Functor ((<$>))
import Data.Foldable (Foldable,sum,toList)
import Data.Traversable
import Control.Applicative (Applicative(..),liftA2)
import Data.Complex (Complex(..))

import Control.Compose ((:.)(..),inO,unO)
import TypeUnary.Nat (Nat(..),IsNat(..),natToZ,N0,N1,N2)

import Data.Newtypes.PrettyDouble

import Circat.Misc (transpose, inTranspose,Unop)
import Circat.Scan (LScan,lproducts,lsums,scanlT)
import Circat.Pair
import qualified Circat.LTree as L
import qualified Circat.RTree as R

{--------------------------------------------------------------------
    Statically sized functors
--------------------------------------------------------------------}

class Sized f where
  size :: f () -> Int -- ^ Argument is ignored at runtime

-- TODO: Switch from f () to f Void

-- The argument to size is unfortunate. When GHC Haskell has explicit type
-- application (<https://ghc.haskell.org/trac/ghc/wiki/TypeApplication>),
-- replace "size (undefined :: f ())" with "size @f", and likewise for g.
-- Meanwhile, a macro helps.

#define tySize(f) (size (undefined :: (f) ()))

-- | Useful default for 'size'.
sizeAF :: forall f. (Applicative f, Foldable f) => f () -> Int
sizeAF = const (sum (pure 1 :: f Int))

instance Sized Pair where size = const 2

instance (Sized g, Sized f) => Sized (g :. f) where
  size = const (tySize(g) * tySize(f))

instance IsNat n => Sized (L.Tree n) where
  size = const (twoNat (nat :: Nat n))

instance IsNat n => Sized (R.Tree n) where
  size = const (twoNat (nat :: Nat n))

-- | @2 ^ n@
twoNat :: Nat n -> Int
twoNat n = 2 ^ (natToZ n :: Int)

-- TODO: Generalize from Pair in L.Tree and R.Tree

-- TODO: Try using sizeAF instead of size, and see what happens. I think it'd
-- work but be much slower, either at compile- or run-time.

{--------------------------------------------------------------------
    FFT
--------------------------------------------------------------------}

type DFTTy f f' = forall a. RealFloat a => f (Complex a) -> f' (Complex a)

class (Sized f, Sized f') => FFT f f' | f -> f' where
  fft :: DFTTy f f'  -- refine later

instance ( Applicative f , Traversable f , Traversable g
         , Applicative f', Applicative g', Traversable g'
         , FFT f f', FFT g g', LScan g', LScan f)
      => FFT (g :. f) (f' :. g') where
  fft = inO (transpose . fmap fft . twiddle . inTranspose (fmap fft))

-- Without UndecidableInstances, I get the following:
-- 
--     Illegal instance declaration for ‘FFT (g :. f) (f' :. g')’
--       The coverage condition fails in class ‘FFT’
--         for functional dependency: ‘f -> f'’
--       Reason: lhs type ‘g :. f’ does not determine rhs type ‘f' :. g'’
--       Using UndecidableInstances might help
--     In the instance declaration for ‘FFT (g :. f) (f' :. g')’
--
-- What's going on here? Compiler bug? Misleading error message?

#if 0

-- Types in fft for (g :. f):

unO       :: (g :. f) a -> g  (f  a)
transpose :: g  (f  a)  -> f  (g  a)
fmap onG  :: f  (g  a)  -> f  (g' a)
transpose :: f  (g' a)  -> g' (f  a)
twiddle   :: g' (f  a)  -> g' (f  a)
fmap onF  :: g' (f  a)  -> g' (f' a)
transpose :: g' (f' a)  -> f' (g' a)
O         :: g  (f a)   -> (g :. f) a

#endif

type AFS h = (Applicative h, Foldable h, Sized h, LScan h)

twiddle :: (AFS g, AFS f, RealFloat a) => Unop (g (f (Complex a)))
twiddle = (liftA2.liftA2) (*) twiddles

-- Twiddle factors. Working here.
twiddles :: forall g f a. (AFS g, AFS f, RealFloat a) => g (f (Complex a))
twiddles = outerProduct pows muls
 where
   om   = omega (tySize(g :. f))
   pows = powers    om :: g (Complex a)
   muls = multiples om :: f (Complex a)

omega :: RealFloat a => Int -> Complex a
omega n = exp (- 2 * i * pi / fromIntegral n)

{--------------------------------------------------------------------
    Specialized FFT instances
--------------------------------------------------------------------}

-- Radix 2 butterfly
instance FFT Pair Pair where
  fft (a :# b) = (a + b) :# (a - b)

-- Handle trees by conversion to function composition:

instance IsNat n => FFT (L.Tree n) (R.Tree n) where
  fft = fft' nat
   where
     fft' :: Nat m -> DFTTy (L.Tree m) (R.Tree m)
     fft' Zero     = R.L          .        L.unL
     fft' (Succ _) = R.B . unO . fft . O . L.unB

instance IsNat n => FFT (R.Tree n) (L.Tree n) where
  fft = fft' nat
   where
     fft' :: Nat m -> DFTTy (R.Tree m) (L.Tree m)
     fft' Zero     = L.L          .        R.unL
     fft' (Succ _) = L.B . unO . fft . O . R.unB

-- TODO: explore deriving these instances using generic deriving

-- TODO: Do these instances amount to DIT and DIF respectively?

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- Powers of x, starting x^0. Uses 'LScan' for log parallel time
powers :: (LScan f, Applicative f, Num a) => a -> f a
powers = fst . lproducts . pure

-- Multiples of x, starting 0*x.  Uses 'LScan' for log parallel time
multiples :: (LScan f, Applicative f, Num a) => a -> f a
multiples = fst . lsums . pure

-- TODO: Consolidate with powers in TreeTest. Move powers and multiples to
-- LScan, and rename sensibly. Maybe use "Inc" and "Exc" suffixes to distinguish
-- inclusive and exclusive cases.

i :: Num a => Complex a
i = 0 :+ 1

-- | Generalized outer product
outer :: (Functor g, Functor f) => (a -> b -> c) -> g a -> f b -> g (f c)
outer h ga fb = (\ a -> h a <$> fb) <$> ga

-- | Outer product
outerProduct :: (Functor g, Functor f, Num a) => g a -> f a -> g (f a)
outerProduct = outer (*)

{--------------------------------------------------------------------
    Simple, quadratic DFT (for specification & testing)
--------------------------------------------------------------------}

-- Adapted from Dave's definition
dft :: RealFloat a => Unop [Complex a]
dft xs = [ sum [ x * (ok ^ n) | x <- xs | n <- [0 :: Int ..] ]
         | k <- [0 .. length xs - 1], let ok = om ^ k ]
 where
   om = omega (length xs)

{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

type C = Complex PrettyDouble

fftl :: (FFT f f', Foldable f', RealFloat a) => f (Complex a) -> [Complex a]
fftl = toList . fft

type LC n = L.Tree n C
type RC n = R.Tree n C

p1 :: Pair C
p1 = 1 :# 0

tw1 :: L.Tree N1 (Pair C)
tw1 = twiddles

tw2 :: L.Tree N2 (Pair C)
tw2 = twiddles

-- Adapted from Dave's testing
test :: (FFT f f', Foldable f, Foldable f') => f C -> IO ()
test xs =
  do ps "\nTesting input" (toList xs)
     ps "Expected output" (dft (toList xs))
     ps "Actual output  " (toList (fft xs))
 where
   ps :: Show z => String -> z -> IO ()
   ps label z = putStrLn (label ++ ": " ++ show z)

l0 :: [C]
l0 = [1]

t0 :: LC N0
t0 = L.fromList l0

l1 :: [C]
l1 = [1, 0]

t1 :: LC N1
t1 = L.fromList l1

l2 :: [C]
l2 = [1, 0, 0, 0]

t2 :: LC N2
t2 = L.fromList l2

tests :: IO ()
tests = do test t0
           test t1
           test t2
