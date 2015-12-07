{-# LANGUAGE CPP, Rank2Types, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds, ParallelListComp #-}
{-# LANGUAGE FlexibleContexts, TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE UndecidableInstances #-} -- See below

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

#define TESTING

#ifdef TESTING
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP
#endif

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

module Circat.FFT
  ( Sized(..), sizeAF, FFT(..), DFTTy
  -- Temporary while debugging
  , twiddle, twiddles, omega, cis
  ) where

-- TODO: explicit exports

import Prelude hiding (sum,product)

import Data.Functor ((<$>))
import Data.Foldable (Foldable,toList,sum,product)
import Data.Traversable
import Control.Applicative (Applicative(..),liftA2)

import Test.QuickCheck.All (quickCheckAll)

import Control.Compose ((:.)(..),inO,unO)
import TypeUnary.Nat (Nat(..),IsNat(..),natToZ,N0,N1,N2,N3,N4)

import Data.Newtypes.PrettyDouble

import Circat.Complex
import Circat.Misc (transpose, inTranspose,Unop,Binop)
import Circat.Scan (LScan,lproducts,lsums,scanlT,iota)
import Circat.ApproxEq (ApproxEq(..))
import Circat.Pair
import qualified Circat.LTree as L
import qualified Circat.RTree as R


{--------------------------------------------------------------------
    Statically sized functors
--------------------------------------------------------------------}

class Sized f where
  size :: f () -> Int -- ^ Argument is ignored at runtime
  -- Temporary hack to avoid newtype-like representation.
  sizeDummy :: f a
  sizeDummy = undefined

-- TODO: Switch from f () to f Void

-- The argument to size is unfortunate. When GHC Haskell has explicit type
-- application (<https://ghc.haskell.org/trac/ghc/wiki/TypeApplication>),
-- replace "size (undefined :: f ())" with "size @f".
-- Meanwhile, a macro helps.

#define tySize(f) (size (undefined :: (f) ()))

-- | Useful default for 'size'.
sizeAF :: forall f. (Applicative f, Foldable f) => f () -> Int
sizeAF = const (sum (pure 1 :: f Int))

instance (Sized g, Sized f) => Sized (g :. f) where
  size = const (tySize(g) * tySize(f))
  {-# INLINE size #-}

instance Sized Pair where
  size = const 2
  {-# INLINE size #-}

-- | @2 ^ n@
twoNat :: Integral m => Nat n -> m
twoNat n = 2 ^ (natToZ n :: Int)

instance IsNat n => Sized (L.Tree n) where
  size = const (twoNat (nat :: Nat n))
  {-# INLINE size #-}

instance IsNat n => Sized (R.Tree n) where
  size = const (twoNat (nat :: Nat n))
  {-# INLINE size #-}

-- TODO: Generalize from Pair in L.Tree and R.Tree

-- TODO: Try using sizeAF instead of size, and see what happens. I think it'd
-- work but be much slower, either at compile- or run-time.

{--------------------------------------------------------------------
    FFT
--------------------------------------------------------------------}

type DFTTy f f' = forall a. RealFloat a => f (Complex a) -> f' (Complex a)

class FFT f f' | f -> f' where
  fft :: DFTTy f f'
  -- Temporary hack to avoid newtype-like representation.
  fftDummy :: f a
  fftDummy = undefined

instance ( Applicative f , Traversable f , Traversable g
         , Applicative f', Applicative g', Traversable g'
         , FFT f f', FFT g g', LScan f, LScan g', Sized f, Sized g' )
      => FFT (g :. f) (f' :. g') where
  fft = inO (transpose . fmap fft . twiddle . transpose . fmap fft . transpose)
  {-# INLINE fft #-}

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

twiddle :: forall g f a. (AFS g, AFS f, RealFloat a) => Unop (g (f (Complex a)))
twiddle = (liftA2.liftA2) (*) (twiddles (tySize(g :. f)))
{-# INLINE twiddle #-}

-- Twiddle factors.
twiddles :: (AFS g, AFS f, RealFloat a) => Int -> g (f (Complex a))
twiddles n = powers <$> powers (omega n)
{-# INLINE twiddles #-}

omega :: (Integral n, RealFloat a) => n -> Complex a
omega n = cis (- 2 * pi / fromIntegral n)
-- omega n = exp (0 :+ (- 2 * pi / fromIntegral n))
-- omega n = exp (- 2 * (0:+1) * pi / fromIntegral n)
{-# INLINE omega #-}

-- | @'exp' (i * a)
cis :: RealFloat a => a -> Complex a
cis a = cos a :+ sin a

-- Powers of x, starting x^0. Uses 'LScan' for log parallel time
powers :: (LScan f, Applicative f, Num a) => a -> f a
powers = fst . lproducts . pure
{-# INLINE powers #-}

-- TODO: Consolidate with powers in TreeTest and rename sensibly. Maybe use
-- "In" and "Ex" suffixes to distinguish inclusive and exclusive cases.

{--------------------------------------------------------------------
    Specialized FFT instances.
--------------------------------------------------------------------}

-- I put the specific instances here in order to avoid an import loop between
-- LTree and RTree.

-- Radix 2 butterfly
instance FFT Pair Pair where
  fft (a :# b) = (a + b) :# (a - b)
  {-# INLINE fft #-}

-- Handle trees by conversion to functor compositions.

instance IsNat n => FFT (L.Tree n) (R.Tree n) where
  fft = fftL nat
  {-# INLINE fft #-}

fftL :: Nat m -> DFTTy (L.Tree m) (R.Tree m)
fftL Zero     = R.L          .        L.unL
fftL (Succ _) = R.B . unO . fft . O . L.unB
{-# INLINE fftL #-}

instance IsNat n => FFT (R.Tree n) (L.Tree n) where
  fft = fftR nat
  {-# INLINE fft #-}

fftR :: Nat m -> DFTTy (R.Tree m) (L.Tree m)
fftR Zero     = L.L          .        R.unL
fftR (Succ _) = L.B . unO . fft . O . R.unB
{-# INLINE fftR #-}

-- TODO: Do these instances amount to DIT and DIF respectively?
-- TODO: Remove the boilerplate via DeriveGeneric.
-- TODO: functor products and sums
-- TODO: Pair via Identity and functor product.

#ifdef TESTING

{--------------------------------------------------------------------
    Simple, quadratic DFT (for specification & testing)
--------------------------------------------------------------------}

-- Adapted from Dave's definition
dft :: RealFloat a => Unop [Complex a]
dft xs = [ sum [ x * ok^n | x <- xs | n <- [0 :: Int ..] ]
         | k <- [0 .. length xs - 1], let ok = om ^ k ]
 where
   om = omega (length xs)

-- Generalization of 'dft' to traversables. Warning: use only on zippy
-- applicatives (not on []).
dftT :: forall f a. (AFS f, Traversable f, RealFloat a) => Unop (f (Complex a))
dftT xs = out <$> indices
 where
   out k = sum (liftA2 (\ n x -> x * ok^n) indices xs)
    where ok = om ^ k
   indices = iota :: f Int
   om = omega (tySize(f))

-- TODO: Replace Applicative with Zippable

-- Perhaps dftT isn't very useful. Its result and argument types match, unlike fft.

dftQ :: forall f a. (AFS f, RealFloat a) => Unop (f (Complex a))
dftQ as = (<.> as) <$> twiddles (tySize(f))
{-# INLINE dftQ #-}

-- Binary dot product
infixl 7 <.>
(<.>) :: (Foldable f, Applicative f, Num a) => f a -> f a -> a
u <.> v = sum (liftA2 (*) u v)

{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

-- > powers 2 :: L.Tree N2 Int
-- B (B (L ((1 :# 2) :# (4 :# 8))))
-- > powers 2 :: L.Tree N3 Int
-- B (B (B (L (((1 :# 2) :# (4 :# 8)) :# ((16 :# 32) :# (64 :# 128))))))

type C = Complex {-Pretty-}Double

fftl :: (FFT f f', Foldable f', RealFloat a) => f (Complex a) -> [Complex a]
fftl = toList . fft

type LC n = L.Tree n C
type RC n = R.Tree n C

p1 :: Pair C
p1 = 1 :# 0

tw1 :: L.Tree N1 (Pair C)
tw1 = twiddles (tySize (L.Tree N1 :. Pair))

tw2 :: L.Tree N2 (Pair C)
tw2 = twiddles (tySize (L.Tree N2 :. Pair))

-- Adapted from Dave's testing

test :: (FFT f f', Foldable f, Foldable f') => f C -> IO ()
test fx =
  do ps "\nTesting input" xs
     ps "Expected output" (dft xs)
     ps "Actual output  " (toList (fft fx))
 where
   ps label z = putStrLn (label ++ ": " ++ show z)
   xs = toList fx

t0 :: LC N0
t0 = L.fromList [1]

t1 :: LC N1
t1 = L.fromList [1, 0]

t2s :: [LC N2]
t2s = L.fromList <$>
        [ [1,  0,  0,  0]  -- Delta
        , [1,  1,  1,  1]  -- Constant
        , [1, -1,  1, -1]  -- Nyquist
        , [1,  0, -1,  0]  -- Fundamental
        , [0,  1,  0, -1]  -- Fundamental w/ 90-deg. phase lag
       ]

tests :: IO ()
tests = do test p1
           test t0
           test t1
           mapM_ test t2s

-- infix 4 ===
-- (===) :: Eq b => (a -> b) -> (a -> b) -> a -> Bool
-- (f === g) x = f x == g x

infix 4 =~=
(=~=) :: ApproxEq b => (a -> b) -> (a -> b) -> a -> Bool
(f =~= g) x = f x =~ g x

fftIsDft :: (FFT f f', Foldable f, Foldable f', RealFloat a, ApproxEq a) =>
            f (Complex a) -> Bool
fftIsDft = toList . fft =~= dft . toList

dftTIsDft :: (AFS f, Traversable f, RealFloat a, ApproxEq a) =>
            f (Complex a) -> Bool
dftTIsDft = toList . dftT =~= dft . toList

dftQIsDft :: (AFS f, Traversable f, RealFloat a, ApproxEq a) =>
            f (Complex a) -> Bool
dftQIsDft = toList . dftQ =~= dft . toList

{--------------------------------------------------------------------
    Properties to test
--------------------------------------------------------------------}

-- PrettyDouble doesn't yet have an Arbitrary instance, so use Double for now
type C' = Complex Double

transposeTwiddleCommutes :: (AFS g, Traversable g, AFS f, (ApproxEq (f (g C'))))
                         => g (f C') -> Bool
transposeTwiddleCommutes =
 twiddle . transpose =~= twiddle . transpose

prop_transposeTwiddle_L3P :: L.Tree N3 (Pair C') -> Bool
prop_transposeTwiddle_L3P = transposeTwiddleCommutes

prop_transposeTwiddle_R3P :: R.Tree N3 (Pair C') -> Bool
prop_transposeTwiddle_R3P = transposeTwiddleCommutes

prop_dftQ_R3 :: R.Tree N3 C' -> Bool
prop_dftQ_R3 = dftQIsDft

prop_dftQ_L3 :: L.Tree N3 C' -> Bool
prop_dftQ_L3 = dftQIsDft

prop_dftT_p :: Pair C' -> Bool
prop_dftT_p = dftTIsDft

prop_dftT_L3 :: L.Tree N3 C' -> Bool
prop_dftT_L3 = dftTIsDft

prop_dftT_R3 :: R.Tree N3 C' -> Bool
prop_dftT_R3 = dftTIsDft

prop_fft_p :: Pair C' -> Bool
prop_fft_p = fftIsDft

prop_fft_L1 :: L.Tree N1 C' -> Bool
prop_fft_L1 = fftIsDft

prop_fft_L2 :: L.Tree N2 C' -> Bool
prop_fft_L2 = fftIsDft

prop_fft_L3 :: L.Tree N3 C' -> Bool
prop_fft_L3 = fftIsDft

prop_fft_L4 :: L.Tree N4 C' -> Bool
prop_fft_L4 = fftIsDft

prop_fft_R1 :: R.Tree N1 C' -> Bool
prop_fft_R1 = fftIsDft

prop_fft_R2 :: R.Tree N2 C' -> Bool
prop_fft_R2 = fftIsDft

prop_fft_R3 :: R.Tree N3 C' -> Bool
prop_fft_R3 = fftIsDft

prop_fft_R4 :: R.Tree N4 C' -> Bool
prop_fft_R4 = fftIsDft

-- TH oddity
return []

runTests :: IO Bool
runTests = $quickCheckAll

-- end of tests
#endif
