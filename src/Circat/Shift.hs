{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators, TypeFamilies #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Shift
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Shift values through structures
----------------------------------------------------------------------

module Circat.Shift (accumL, accumR, shiftL, shiftR) where

import Prelude hiding (zip,unzip,zipWith)

import Data.Traversable (Traversable(..)) -- ,mapAccumR
import Control.Applicative (Applicative(..))
import Data.Tuple (swap)

import Circat.Misc ((:*))
import Circat.Rep

-- Utilities

-- | Swap domain
swapD :: (a :* b -> c) -> (b :* a -> c)
swapD = (. swap)

-- | Swap range
swapR :: (a -> b :* c) -> (a -> c :* b)
swapR = (swap .)

-- | Accumulate rightward
accumR :: Traversable t => (a :* b -> c :* a) -> (a :* t b -> t c :* a)
accumR = swapR . uncurry . mapAccumL . curry . swapR

#if 0
mapAccumL :: Traversable t => (a -> b -> a :* c) -> a -> t b -> a :* t c

h :: a :* b -> c :* a
swapR h :: a :* b -> a :* c
curry (swapR h) :: a -> b -> a :* c
mapAccumL (curry (swapR h)) :: a -> t b -> a :* t c
uncurry (mapAccumL (curry (swapR h))) :: a :* t b -> a :* t c
swapR uncurry (mapAccumL (curry (swapR h))) :: a :* t b -> t c :* a
#endif

-- | Accumulate leftward
accumL :: Traversable t => (c :* a -> a :* b) -> (t c :* a -> a :* t b)
accumL = swapD . uncurry . mapAccumR . curry . swapD

#if 0
mapAccumR :: Traversable t => (a -> c -> a :* b) -> a -> t c -> a :* t b

h :: c :* a -> a :* b
swapD h :: a :* c -> a :* b
curry (swapD h) :: a -> c -> a :* b
mapAccumR (curry (swapD h)) :: a -> t c -> a :* t b
uncurry (mapAccumR (curry (swapD h))) :: a :* t c -> a :* t b
swapD (uncurry (mapAccumR (curry (swapD h)))) :: t c :* a -> a :* t b
#endif

-- accumL = (inSwapD.inCurry) mapAccumR
-- accumR = (inSwapR.inCurry) mapAccumL

-- | Shift a value leftward (from the right)
shiftL :: Traversable t => t a :* a -> a :* t a
shiftL = accumL id
-- shiftL (as,a') = mapAccumR (flip (,)) a' as

-- | Shift a value rightward (from the left)
shiftR :: Traversable t => a :* t a -> t a :* a
shiftR = accumR id
-- shiftR (a',as) = swap (mapAccumL (flip (,)) a' as)

-- Note id instead of swap, which I discovered in testing.
-- To do: rethink.

{--------------------------------------------------------------------
    From Data.Traversable
--------------------------------------------------------------------}

-- I had to copy this code, because Data.Traversable doesn't export StateR, and
-- I need a HasRep instance.
-- TODO: Fix compilation to synthesize HasRep instances when they're missing.

-- left-to-right state transformer
newtype StateL s a = StateL { runStateL :: s -> (s, a) }

instance Functor (StateL s) where
    fmap f (StateL k) = StateL $ \ s -> let (s', v) = k s in (s', f v)

instance Applicative (StateL s) where
    pure x = StateL (\ s -> (s, x))
    StateL kf <*> StateL kv = StateL $ \ s ->
        let (s', f) = kf s
            (s'', v) = kv s'
        in (s'', f v)

-- |The 'mapAccumL' function behaves like a combination of 'fmap'
-- and 'foldl'; it applies a function to each element of a structure,
-- passing an accumulating parameter from left to right, and returning
-- a final value of this accumulator together with the new structure.
mapAccumL :: Traversable t => (a -> b -> (a, c)) -> a -> t b -> (a, t c)
mapAccumL f s t = runStateL (traverse (StateL . flip f) t) s

-- right-to-left state transformer
newtype StateR s a = StateR { runStateR :: s -> (s, a) }

instance Functor (StateR s) where
    fmap f (StateR k) = StateR $ \ s -> let (s', v) = k s in (s', f v)

instance Applicative (StateR s) where
    pure x = StateR (\ s -> (s, x))
    StateR kf <*> StateR kv = StateR $ \ s ->
        let (s', v) = kv s
            (s'', f) = kf s'
        in (s'', f v)

-- |The 'mapAccumR' function behaves like a combination of 'fmap'
-- and 'foldr'; it applies a function to each element of a structure,
-- passing an accumulating parameter from right to left, and returning
-- a final value of this accumulator together with the new structure.
mapAccumR :: Traversable t => (a -> b -> (a, c)) -> a -> t b -> (a, t c)
mapAccumR f s t = runStateR (traverse (StateR . flip f) t) s

-- Add HasRep instances

type instance Rep (StateL s a) = s -> s :* a
instance HasRep (StateL s a) where
  abst = StateL
  repr = runStateL

type instance Rep (StateR s a) = s -> s :* a
instance HasRep (StateR s a) where
  abst = StateR
  repr = runStateR
