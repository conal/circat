{-# LANGUAGE ExistentialQuantification, ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Delay
-- Copyright   :  (c) 2015 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Partiality monad in direct and unfold forms
----------------------------------------------------------------------

module Circat.Delay where

-- TODO: explicit exports

import Control.Applicative (Applicative(..))

{--------------------------------------------------------------------
    Direct form
--------------------------------------------------------------------}

-- | Partiality monad in direct form
data Delay a = Later (Delay a) | Now a

instance Functor Delay where
  fmap f (Later d) = Later (fmap f d)
  fmap f (Now   a) = Now   (f a)

instance Applicative Delay where
  pure = Now
  Later df <*> Later dx = Later (df <*> dx)
  Later df <*> v = Later (df <*> v)
  Now f    <*> v = fmap f v

-- Note: remove the Later/Later case for sequential evaluation

instance Monad Delay where
  return = Now
  Later d >>= f = Later (d >>= f)
  Now   a >>= f = f a

-- Can a `Monad` instance agree with the Later df <*> Later dx?

{--------------------------------------------------------------------
    Unfold form
--------------------------------------------------------------------}

-- | Partiality monad in unfold form
data DelayU a = forall s. DelayU (s -> Either s a) s

-- TODO: Make the base functor explicit, and use in DelayU.
-- Then consider generalizing.

data DelayF a s = LaterF s | NowF a

-- | Semantics
mu :: DelayU a -> Delay a
mu (DelayU h s0) = go s0
 where
   go s = case h s of
            Left s' -> Later (go s')
            Right a -> Now a

instance Functor DelayU where
  fmap f (DelayU h s) = DelayU ((fmap.fmap) f h) s

instance Applicative DelayU where
  pure a = DelayU ((pure.pure) a) ()
  DelayU hf s0 <*> DelayU af t0 = DelayU bf (s0,t0)
   where
     bf (s,t) = case (hf s, af t) of
                  (Left s', Left t') -> Left (s',t')
                  (Left s', _)       -> Left (s',t )
                  (_, Left t')       -> Left (s ,t')
                  (Right f, Right a) -> Right (f a)

-- TODO: How to derive these instance from mu and the corresponding Delay instances?

instance Monad DelayU where
  return = pure
  DelayU af s0 >>= f = DelayU bf (Left s0)
   where
     bf (Left s) = case af s of
                     Left s' -> Left (Left s')
                     Right (f -> DelayU bf t0) -> undefined bf t0




-- f :: a -> DelayU b
-- f a :: DelayU b
-- Delay bf t0 = f a
-- bf :: t -> Either t b
-- t0 :: t

