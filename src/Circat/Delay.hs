{-# LANGUAGE CPP, ExistentialQuantification, ViewPatterns #-}
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

data DelayU' a = forall s. DelayU' (s -> DelayF a s) s

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
                     Right (f -> d') -> Left (Right d')
     bf (Right (DelayU h t)) = case h t of
                                  Left t' -> Left (Right (DelayU h t'))
                                  Right b -> Right b

-- It's slightly simpler to define join instead (and use the standard definition
-- ma >>= f == join (fmap f ma)).

joinU :: DelayU (DelayU a) -> DelayU a
joinU (DelayU f s0) = DelayU h (Left s0)
   where
     h (Left s) = case f s of
                    Left s' -> Left (Left s')
                    Right d -> Left (Right d)
     h (Right (DelayU g t)) = case g t of
                                Left t' -> Left (Right (DelayU g t'))
                                Right a -> Right a

