{-# LANGUAGE CPP, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}  -- See below

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.If
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Class for conditionals
----------------------------------------------------------------------

module Circat.If (HasIf(..), muxBool, muxInt, repIf) where

import TypeUnary.Vec (Vec) -- ,Z,S

import Circat.Classes (muxB,muxI)
import Circat.Rep

-- | Conditional on boolean values, uncurried and with then/else swapped (for
-- trie consistency).
muxBool :: (Bool,(Bool,Bool)) -> Bool
muxBool = muxB
{-# NOINLINE muxBool #-}
-- Don't inline muxBool, since we have a primitive for it.

-- | Conditional on Int values, uncurried and with then/else swapped (for
-- trie consistency).
muxInt :: (Bool,(Int,Int)) -> Int
muxInt = muxI
{-# NOINLINE muxInt #-}
-- Don't inline muxInt, since we have a primitive for it.

class HasIf a where
  if_then_else :: Bool -> a -> a -> a
  -- TEMP hack
  temp_hack_HasIf :: a
  temp_hack_HasIf = undefined

instance HasIf Bool where
  if_then_else c a a' = muxBool (c,(a',a))  -- note reversal
  {-# INLINE if_then_else #-}

instance HasIf Int where
  if_then_else c a a' = muxInt (c,(a',a))  -- note reversal
  {-# INLINE if_then_else #-}

instance HasIf () where
  if_then_else _ () () = ()
  {-# INLINE if_then_else #-}

instance (HasIf s, HasIf t) => HasIf (s,t) where
  if_then_else c (s,t) (s',t') = (if_then_else c s s', if_then_else c t t')
  {-# INLINE if_then_else #-}

instance (HasIf s, HasIf t, HasIf u) => HasIf (s,t,u) where
  if_then_else = repIf

instance (HasIf s, HasIf t, HasIf u, HasIf v) => HasIf (s,t,u,v) where
  if_then_else = repIf

instance (HasIf s, HasIf t) => HasIf (s -> t) where
  if_then_else c f f' = \ s -> if_then_else c (f s) (f' s)
  {-# INLINE if_then_else #-}

repIf :: (HasRep a, HasIf (Rep a)) => Bool -> a -> a -> a
repIf c a a' = abst (if_then_else c (repr a) (repr a'))

instance (HasIf (Rep (Vec n a)), HasRep (Vec n a)) => HasIf (Vec n a) where
  if_then_else = repIf

--     Constraint is no smaller than the instance head
--       in the constraint: HasIf (Rep (Vec n a))
--     (Use UndecidableInstances to permit this)

-- instance HasIf (Vec Z a) where if_then_else = repIf
-- instance (HasIf (Vec n a), HasIf a) => HasIf (Vec (S n) a) where if_then_else = repIf
