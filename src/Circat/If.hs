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

module Circat.If (HasIf(..), repIf) where

import TypeUnary.Vec (Vec) -- ,Z,S

import Circat.Rep

-- | Conditional on boolean values, uncurried and with then/else swapped (for
-- trie consistency).
muxB :: (Bool,(Bool,Bool)) -> Bool
muxB (i,(e,t)) = (i && t) || (not i && e)  -- note then/else swap
{-# NOINLINE muxB #-}
-- Don't inline muxB, since we have a primitive for it.

class HasIf a where
  if_then_else :: Bool -> a -> a -> a
  -- TEMP hack
  temp_hack_HasIf :: a
  temp_hack_HasIf = undefined

instance HasIf Bool where
  if_then_else c a a' = muxB (c,(a',a))  -- note reversal
  {-# INLINE if_then_else #-}

instance HasIf () where
  if_then_else _ () () = ()
  {-# INLINE if_then_else #-}

instance (HasIf s, HasIf t) => HasIf (s,t) where
  if_then_else c (s,t) (s',t') = (if_then_else c s s', if_then_else c t t')
  {-# INLINE if_then_else #-}

#if 0
-- We'll get triples and quadruples via HasRep
instance (HasIf s, HasIf t, HasIf u) => HasIf (s,t,u) where
  if_then_else c (s,t,u) (s',t',u') =
    ( if_then_else c s s'
    , if_then_else c t t'
    , if_then_else c u u' )
  {-# INLINE if_then_else #-}

instance (HasIf s, HasIf t, HasIf u, HasIf v) => HasIf (s,t,u,v) where
  if_then_else c (s,t,u,v) (s',t',u',v') =
    ( if_then_else c s s'
    , if_then_else c t t'
    , if_then_else c u u'
    , if_then_else c v v'
    )
  {-# INLINE if_then_else #-}
#endif

instance (HasIf s, HasIf t) => HasIf (s -> t) where
  if_then_else c f f' = \ s -> if_then_else c (f s) (f' s)
  {-# INLINE if_then_else #-}

repIf :: (HasRep a, HasIf (Rep a)) => Bool -> a -> a -> a
repIf c a a' = abst (if_then_else c (repr a) (repr a'))

instance (HasIf (Rep (Vec n a)), HasRep (Vec n a)) =>
  HasIf (Vec n a) where if_then_else = repIf

--     Constraint is no smaller than the instance head
--       in the constraint: HasIf (Rep (Vec n a))
--     (Use UndecidableInstances to permit this)

-- instance HasIf (Vec Z a) where if_then_else = repIf
-- instance (HasIf (Vec n a), HasIf a) => HasIf (Vec (S n) a) where if_then_else = repIf
