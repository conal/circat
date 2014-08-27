{-# LANGUAGE TypeOperators, TypeFamilies, ConstraintKinds, GADTs, CPP #-}
{-# LANGUAGE Rank2Types, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-} -- see below

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Classes
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Additional type classes for circuit-friendly operations
----------------------------------------------------------------------

module Circat.Classes where

-- TODO: explicit exports

import Prelude hiding (id,(.),const,not,and,or,curry,uncurry)
import qualified Prelude as P
import Control.Arrow (arr,Kleisli)

import Circat.Misc ((:*))
import Circat.Category

-- | Category with boolean operations.
class ProductCat k => BoolCat k where
  not :: Bool `k` Bool
  and, or, xor :: (Bool :* Bool) `k` Bool

-- The Category superclass is just for convenience.

instance BoolCat (->) where
  not = P.not
  and = P.uncurry (&&)
  or  = P.uncurry (||)
  xor = P.uncurry (/=)

-- HACK: generalize/replace/...
class NumCat k a where
  add, mul :: (a :* a) `k` a

instance Num a => NumCat (->) a where
  add = uncurry (+)
  mul = uncurry (*)

instance (Monad m, Num a) => NumCat (Kleisli m) a where
  add = arr add
  mul = arr mul

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- | One-bit mux
class MuxCat k where
  mux :: (Bool :* (Bool :* Bool)) `k` Bool

instance MuxCat (->) where
  mux (i,(e,t)) = (i && t) || (not i && e)
