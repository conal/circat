{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Circuit
-- Copyright   :  (c) 2013 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Circuit representation
----------------------------------------------------------------------

module Circat.Circuit where

-- TODO: explicit exports

import Prelude hiding (id,(.),fst,snd)
import qualified Prelude as P

import Control.Applicative
import Control.Monad (void,join,(>=>),(<=<))
import qualified Control.Arrow as A
import Control.Arrow (Kleisli(..))

import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad.State (State) -- mtl
-- import Control.Newtype (Newtype(..))

import Circat.Misc ((:*),(:+),(<~))
import Circat.Category

{--------------------------------------------------------------------
    The circuit monad
--------------------------------------------------------------------}

-- The circuit monad:
type CircuitM = State Maps

-- Stub for component type
type Comp = String

data Maps = Maps { comps :: IMap Comp, pins :: IMap Pin }

-- These two maps have a identifier supply (represented by the next free
-- identifier, which is an `Int`):

-- Identifier-indexed map with a supply
type IMap a = (Supply, Map Id a)

newtype Id = Id Int
type Supply = Id  -- Next free Id

-- A pin is defined as a component ID and output pin number:

type Pin = (Id,PinIdx)

newtype PinIdx = PinIdx Int

{--------------------------------------------------------------------
    Pins
--------------------------------------------------------------------}

-- The Pins type family gives a representation for a type in terms of structures of pins.

type  family  Pins t

type instance Pins ()       = ()
type instance Pins Bool     = Pin
type instance Pins (a :* b) = Pins a :* Pins b
type instance Pins (a :+ b) = Pins a :+ Pins b   -- ???

{--------------------------------------------------------------------
    Circuit category
--------------------------------------------------------------------}

infixl 1 :>, :+>

-- | Internal representation for '(:>)'.
type a :+> b = Kleisli CircuitM (Pins a) (Pins b)

-- type a :+> b = Pins a -> CircuitM (Pins b)


-- First shot at circuit category
newtype a :> b = C { unC :: a :+> b }

-- instance Newtype (a :> b) (Pins a -> CircuitM (Pins b)) where
--   pack = C
--   unpack = unC

--     Illegal type synonym family application in instance.
--
-- So define manually:

inC :: (a :+> b -> a' :+> b') -> (a :> b -> a' :> b')
inC = C <~ unC

inC2 :: (a :+> b -> a' :+> b' -> a'' :+> b'')
     -> (a :> b -> a' :> b' -> a'' :> b'')
inC2 = inC <~ unC

instance Category (:>) where
  id  = C id
  (.) = inC2 (.)

instance CategoryProduct (:>) where
  fst   = C fst
  snd   = C snd
  dup   = C dup
  (***) = inC2 (***)
  (&&&) = inC2 (&&&)

instance CategoryCoproduct (:>) where
  lft       = C lft
  rht       = C rht
  jam       = C jam
  ldistribS = C ldistribS
  rdistribS = C rdistribS
  (+++)     = inC2 (+++)
  (|||)     = inC2 (|||)

-- TODO: Reconsider this CategoryCoproduct instance, which relies on the dubious
-- 
--   type instance Pins (a :+ b) = Pins a :+ Pins b.

