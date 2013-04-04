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

import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad.State (State) -- mtl
-- import Control.Newtype (Newtype(..))

import Circat.Misc ((:*),(<~))
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

-- type instance Pins (a :+ b) = ???

{--------------------------------------------------------------------
    Circuit category
--------------------------------------------------------------------}

infixl 1 :>, :+>

-- Internal representation for '(:>)'.
type a :+> b = Pins a -> CircuitM (Pins b)

-- type a :+> b = Kleisli CircuitM (Pins a) (Pins b)

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
  id  = C pure
  (.) = inC2 (<=<)

-- instance CategoryProduct (:>) where
--   (***) = inC2 $ \ f g -> \ (a,b) -> 


-- -- | Category with product. Minimal definition: 'fst', 'snd', and either
-- -- (a) '(&&&)', (b) both '(***)' and 'dup', or (c) both '(&&&)' and '(***)'.
-- -- TODO: Generalize '(:*)' to an associated type. Keep the types fairly pretty.
-- class Category (~>) => CategoryProduct (~>) where
--   fst     :: (a :* b) ~> a
--   snd     :: (a :* b) ~> b
--   dup     :: a ~> (a :* a)
--   dup     =  id &&& id
--   swapP   :: (a :* b) ~> (b :* a)
--   swapP   =  snd &&& fst
--   (***)   :: (a ~> c) -> (b ~> d) -> ((a :* b) ~> (c :* d))
--   f *** g =  f . fst &&& g . snd
--   (&&&)   :: (a ~> c) -> (a ~> d) -> (a ~> (c :* d))
--   f &&& g =  (f *** g) . dup
--   first   :: (a ~> a') -> ((a :* b) ~> (a' :* b))
--   first   =  (*** id)
--   second  :: (b ~> b') -> ((a :* b) ~> (a :* b'))
--   second  =  (id ***)
--   lassocP :: (a :* (b :* c)) ~> ((a :* b) :* c)
--   lassocP =  second fst &&& (snd . snd)
--   rassocP :: ((a :* b) :* c) ~> (a :* (b :* c))
--   rassocP =  (fst . fst) &&& first  snd
