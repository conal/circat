{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

import Control.Monad.Trans.State (State,get,put,runState) -- transformers

import Circat.Misc ((:*),(:+),(<~),Unop)
import Circat.Category
import Circat.Classes

{--------------------------------------------------------------------
    The circuit monad
--------------------------------------------------------------------}

-- The circuit monad:
type CircuitM = State Maps

-- Primitive (stub)
type Prim = String

-- Component: primitive instance with input sources
data Comp = Comp Prim [Pin]

-- data Comp = forall a b. HasPins2 a b => Comp Prim [Pin]

-- TODO: Phantom type parameters for Prim

data Maps = Maps { compMap :: IMap Comp, pinMap :: IMap Pin }

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

sourceToPins :: forall a. HasPins a => Source a -> [Pin]
sourceToPins = ($ []) . toPins (error "toPins: dummy argument" :: a)

pinsToSource :: forall a. HasPins a => [Pin] -> Source a
pinsToSource pins | null rest = src
                  | otherwise = error "pinsToSource: wrong number of pins"
 where
   (src,rest) = runState (fromPins (error "fromPins dummy argument" :: a)) pins

-- The Source type family gives a representation for a type in terms of structures of pins.
class HasPins a where
  type Source a
  -- | Generate a difference list of pins. First argument is phantom for Source
  -- non-injectivity.
  toPins   :: a -> Source a -> Unop [Pin]
  -- | Generate a source from a supply of pins
  fromPins :: a -> State [Pin] (Source a)

type HasPins2 a b = (HasPins a, HasPins b)

instance HasPins () where
  type Source () = ()
  toPins _ () = id
  fromPins _ = return ()
    
pop :: State [a] a
pop = do { (a:as) <- get ; put as ; return a }

instance HasPins Bool where
  type Source Bool = Pin
  toPins _ b = (b :)
  fromPins _ = pop

instance HasPins2 a b => HasPins (a :* b) where
  type Source (a :* b) = Source a :* Source b
  toPins ~(a,b) (sa,sb) = toPins b sb . toPins a sa
  -- fromPins = liftA2 (,) fromPins fromPins
  fromPins ~(a,b) = do sa <- fromPins a
                       sb <- fromPins b
                       return (sa,sb)


-- instance HasPins (a :+ b) where
--   type Source (a :+ b) = Source a :+ Source b   -- ???


{--------------------------------------------------------------------
    Circuit category
--------------------------------------------------------------------}

infixl 1 :>, :+>

-- | Internal representation for '(:>)'.
type a :+> b = Kleisli CircuitM (Source a) (Source b)

-- First shot at circuit category
newtype a :> b = C { unC :: a :+> b }

cirk :: (Source a -> CircuitM (Source b)) -> (a :> b)
cirk = C . Kleisli

-- instance Newtype (a :> b) (Source a -> CircuitM (Source b)) where
--   pack   = C
--   unpack = unC
-- 
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

-- instance CategoryCoproduct (:>) where
--   lft       = C lft
--   rht       = C rht
--   jam       = C jam
--   ldistribS = C ldistribS
--   rdistribS = C rdistribS
--   (+++)     = inC2 (+++)
--   (|||)     = inC2 (|||)

-- TODO: Reconsider this CategoryCoproduct instance, which relies on the dubious
-- 
--   type instance Source (a :+ b) = Source a :+ Source b.

-- class BoolCat (~>) where
--   notC :: Bool ~> Bool
--   andC, orC :: (Bool :* Bool) ~> Bool

-- -- | Instantiate a component, given its primitive, inputs, and number of outputs.
-- -- TODO: Rework this interface.
-- addComp :: Prim -> [Pin] -> Int -> CircuitM [Pin]
-- addComp = error "addComp: not implemented"

-- instance BoolCat (:>) where
--   notC = cirk $ \ i     -> do [o] <- addComp "not" [ i ] 1
--                               return o
--   andC = cirk $ \ (a,b) -> do [o] <- addComp "and" [a,b] 1
--                               return o
--   orC  = cirk $ \ (a,b) -> do [o] <- addComp "or"  [a,b] 1
--                               return o

-- TODO: Refactor

-- addComp' :: HasPins2 a => Prim -> (a :> b)
-- addComp' prim = 
--   cirk $ \ a -> 
--     do [o] <- pinsToSource <$> addComp prim (sourceToPins a) 
              
