{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE TupleSections, ScopedTypeVariables, ExistentialQuantification #-}
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

-- mtl
import Control.Monad.State (MonadState(..),State,runState)
import Control.Monad.Writer (MonadWriter(..),WriterT)

import Circat.Misc ((:*),(:+),(<~),Unop)
import Circat.Category
import Circat.Classes

{--------------------------------------------------------------------
    The circuit monad
--------------------------------------------------------------------}

-- Primitive (stub)
newtype Prim a b = Prim String deriving Show

-- Component: primitive instance with inputs & outputs
data Comp = forall a b. IsSource2 a b => Comp (Prim a b) a b

deriving instance Show Comp

-- The circuit monad:
type CircuitM = WriterT [Comp] (State PinSupply)

-- TODO: Is WriterT [a] efficient, or do we get frequent (++)? I could use a
-- difference list instead, i.e., Unop [Comp] instead of [Comp].

newtype Pin = Pin Int deriving (Eq,Show,Enum)
type PinSupply = Pin  -- Next free pin

newPin :: CircuitM Pin
newPin = do { p <- get ; put (succ p) ; return p }

{--------------------------------------------------------------------
    Pins
--------------------------------------------------------------------}

sourcePins :: forall a. IsSource a => a -> [Pin]
sourcePins s = toPins s []

-- The Source type family gives a representation for a type in terms of
-- structures of pins. Maybe drop the Show constraint later (after testing).
class Show a => IsSource a where
  toPins    :: a -> Unop [Pin]  -- difference list
  genSource :: CircuitM a

genComp :: forall a b. IsSource2 a b =>
           Prim a b -> a -> CircuitM b
genComp prim a = do b <- genSource
                    tell [Comp prim a b]
                    return b

type IsSource2 a b = (IsSource a, IsSource b)

instance IsSource () where
  toPins () = id
  genSource = pure ()

instance IsSource Pin where
  toPins p  = (p :)
  genSource = newPin

instance IsSource2 a b => IsSource (a :* b) where
  toPins (sa,sb) = toPins sb . toPins sa
  genSource      = liftA2 (,) genSource genSource

-- instance IsSource (a :+ b) where ... ???

{--------------------------------------------------------------------
    Circuit category
--------------------------------------------------------------------}

infixl 1 :>

-- | Circuit category
type (:>) = Kleisli CircuitM

-- TODO: Will the product & coproduct instances really work here, or do I need a
-- wrapper around Kleisli? Maybe they just work. Hm. If so, what benefit accrues
-- from using the categorical instead of monadic form?

newComp :: IsSource2 a b => Prim a b -> a :> b
newComp prim = Kleisli (genComp prim)

pcomp :: IsSource2 a b => String -> a :> b
pcomp = newComp . Prim

instance BoolCat (:>) where
  type Bit (:>) = Pin
  notC = pcomp "not"
  orC  = pcomp "or"
  andC = pcomp "and"

instance EqCat (:>) where
  type EqConstraint (:>) a = IsSource a
  eq  = pcomp "eq"
  neq = pcomp "neq"
