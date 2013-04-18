{-# LANGUAGE TypeOperators, TypeFamilies, TupleSections, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.State
-- Copyright   :  (c) 2013 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- State abstractions
----------------------------------------------------------------------

module Circat.State
  ( StateCat(..), pureState, FState(..)
  ) where

import Prelude hiding (id,(.),fst,snd,const)
import qualified Prelude as P

import Control.Category

import Control.Newtype

import FunctorCombo.StrictMemo (HasTrie(..),(:->:))

import Circat.Misc ((:*),(<~))
import Circat.Category

{--------------------------------------------------------------------
    State
--------------------------------------------------------------------}

-- TODO: Move to another module

-- | State interface. Minimal definition: 'state' and 'runState'
class UnitCat (~>) => StateCat st (~>) where
  state    :: (s :* a) ~> (b :* s) -> st (~>) s a b  -- ^ Make a stateful computation
  runState :: st (~>) s a b -> (s :* a) ~> (b :* s)  -- ^ Run a stateful computation
  get      :: st (~>) s a s                          -- ^ Get state
  get      = state (dup   . fst)
  put      :: st (~>) s s ()                         -- ^ Set state
  put      = state (lunit . snd)

pureState :: StateCat st (~>) => (a ~> b) -> st (~>) s a b
pureState f = state (swapP . second f)

inState :: (StateCat p (~>), StateCat q (+>)) =>
           (((s :* a) ~> (b :* s)) -> ((t :* c) +> (d :* t)))
        -> (p (~>) s a b           -> q (+>) t c d)
inState = state <~ runState

inState2 :: (StateCat p (~>), StateCat q (+>), StateCat r (#>)) =>
            (((s :* a) ~> (b :* s)) -> ((t :* c) +> (d :* t)) -> ((u :* e) #> (f :* u)))
         -> (p (~>) s a b           -> q (+>) t c d           -> r (#>) u e f)
inState2 = inState <~ runState

-- | Change state categories
restate :: (StateCat st (~>), StateCat st' (~>)) =>
           st (~>) s a b -> st' (~>) s a b
restate = inState id

-- restate = state . runState

-- | Simple stateful category
newtype FState (~>) s a b = FState { runFState :: (s :* a) ~> (b :* s) }

-- We can operate on any StateCat as if it were FState, leading to a simple
-- implementation of all classes for which FState is an instance.

asFState :: (StateCat p (~>), StateCat q (+>)) =>
            (FState (~>) s a b -> FState (+>) t c d)
         -> (p (~>) s a b -> q (+>) t c d)
asFState = restate <~ restate

asFState2  :: (StateCat p (~>), StateCat q (+>), StateCat r (#>)) =>
              (FState (~>) s a b -> FState (+>) t c d -> FState (#>) u e f)
           -> (p (~>) s a b -> q (+>) t c d -> r (#>) u e f)
asFState2 = asFState <~ restate

-- Generic definition

instance UnitCat (~>) => StateCat FState (~>) where
  state    = state
  runState = runFState

instance Newtype (FState (~>) s a b) ((s :* a) ~> (b :* s)) where
  pack f = FState f
  unpack (FState f) = f

-- Generic definitions for StateCat. 

instance UnitCat (~>) => Category (FState (~>) s) where
  id  = pack swapP
  (.) = inState2 $ \ g f -> g . swapP . f

instance UnitCat (~>) => ProductCat (FState (~>) s) where
  fst   = pureState fst
  snd   = pureState snd
  dup   = pureState dup
  (***) = inState2 $ \ f g -> lassocP . second g . inLassocP (first f)

-- f    :: s * a       ~> s * c
-- g    :: s * b       ~> s * d
-- want :: s * (a * b) ~> s * (c * d)

{- Derivation:
                 
lassocP  :: s * (a * b) ~> (s * a) * b
first f  ::             ~> (c * s) * b
rassocP  ::             ~> c * (s * b)
second g ::             ~> c * (d * s)
lassocP  ::             ~> (c * d) * s

-}

instance UnitCat (~>) => UnitCat (FState (~>) s) where
  lunit = pureState lunit
  runit = pureState runit


{--------------------------------------------------------------------
    Memoization
--------------------------------------------------------------------}

-- | 'StateTrie' inner representation
type StateTrieX (~>) s a b = a ~> (s :->: (b :* s))

-- | Memoizing state category
newtype StateTrie (~>) s a b =
  StateTrie { unStateTrie :: StateTrieX (~>) s a b }

-- instance StateCat StateTrie (~>) where
--   state = ... working here ...



-- class UnitCat (~>) => StateCat st (~>) where
--   state    :: (s :* a) ~> (b :* s) -> st (~>) s a b  -- ^ Make a stateful computation
--   runState :: st (~>) s a b -> (s :* a) ~> (b :* s)  -- ^ Run a stateful computation

-- instance UnitCat (~>) => StateCat FState (~>) where
--   state    = state
--   runState = runFState

-- TODO: Reconsider my unconventional choice of argument/result order in
-- 'FState'. Now that I have the 'StateCat' interface and the traverse
-- formulation of addition, does the 'FState' representation have much impact?
-- Would I want to keep the unconventional order in the 'state' method?
