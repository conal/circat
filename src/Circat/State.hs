{-# LANGUAGE TypeOperators, TypeFamilies, TupleSections, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

import Circat.Misc ((:*),(<~))
import Circat.Category

{--------------------------------------------------------------------
    State
--------------------------------------------------------------------}

-- TODO: Move to another module

-- | State interface.
class UnitCat (~>) => StateCat st (~>) where
  get      :: st (~>) s a s                          -- ^ Get state
  put      :: st (~>) s s ()                         -- ^ Set state
  state    :: (s :* a) ~> (b :* s) -> st (~>) s a b  -- ^ Make a stateful computation
  runState :: st (~>) s a b -> (s :* a) ~> (b :* s)  -- ^ Run a stateful computation

pureState :: StateCat st (~>) => (a ~> b) -> st (~>) s a b
pureState f = state (swapP . second f)

-- | Simple stateful category
newtype FState (~>) s a b = FState { runFState :: (s :* a) ~> (b :* s) }

instance UnitCat (~>) => StateCat FState (~>) where
  get      = FState (dup   . fst)
  put      = FState (lunit . snd)
  state    = FState
  runState = runFState

inState :: (StateCat p (~>), StateCat q (+>)) =>
           (((s :* a) ~> (b :* s)) -> ((t :* c) +> (d :* t)))
        -> (p (~>) s a b           -> q (+>) t c d)
inState = state <~ runState

inState2 :: (StateCat p (~>), StateCat q (+>), StateCat r (#>)) =>
            (((s :* a) ~> (b :* s)) -> ((t :* c) +> (d :* t)) -> ((u :* e) #> (f :* u)))
         -> (p (~>) s a b           -> q (+>) t c d           -> r (#>) u e f)
inState2 = inState <~ runState

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


-- -- | 'StateTrie' inner representation
-- type StateTrieX (~>) s a b = a ~> (s :->: (a,s))

-- -- | Memoizing state category
-- newtype StateTrie (~>) s a b = StateTrie { unStateTrie :: (s :* a) ~> (b :* s) }

