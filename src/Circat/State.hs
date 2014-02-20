{-# LANGUAGE TypeOperators, TypeFamilies, TupleSections, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-} -- see below

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.State
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- State abstractions
----------------------------------------------------------------------

module Circat.State
  ( StateCat(..), StateCatWith, pureState, StateFun(..), StateExp(..)
  ) where

import Prelude hiding (id,(.),const,curry,uncurry)
import qualified Prelude as P

import Control.Category

import Control.Newtype

import Circat.Misc ((:*),(:=>),(<~))
import Circat.Category

{--------------------------------------------------------------------
    State
--------------------------------------------------------------------}

-- | State interface. Minimal definition: 'state' and 'runState'
class TerminalCat (StateBase sk) => StateCat sk where
  type StateBase sk :: * -> * -> *
  type StateT    sk :: *
  -- | Make a stateful computation
  state    :: StateParts sk k s =>
              (s :* a) `k` (b :* s) -> a `sk` b
  -- | Run a stateful computation
  runState :: StateParts sk k s =>
              a `sk` b -> (s :* a) `k` (b :* s)
  -- | Get state
  get :: StateParts sk k s => a `sk` s
  get = state (dup   . exl)
  -- | Set state
  put :: StateParts sk k s => s `sk` ()
  put = state (lunit . exr)

type StateParts sk k s = (k ~ StateBase sk, s ~ StateT sk)

type StateCatWith sk k s = (StateCat sk, StateParts sk k s)


-- Alternative naming style:

-- class TerminalCat (StateBase k) => StateCat k where
--   type StateT k :: *
--   type StateBase k :: * -> * -> *
--   state    :: StateParts k (.`k`) s =>  -- ^ Make a stateful computation
--               (s :* a) .`k` (b :* s) -> a `k` b
--   runState :: StateParts k (.`k`) s =>  -- ^ Run a stateful computation
--               a `k` b -> (s :* a) .`k` (b :* s)
--   get :: s ~ StateT k => a `k` s     -- ^ Get state
--   get = state (dup   . exl)
--   put :: s ~ StateT k => s `k` ()    -- ^ Set state
--   put = state (lunit . exr)

pureState :: StateCatWith sk k s => (a `k` b) -> a `sk` b
pureState f = state (swapP . second f)

inState :: (StateCatWith sk k s, StateCatWith sk' k' t) =>
           (((s :* a) `k` (b :* s)) -> ((t :* c) `k'` (d :* t)))
        -> (a `sk` b                -> c `sk'` d)
inState = state <~ runState

inState2 :: (StateCatWith sk k s, StateCatWith sk' k' t
            ,StateCatWith sk'' k'' u) =>
            (((s :* a) `k` (b :* s)) -> ((t :* c) `k'` (d :* t)) -> ((u :* e) `k''` (f :* u)))
         -> (a `sk` b                -> c `sk'` d                -> e `sk''` f)
inState2 = inState <~ runState

-- | Change state categories. Must share common base category and state type
restate :: (StateCatWith sk k s, StateCatWith sk' k s) =>
           a `sk` b -> a `sk'` b
restate = inState id

-- restate = state . runState

-- | Simple stateful category
newtype StateFun k s a b = StateFun { runStateFun :: (s :* a) `k` (b :* s) }

instance Newtype (StateFun k s a b) ((s :* a) `k` (b :* s)) where
  pack f = StateFun f
  unpack (StateFun f) = f

instance TerminalCat k => Category (StateFun k s) where
  id  = pack swapP
  (.) = inState2 $ \ g f -> g . swapP . f

instance TerminalCat k => ProductCat (StateFun k s) where
  exl   = pureState exl
  exr   = pureState exr
  dup   = pureState dup
  (***) = inState2 $ \ f g -> lassocP . second g . inLassocP (first f)

-- f    :: s * a       `k` s * c
-- g    :: s * b       `k` s * d
-- want :: s * (a * b) `k` s * (c * d)

{- Derivation:
                 
lassocP  :: s * (a * b) `k` (s * a) * b
first f  ::             `k` (c * s) * b
rassocP  ::             `k` c * (s * b)
second g ::             `k` c * (d * s)
lassocP  ::             `k` (c * d) * s

-}

instance TerminalCat k => TerminalCat (StateFun k s) where
  it = pureState it

instance TerminalCat k => StateCat (StateFun k s) where
  type StateBase (StateFun k s) = k
  type StateT    (StateFun k s) = s
  state    = StateFun
  runState = runStateFun

-- We can operate on any StateCat as if it were StateFun, leading to a simple
-- implementation of all classes for which StateFun is an instance.

asStateFun  :: (StateCatWith sk k s, StateCatWith sk' k' t) =>
             (StateFun k s a b -> StateFun k' t c d)
          -> (a `sk` b           -> c `sk'` d)
asStateFun  = restate <~ restate

asStateFun2 :: (StateCatWith sk k s, StateCatWith sk' k' t
             ,StateCatWith sk'' k'' u) =>
             (StateFun k s a b -> StateFun k' t c d -> StateFun k'' u e f)
          -> (a `sk` b           -> c `sk'` d           -> e `sk''` f)
asStateFun2 = asStateFun <~ restate


-- | Specialize 'restate' to convert from StateFun
restateF :: (StateCatWith sk k s) =>
            StateFun k s a b -> a `sk` b
restateF = inState id


{--------------------------------------------------------------------
    Memoization
--------------------------------------------------------------------}

-- | State via exponentials. For (->), isomorphic to 'StateFun'. Can lead to
-- memoization for other categories.
newtype StateExp k s a b = StateExp { unStateExp :: a `k` (s :=> b :* s) }

-- TODO: Move s out of StateExp

type ClosedCatU k = (ClosedCat k, TerminalCat k)

instance ClosedCatU k => StateCat (StateExp k s) where
  type StateBase (StateExp k s) = k
  type StateT    (StateExp k s) = s
  state    f  = StateExp (curry (f . swapP))
  runState st = uncurry (unStateExp st) . swapP

-- TODO: Do I want to use RepT for StateT? I guess I could define a dummy State
-- type to represent the intention, and then define StateT k = RepT k
-- State. Unclear, so postpone change.

{- Derivations

f                            :: (s :* a) `k` (b :* s)
f . swapP                    :: (a :* s) `k` (b :* s)
curry (f . swapP)            :: a `k` (ExpT k s (b :* s))
StateExp (curry (f . swapP)) :: StateExp k s a b

Then invert for runState.

-}

-- For the other class instances, use pureState and defer to StateFun:

instance ClosedCatU k => Category (StateExp k s) where
  id  = restateF id
  (.) = asStateFun2 (.)

--     Illegal irreducible constraint ClosedKon k s in superclass/instance
--     head context (Use -XUndecidableInstances to permit this)

instance ClosedCatU k => ProductCat (StateExp k s) where
  exl   = pureState exl  -- or restateF exl
  exr   = pureState exr
  dup   = pureState dup
  (***) = asStateFun2 (***)

instance ClosedCatU k => TerminalCat (StateExp k s) where
  it = pureState it
