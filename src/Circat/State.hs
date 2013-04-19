{-# LANGUAGE TypeOperators, TypeFamilies, TupleSections, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-} -- see below

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
  {- ( StateCat(..), pureState, FState(..)
  ) -} where

import Prelude hiding (id,(.),fst,snd,const,curry,uncurry)
import qualified Prelude as P

import Control.Category
import GHC.Prim (Constraint)

import Control.Newtype

import FunctorCombo.StrictMemo (HasTrie(..),(:->:))

import Circat.Misc ((:*),(<~))
import Circat.Category

{--------------------------------------------------------------------
    State
--------------------------------------------------------------------}

-- | State interface. Minimal definition: 'state' and 'runState'
class UnitCat (StateBase (~~>)) => StateCat (~~>) where
  type StateKon (~~>) :: Constraint
  type StateKon (~~>) = ()
  type StateBase (~~>) :: * -> * -> *
  type StateT    (~~>) :: *
  state    :: StateParts (~~>) (~>) s =>      -- ^ Make a stateful computation
              (s :* a) ~> (b :* s) -> a ~~> b
  runState :: StateParts (~~>) (~>) s =>      -- ^ Run a stateful computation
              a ~~> b -> (s :* a) ~> (b :* s)
  get :: StateParts (~~>) (~>) s => a ~~> s          -- ^ Get state
  get = state (dup   . fst)
  put :: StateParts (~~>) (~>) s => s ~~> ()         -- ^ Set state
  put = state (lunit . snd)

type StateParts (~~>) (~>) s =
  ((~>) ~ StateBase (~~>), s ~ StateT (~~>), StateKon (~~>))

type StateCatWith (~~>) (~>) s = (StateCat (~~>), StateParts (~~>) (~>) s)


-- Alternative naming style:

-- class UnitCat (StateBase (~>)) => StateCat (~>) where
--   type StateT (~>) :: *
--   type StateBase (~>) :: * -> * -> *
--   state    :: StateParts (~>) (.~>) s =>  -- ^ Make a stateful computation
--               (s :* a) .~> (b :* s) -> a ~> b
--   runState :: StateParts (~>) (.~>) s =>  -- ^ Run a stateful computation
--               a ~> b -> (s :* a) .~> (b :* s)
--   get :: s ~ StateT (~>) => a ~> s     -- ^ Get state
--   get = state (dup   . fst)
--   put :: s ~ StateT (~>) => s ~> ()    -- ^ Set state
--   put = state (lunit . snd)

pureState :: StateCatWith (~~>) (~>) s => (a ~> b) -> a ~~> b
pureState f = state (swapP . second f)

inState :: (StateCatWith (~~>) (~>) s, StateCatWith (++>) (+>) t) =>
           (((s :* a) ~> (b :* s)) -> ((t :* c) +> (d :* t)))
        -> (a ~~> b                -> c ++> d)
inState = state <~ runState

inState2 :: (StateCatWith (~~>) (~>) s, StateCatWith (++>) (+>) t
            ,StateCatWith (##>) (#>) u) =>
            (((s :* a) ~> (b :* s)) -> ((t :* c) +> (d :* t)) -> ((u :* e) #> (f :* u)))
         -> (a ~~> b                -> c ++> d                -> e ##> f)
inState2 = inState <~ runState

-- | Change state categories. Must share common base category and state type
restate :: (StateCatWith (~~>) (~>) s, StateCatWith (++>) (~>) s) =>
           a ~~> b -> a ++> b
restate = inState id

-- restate = state . runState

-- | Simple stateful category
newtype FState (~>) s a b = FState { runFState :: (s :* a) ~> (b :* s) }

instance Newtype (FState (~>) s a b) ((s :* a) ~> (b :* s)) where
  pack f = FState f
  unpack (FState f) = f

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

instance UnitCat (~>) => StateCat (FState (~>) s) where
  type StateKon  (FState (~>) s) = ()
  type StateBase (FState (~>) s) = (~>)
  type StateT    (FState (~>) s) = s
  state    = FState
  runState = runFState

-- We can operate on any StateCat as if it were FState, leading to a simple
-- implementation of all classes for which FState is an instance.

asFState  :: (StateCatWith (~~>) (~>) s, StateCatWith (++>) (+>) t) =>
             (FState (~>) s a b -> FState (+>) t c d)
          -> (a ~~> b           -> c ++> d)
asFState  = restate <~ restate

asFState2 :: (StateCatWith (~~>) (~>) s, StateCatWith (++>) (+>) t
             ,StateCatWith (##>) (#>) u) =>
             (FState (~>) s a b -> FState (+>) t c d -> FState (#>) u e f)
          -> (a ~~> b           -> c ++> d           -> e ##> f)
asFState2 = asFState <~ restate


-- | Specialize 'restate' to convert from FState
restateF :: (StateCatWith (~~>) (~>) s) =>
            FState (~>) s a b -> a ~~> b
restateF = inState id


{--------------------------------------------------------------------
    Memoization
--------------------------------------------------------------------}

-- | State via exponentials. For (->), isomorphic to 'FState'. Can lead to
-- memoization for other categories.
newtype StateExp (~>) s a b =
  StateExp { unStateExp :: a ~> Exp (~>) s (b :* s) }

type ClosedCatU (~>) s = (ClosedCatWith (~>) s, UnitCat (~>))

instance ClosedCatU (~>) s => StateCat (StateExp (~>) s) where
  type StateKon (StateExp (~>) s) = ClosedKon (~>) s
  type StateBase (StateExp (~>) s) = (~>)
  type StateT    (StateExp (~>) s) = s
  state    f  = StateExp (curry (f . swapP))
  runState st = uncurry (unStateExp st) . swapP

{- Derivations

f                            :: (s :* a) ~> (b :* s)
f . swapP                    :: (a :* s) ~> (b :* s)
curry (f . swapP)            :: a ~> (Exp (~>) s (b :* s))
StateExp (curry (f . swapP)) :: StateExp (~>) s a b

Then invert for runState.

-}

-- For the other class instances, use pureState and defer to FState:

instance ClosedCatU (~>) s => Category (StateExp (~>) s) where
  id  = restateF id
  (.) = asFState2 (.)

--     Illegal irreducible constraint ClosedKon (~>) s in superclass/instance
--     head context (Use -XUndecidableInstances to permit this)

instance ClosedCatU (~>) s => ProductCat (StateExp (~>) s) where
  fst   = pureState fst  -- or restateF fst
  snd   = pureState snd
  dup   = pureState dup
  (***) = asFState2 (***)

instance ClosedCatU (~>) s => UnitCat (StateExp (~>) s) where
  lunit = pureState lunit
  runit = pureState runit
