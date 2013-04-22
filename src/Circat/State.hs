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
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- State abstractions
----------------------------------------------------------------------

module Circat.State
  ( StateCat(..), StateCatWith, pureState, StateFun(..), StateExp(..)
  ) where

import Prelude hiding (id,(.),fst,snd,const,curry,uncurry)
import qualified Prelude as P

import Control.Category
import GHC.Prim (Constraint)

import Control.Newtype

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
newtype StateFun (~>) s a b = StateFun { runStateFun :: (s :* a) ~> (b :* s) }

instance Newtype (StateFun (~>) s a b) ((s :* a) ~> (b :* s)) where
  pack f = StateFun f
  unpack (StateFun f) = f

instance UnitCat (~>) => Category (StateFun (~>) s) where
  id  = pack swapP
  (.) = inState2 $ \ g f -> g . swapP . f

instance UnitCat (~>) => ProductCat (StateFun (~>) s) where
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

instance UnitCat (~>) => UnitCat (StateFun (~>) s) where
  lunit = pureState lunit
  runit = pureState runit

instance UnitCat (~>) => StateCat (StateFun (~>) s) where
  type StateKon  (StateFun (~>) s) = ()
  type StateBase (StateFun (~>) s) = (~>)
  type StateT    (StateFun (~>) s) = s
  state    = StateFun
  runState = runStateFun

-- We can operate on any StateCat as if it were StateFun, leading to a simple
-- implementation of all classes for which StateFun is an instance.

asStateFun  :: (StateCatWith (~~>) (~>) s, StateCatWith (++>) (+>) t) =>
             (StateFun (~>) s a b -> StateFun (+>) t c d)
          -> (a ~~> b           -> c ++> d)
asStateFun  = restate <~ restate

asStateFun2 :: (StateCatWith (~~>) (~>) s, StateCatWith (++>) (+>) t
             ,StateCatWith (##>) (#>) u) =>
             (StateFun (~>) s a b -> StateFun (+>) t c d -> StateFun (#>) u e f)
          -> (a ~~> b           -> c ++> d           -> e ##> f)
asStateFun2 = asStateFun <~ restate


-- | Specialize 'restate' to convert from StateFun
restateF :: (StateCatWith (~~>) (~>) s) =>
            StateFun (~>) s a b -> a ~~> b
restateF = inState id


{--------------------------------------------------------------------
    Memoization
--------------------------------------------------------------------}

-- | State via exponentials. For (->), isomorphic to 'StateFun'. Can lead to
-- memoization for other categories.
newtype StateExp (~>) s a b =
  StateExp { unStateExp :: a ~> Exp (~>) s (b :* s) }

type ClosedCatU (~>) s = (ClosedCatWith (~>) s, UnitCat (~>))

instance ClosedCatU (~>) s => StateCat (StateExp (~>) s) where
  type StateKon  (StateExp (~>) s) = ClosedKon (~>) s
  type StateBase (StateExp (~>) s) = (~>)
  type StateT    (StateExp (~>) s) = s
  state    f  = StateExp (curry (f . swapP))
  runState st = uncurry (unStateExp st) . swapP

-- TODO: Do I want to use RepT for StateT? I guess I could define a dummy State
-- type to represent the intention, and then define StateT (~>) = RepT (~>)
-- State. Unclear, so postpone change.

{- Derivations

f                            :: (s :* a) ~> (b :* s)
f . swapP                    :: (a :* s) ~> (b :* s)
curry (f . swapP)            :: a ~> (ExpT (~>) s (b :* s))
StateExp (curry (f . swapP)) :: StateExp (~>) s a b

Then invert for runState.

-}

-- For the other class instances, use pureState and defer to StateFun:

instance ClosedCatU (~>) s => Category (StateExp (~>) s) where
  id  = restateF id
  (.) = asStateFun2 (.)

--     Illegal irreducible constraint ClosedKon (~>) s in superclass/instance
--     head context (Use -XUndecidableInstances to permit this)

instance ClosedCatU (~>) s => ProductCat (StateExp (~>) s) where
  fst   = pureState fst  -- or restateF fst
  snd   = pureState snd
  dup   = pureState dup
  (***) = asStateFun2 (***)

instance ClosedCatU (~>) s => UnitCat (StateExp (~>) s) where
  lunit = pureState lunit
  runit = pureState runit
