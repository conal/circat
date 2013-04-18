{-# LANGUAGE TypeOperators, TypeFamilies, TupleSections, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Category
-- Copyright   :  (c) 2013 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Categories with product and co-product
----------------------------------------------------------------------

module Circat.Category
  ( module Control.Category
  , ProductCat(..), inLassocP, inRassocP
  , CoproductCat(..)
  , ConstCat(..), ConstUCat, UnitCat(..), lconst, rconst
  , FState(..)
  ) where

import Prelude hiding (id,(.),fst,snd,const)
import qualified Prelude as P

import Control.Category
import qualified Control.Arrow as A
import Control.Arrow (Kleisli(..),arr)
import Control.Monad (liftM2)
import GHC.Prim (Constraint)

import Control.Newtype

import Circat.Misc ((:*),(:+),(<~),inNew2)

infixr 3 ***, &&&

-- | Category with product. Minimal definition: 'fst', 'snd', and either (a)
-- '(&&&)' or (b) both '(***)' and 'dup'. TODO: Generalize '(:*)' to an
-- associated type. Keep the types fairly pretty.
class Category (~>) => ProductCat (~>) where
  fst     :: (a :* b) ~> a
  snd     :: (a :* b) ~> b
  dup     :: a ~> (a :* a)
  dup     =  id &&& id
  swapP   :: (a :* b) ~> (b :* a)
  swapP   =  snd &&& fst
  (***)   :: (a ~> c) -> (b ~> d) -> ((a :* b) ~> (c :* d))
  f *** g =  f . fst &&& g . snd
  (&&&)   :: (a ~> c) -> (a ~> d) -> (a ~> (c :* d))
  f &&& g =  (f *** g) . dup
  first   :: (a ~> a') -> ((a :* b) ~> (a' :* b))
  first   =  (*** id)
  second  :: (b ~> b') -> ((a :* b) ~> (a :* b'))
  second  =  (id ***)
  lassocP :: (a :* (b :* c)) ~> ((a :* b) :* c)
  lassocP =  second fst &&& (snd . snd)
  rassocP :: ((a :* b) :* c) ~> (a :* (b :* c))
  rassocP =  (fst . fst) &&& first  snd

--   ldistribP :: (a, u :* v) ~> ((a,u) :* (a,v))
--   ldistribP =  transPair . first  dup -- second fst &&& second snd
--   rdistribP :: (u :* v, b) ~> ((u,b) :* (v,b))
--   rdistribP =  transPair . second dup -- first  fst &&& first  snd

inRassocP :: ProductCat (~>) =>
             ((a :* (b :* c)) ~> (a' :* (b' :* c')))
          -> (((a :* b) :* c) ~> ((a' :* b') :* c'))
inRassocP = lassocP <~ rassocP

inLassocP :: ProductCat (~>) =>
             (((a :* b) :* c) ~> ((a' :* b') :* c'))
          -> ((a :* (b :* c)) ~> (a' :* (b' :* c')))
inLassocP = rassocP <~ lassocP

infixr 2 +++, |||

-- | Category with co-product. Minimal definition: 'lft', 'rht', and either
-- (a) '(|||)', (b) both '(+++)' and 'jam', or (c) both '(|||)' and '(+++)'.
-- TODO: Generalize '(:+)' to an associated type. Keep the types fairly pretty.
class Category (~>) => CoproductCat (~>) where
  lft       :: a ~> (a :+ b)
  rht       :: b ~> (a :+ b)
  jam       :: (a :+ a) ~> a                  -- dual to dup. standard name?
  jam       =  id ||| id
  (+++)     :: (a ~> c) -> (b ~> d) -> ((a :+ b) ~> (c :+ d))
  f +++ g   =  lft . f ||| rht . g
  (|||)     :: (a ~> c) -> (b ~> c) -> ((a :+ b) ~>  c)
  f ||| g   =  jam . (f +++ g)
  left      :: (a ~> a') -> ((a :+ b) ~> (a' :+ b ))
  left      =  (+++ id)
  right     :: (b ~> b') -> ((a :+ b) ~> (a  :+ b'))
  right     =  (id +++)
  ldistribS :: (a, u :+ v) ~> ((a,u) :+ (a,v))
  rdistribS :: (u :+ v, b) ~> ((u,b) :+ (v,b))
  swapS     :: (a :+ b) ~> (b :+ a)
  swapS     =  rht ||| lft
  lassocS   :: (a :+ (b :+ c)) ~> ((a :+ b) :+ c)
  rassocS   :: ((a :+ b) :+ c) ~> (a :+ (b :+ c))
  lassocS   =  lft.lft ||| (lft.rht ||| rht)
  rassocS   =  (lft ||| rht.lft) ||| rht.rht

  -- rdistribS = (swapP +++ swapP) . ldistribS . swapP -- Needs ProductCat (~>)

instance ProductCat (->) where
  fst   = P.fst
  snd   = P.snd
  (***) = (A.***)
  (&&&) = (A.&&&)

instance CoproductCat (->) where
  lft              = Left
  rht              = Right
  (+++)            = (A.+++)
  (|||)            = (A.|||)
  ldistribS (a,uv) = ((a,) +++ (a,)) uv
  rdistribS (uv,b) = ((,b) +++ (,b)) uv

instance Monad m => ProductCat (Kleisli m) where
  fst   = arr  fst
  snd   = arr  snd
  dup   = arr  dup
  (***) = inNew2 crossM

crossM :: Monad m => (a -> m c) -> (b -> m d) -> (a :* b -> m (c :* d))
(f `crossM` g) (a,b) = liftM2 (,) (f a) (g b)

instance Monad m => CoproductCat (Kleisli m) where
  lft       = arr  lft
  rht       = arr  rht
  jam       = arr  jam
  ldistribS = arr  ldistribS
  rdistribS = arr  rdistribS
  (|||)     = inNew2 (|||)


-- | Category with constant morphisms
class Category (~>) => ConstCat (~>) where
  type ConstKon (~>) a :: Constraint
  type ConstKon (~>) a = () ~ () -- or just (), if it works
  const :: ConstKon (~>) a => b -> (a ~> b)

instance ConstCat (->) where
  type ConstKon (->) a = ()  -- why necessary?
  const = P.const

instance Monad m => ConstCat (Kleisli m) where
  type ConstKon (Kleisli m) a = ()  -- why necessary?
  const a = arr (const a)

-- | Category with unit injection. Minimal definition: 'lunit' or 'runit'.
class ProductCat (~>) => UnitCat (~>) where
  type UnitKon (~>) a :: Constraint
  type UnitKon (~>) a = () ~ () -- or just (), if it works
  lunit :: a ~> (() :* a)
  lunit = swapP . runit
  runit :: a ~> (a :* ())
  runit = swapP . lunit

type ConstUCat (~>) = (ConstCat (~>), ConstKon (~>) ())

-- | Inject a constant on the left
lconst :: (UnitCat (~>), ConstUCat (~>)) => a -> (b ~> (a :* b))
lconst a = first  (const a) . lunit

-- | Inject a constant on the right
rconst :: (UnitCat (~>), ConstUCat (~>)) => b -> (a ~> (a :* b))
rconst b = second (const b) . runit

instance UnitCat (->) where
  lunit = ((),)
  runit = (,())

instance Monad m => UnitCat (Kleisli m) where
  lunit = arr lunit
  runit = arr runit

{--------------------------------------------------------------------
    State
--------------------------------------------------------------------}

-- | State interface.
class StateCat st where
  type StateKon st :: Constraint
  type StateKon st = () ~ () -- or just (), if it works
  get :: StateKon st => st s a s   -- ^ Get state
  put :: StateKon st => st s s ()  -- ^ Set state

instance StateCat (FState ar) where
  type StateKon (FState ar) = UnitCat ar
  get = FState (dup   . fst)
  put = FState (lunit . snd)

-- | Simple stateful category
newtype FState (~>) s a b = FState { runFState :: (s :* a) ~> (b :* s) }

instance Newtype (FState (~>) s a b) ((s :* a) ~> (b :* s)) where
  pack f = FState f
  unpack (FState f) = f

instance ProductCat (~>) => Category (FState (~>) s) where
  id  = pack swapP
  (.) = inNew2 $ \ g f -> g . swapP . f

pureS :: ProductCat (~>) => (a ~> b) -> FState (~>) s a b
pureS f = pack (swapP . second f)

instance ProductCat (~>) => ProductCat (FState (~>) s) where
  fst   = pureS fst
  snd   = pureS snd
  dup   = pureS dup
  (***) = inNew2 $ \ f g -> lassocP . second g . inLassocP (first f)

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
