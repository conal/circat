{-# LANGUAGE TypeOperators, TupleSections #-}
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
  , CategoryProduct(..), CategoryCoproduct(..)
  ) where

import Prelude hiding (id,(.),fst,snd)
import qualified Prelude as P

import Control.Category
import qualified Control.Arrow as A
import Control.Arrow (Kleisli(..))
import Control.Monad (liftM2)

import Circat.Misc ((:*),(:+),inNew2)


infixr 3 ***, &&&

-- | Category with product. Minimal definition: 'fst', 'snd', and either
-- (a) '(&&&)', (b) both '(***)' and 'dup', or (c) both '(&&&)' and '(***)'.
-- TODO: Generalize '(:*)' to an associated type. Keep the types fairly pretty.
class Category (~>) => CategoryProduct (~>) where
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

infixr 2 +++, |||

-- | Category with co-product. Minimal definition: 'lft', 'rht', and either
-- (a) '(|||)', (b) both '(+++)' and 'jam', or (c) both '(|||)' and '(+++)'.
-- TODO: Generalize '(:+)' to an associated type. Keep the types fairly pretty.
class Category (~>) => CategoryCoproduct (~>) where
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

  -- rdistribS = (swapP +++ swapP) . ldistribS . swapP -- Needs CategoryProduct (~>)

instance CategoryProduct (->) where
  fst   = P.fst
  snd   = P.snd
  (***) = (A.***)
  (&&&) = (A.&&&)

instance CategoryCoproduct (->) where
  lft              = Left
  rht              = Right
  (+++)            = (A.+++)
  (|||)            = (A.|||)
  ldistribS (a,uv) = ((a,) +++ (a,)) uv
  rdistribS (uv,b) = ((,b) +++ (,b)) uv

instance Monad m => CategoryProduct (Kleisli m) where
  fst   = A.arr  fst
  snd   = A.arr  snd
  dup   = A.arr  dup
  (***) = inNew2 crossM

crossM :: Monad m => (a -> m c) -> (b -> m d) -> (a :* b -> m (c :* d))
(f `crossM` g) (a,b) = liftM2 (,) (f a) (g b)

instance Monad m => CategoryCoproduct (Kleisli m) where
  lft       = A.arr  lft
  rht       = A.arr  rht
  jam       = A.arr  jam
  ldistribS = A.arr  ldistribS
  rdistribS = A.arr  rdistribS
  (|||)     = inNew2 (|||)
