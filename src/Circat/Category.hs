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


-- TODO: Reconsider naming scheme for classes. Maybe "ProductCat" -->
-- "CatProduct" or even "CategoryProduct". Compare with Ross's choices. On the
-- other hand, I like "ProductCat" and "ProductKon".

-- TODO: Consider "Kon" --> "Con". Or explain "Kon" as "constraint kind".


module Circat.Category
  ( module Control.Category
  , ProductCat(..), inLassocP, inRassocP
  , CoproductCat(..)
  , ConstCat(..), ConstUCat, UnitCat(..), lconst, rconst
  , ClosedCat(..)
  , Yes
  ) where

import Prelude hiding (id,(.),fst,snd,const,curry,uncurry)
import qualified Prelude as P

import Control.Category
import qualified Control.Arrow as A
import Control.Arrow (Kleisli(..),arr)
import Control.Monad (liftM,liftM2,join)
import GHC.Prim (Constraint)

import FunctorCombo.StrictMemo (HasTrie(..),(:->:))

import Circat.Misc ((:*),(:+),(<~),inNew,inNew2)

infixr 3 ***, &&&

-- | Hack to get around broken constraint defaults like () or ()~()
class Yes a
instance Yes a

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
  type ConstKon (~>) a = Yes a
  const :: ConstKon (~>) a => b -> (a ~> b)

instance ConstCat (->) where
  const = P.const

instance Monad m => ConstCat (Kleisli m) where
  type ConstKon (Kleisli m) a = Yes a  -- why necessary?
  const a = arr (const a)

-- | Category with unit injection. Minimal definition: 'lunit' or 'runit'.
class ProductCat (~>) => UnitCat (~>) where
  type UnitKon (~>) a :: Constraint
  type UnitKon (~>) a = Yes a
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

-- Based on Ed K's CCC from Control.Category.Cartesian.Closed in the categories package:

class ProductCat (~>) => ClosedCat (~>) where
  type ClosedKon (~>) k :: Constraint  -- ^ On the 'Exp' domain
  type ClosedKon (~>) k = Yes k
  type Exp (~>) :: * -> * -> *
  apply   :: (ClosedKon (~>) a, (+>)~Exp (~>)) => ((a +> b) :* a) ~> b
  curry   :: (ClosedKon (~>) b, (+>)~Exp (~>)) => ((a :* b) ~> c) -> a ~> (b +> c)
  uncurry :: (ClosedKon (~>) b, (+>)~Exp (~>)) => a ~> (b +> c) -> (a :* b) ~> c

instance ClosedCat (->) where
  type Exp (->) = (->)
  apply (f,a) = f a
  curry       = P.curry
  uncurry     = P.uncurry

-- For Kleisli, use tries. Might be too sweeping, in which case, comment out
-- this instance as a suggestion for specific monads or for newtype wrappers
-- around some Klieslis.

-- Klesli trie
newtype KTrie m a b = KTrie { unKTrie :: a :->: m b }

-- TODO: Would MemoTrie work as well?

mfun :: Monad m => m (p -> q) -> (p -> m q)
mfun u p = liftM ($ p) u

instance Monad m => ClosedCat (Kleisli m) where
  type ClosedKon (Kleisli m) k = HasTrie k
  type Exp (Kleisli m) = KTrie m
  apply = Kleisli (uncurry (untrie . unKTrie))
  curry = inNew $ \ f -> return . KTrie . trie . curry f
  uncurry = inNew $ \ h -> join . uncurry (mfun . liftM (untrie.unKTrie) . h)

{- Derivations:

apply :: ((a +> b) :* a) ~> b
      :: Kleisli m (KTrie m a b :* a) b
 
untrie :: (a :->: m b) -> a -> m b
untrie . unKTrie :: KTrie m a b -> a -> m b
uncurry (untrie . unKTrie) :: KTrie m a b :* a -> m b
Kleisli (uncurry (untrie . unKTrie)) :: Kleisli (KTrie m a b :* a) b

curry :: ((a :* b) ~> c) -> a ~> (b +> c)
      :: Kleisli m (a :* b) c -> Kleisli m a (KTrie m b c)
 
Kleisli f :: Kleisli m (a :* b) c
f :: a :* b -> m c
curry f :: a -> b -> m c
trie . curry f :: a -> b :->: m c
KTrie . trie . curry f :: a -> KTrie m b c
return . KTrie . trie . curry f :: a -> m (KTrie m b c)
Kleisli (return . KTrie . trie . curry f) :: Kleisli m a (KTrie m b c)


uncurry :: a ~> (b +> c) -> ((a :* b) ~> c)
        :: Kleisli m a (KTrie m b c) -> Kleisli m (a :* b) c
 
Kleisli h :: Kleisli m a (KTrie m b c)
h :: a -> m (KTrie m b c)
liftM unKTrie . h :: a -> m (b :->: m c)
liftM (untrie.unKTrie) . h :: a -> m (b -> m c)
mfun . liftM (untrie.unKTrie) . h :: a -> b -> m (m c)
uncurry (mfun . liftM (untrie.unKTrie) . h) :: a :* b -> m (m c)
join . uncurry (mfun . liftM (untrie.unKTrie) . h) :: a :* b -> m c
Kleisli (join . uncurry (mfun . liftM (untrie.unKTrie) . h)) :: Kleisli m (a :* b) c

-}
