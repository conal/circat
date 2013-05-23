{-# LANGUAGE TypeOperators, TypeFamilies, TupleSections, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Category
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
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
  , ProductCat(..), inLassocP, inRassocP, inLassocPF, inRassocPS
  , CoproductCat(..)
  , ConstCat(..), ConstCatWith, ConstUCat, UnitCat(..), lconst, rconst
  , StrongCat(..), ClosedCat(..), ClosedCatWith
  , Yes
  ) where

import Prelude hiding (id,(.),fst,snd,const,curry,uncurry,sequence)
import qualified Prelude as P

import Control.Category
import qualified Control.Arrow as A
import Control.Arrow (Kleisli(..),arr)
import Control.Monad (liftM2) -- liftM,
-- import Data.Traversable (Traversable,sequence)
import GHC.Prim (Constraint)

-- import FunctorCombo.StrictMemo (HasTrie(..),(:->:))

import Circat.Misc ((:*),(:+),(<~),inNew2) -- ,inNew

infixr 3 ***, &&&

-- | Hack to get around broken constraint defaults like () or ()~().
-- Doesn't seem to do the trick.
class Yes a
instance Yes a

class Yes2 a b
instance Yes2 a b

-- | Category with product. Minimal definition: 'fst', 'snd', and either (a)
-- '(&&&)' or (b) both '(***)' and 'dup'. TODO: Generalize '(:*)' to an
-- associated type. Keep the types fairly pretty.
class Category k => ProductCat k where
  fst     :: (a :* b) `k` a
  snd     :: (a :* b) `k` b
  dup     :: a `k` (a :* a)
  dup     =  id &&& id
  swapP   :: (a :* b) `k` (b :* a)
  swapP   =  snd &&& fst
  (***)   :: (a `k` c) -> (b `k` d) -> ((a :* b) `k` (c :* d))
  f *** g =  f . fst &&& g . snd
  (&&&)   :: (a `k` c) -> (a `k` d) -> (a `k` (c :* d))
  f &&& g =  (f *** g) . dup
  first   :: (a `k` a') -> ((a :* b) `k` (a' :* b))
  first   =  (*** id)
  second  :: (b `k` b') -> ((a :* b) `k` (a :* b'))
  second  =  (id ***)
  lassocP :: (a :* (b :* c)) `k` ((a :* b) :* c)
  lassocP =  second fst &&& (snd . snd)
  rassocP :: ((a :* b) :* c) `k` (a :* (b :* c))
  rassocP =  (fst . fst) &&& first  snd

--   ldistribP :: (a, u :* v) `k` ((a,u) :* (a,v))
--   ldistribP =  transPair . first  dup -- second fst &&& second snd
--   rdistribP :: (u :* v, b) `k` ((u,b) :* (v,b))
--   rdistribP =  transPair . second dup -- first  fst &&& first  snd

-- | Operate on left-associated form
inLassocP :: ProductCat k =>
             (((a :* b) :* c) `k` ((a' :* b') :* c'))
          -> ((a :* (b :* c)) `k` (a' :* (b' :* c')))
inLassocP = rassocP <~ lassocP

-- | Operate on right-associated form
inRassocP :: ProductCat k =>
             ((a :* (b :* c)) `k` (a' :* (b' :* c')))
          -> (((a :* b) :* c) `k` ((a' :* b') :* c'))
inRassocP = lassocP <~ rassocP

-- | Left-associate and operate on left
inLassocPF :: ProductCat k =>
              ((a :* b) `k` (a' :* b'))
           -> ((a :* (b :* c)) `k` (a' :* (b' :* c)))
inLassocPF = inLassocP . first

-- | Right-associate and operate on right
inRassocPS :: ProductCat k =>
              ((b :* c) `k` (b' :* c'))
           -> (((a :* b) :* c) `k` ((a :* b') :* c'))
inRassocPS = inRassocP . second


infixr 2 +++, |||

-- | Category with co-product. Minimal definition: 'lft', 'rht', and either
-- (a) '(|||)', (b) both '(+++)' and 'jam', or (c) both '(|||)' and '(+++)'.
-- TODO: Generalize '(:+)' to an associated type. Keep the types fairly pretty.
class Category k => CoproductCat k where
  lft       :: a `k` (a :+ b)
  rht       :: b `k` (a :+ b)
  jam       :: (a :+ a) `k` a                  -- dual to dup. standard name?
  jam       =  id ||| id
  (+++)     :: (a `k` c) -> (b `k` d) -> ((a :+ b) `k` (c :+ d))
  f +++ g   =  lft . f ||| rht . g
  (|||)     :: (a `k` c) -> (b `k` c) -> ((a :+ b) `k`  c)
  f ||| g   =  jam . (f +++ g)
  left      :: (a `k` a') -> ((a :+ b) `k` (a' :+ b ))
  left      =  (+++ id)
  right     :: (b `k` b') -> ((a :+ b) `k` (a  :+ b'))
  right     =  (id +++)
  ldistribS :: (a, u :+ v) `k` ((a,u) :+ (a,v))
  rdistribS :: (u :+ v, b) `k` ((u,b) :+ (v,b))
  swapS     :: (a :+ b) `k` (b :+ a)
  swapS     =  rht ||| lft
  lassocS   :: (a :+ (b :+ c)) `k` ((a :+ b) :+ c)
  rassocS   :: ((a :+ b) :+ c) `k` (a :+ (b :+ c))
  lassocS   =  lft.lft ||| (lft.rht ||| rht)
  rassocS   =  (lft ||| rht.lft) ||| rht.rht

  -- rdistribS = (swapP +++ swapP) . ldistribS . swapP -- Needs ProductCat k

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
class Category k => ConstCat k where
  type ConstKon k a b :: Constraint
  type ConstKon k a b = Yes2 a b           -- fix
  const :: ConstKon k a b => b -> (a `k` b)

type ConstCatWith k a b = (ConstCat k, ConstKon k a b)

instance ConstCat (->) where
  -- type ConstKon (->) a b = ()           -- fix
  const = P.const

instance Monad m => ConstCat (Kleisli m) where
  type ConstKon (Kleisli m) a b = ()  -- why necessary?
  const a = arr (const a)

-- | Category with unit injection. Minimal definition: 'lunit' or 'runit'.
class ProductCat k => UnitCat k where
  type UnitKon k a :: Constraint
  type UnitKon k a = Yes a
  lunit :: a `k` (() :* a)
  lunit = swapP . runit
  runit :: a `k` (a :* ())
  runit = swapP . lunit

type ConstUCat k b = (UnitCat k, ConstCatWith k () b)

-- | Inject a constant on the left
lconst :: ConstUCat k a => a -> (b `k` (a :* b))
lconst a = first  (const a) . lunit

-- | Inject a constant on the right
rconst :: ConstUCat k b => b -> (a `k` (a :* b))
rconst b = second (const b) . runit

instance UnitCat (->) where
  lunit = ((),)
  runit = (,())

instance Monad m => UnitCat (Kleisli m) where
  lunit = arr lunit
  runit = arr runit

class ProductCat k => StrongCat k f where
  type StrongKon k f a b :: Constraint
  lstrength :: StrongKon k f a b => (a :* f b) `k` f (a :* b)
  rstrength :: StrongKon k f a b => (f a :* b) `k` f (a :* b)

-- TODO: Use generalized Functor

instance Functor f => StrongCat (->) f where
  type StrongKon (->) f a b = ()
  lstrength (a, bs) = fmap (a,) bs
  rstrength (as, b) = fmap (,b) as

instance (Monad m, Functor f) => StrongCat (Kleisli m) f where
  type StrongKon (Kleisli m) f a b = ()
  lstrength = arr lstrength
  rstrength = arr rstrength

-- Based on Ed K's CCC from Control.Category.Cartesian.Closed in the categories
-- package:

class ProductCat k => ClosedCat k where
  type ClosedKon k u :: Constraint  -- On the 'Exp' domain
  type ClosedKon k u = ()
  type Exp k u v
  apply   :: ClosedKon k a => (Exp k a b :* a) `k` b
  curry   :: ClosedKon k b => ((a :* b) `k` c) -> (a `k` Exp k b c)
  uncurry :: ClosedKon k b => (a `k` Exp k b c) -> ((a :* b) `k` c)

type ClosedCatWith k u = (ClosedCat k, ClosedKon k u)

instance ClosedCat (->) where
  type Exp (->) u v = u -> v
  type ClosedKon (->) u = ()
  apply (f,a) = f a
  curry       = P.curry
  uncurry     = P.uncurry

-- TODO: Would MemoTrie work as well?

-- distribMF :: Monad m => m (p -> q) -> (p -> m q)
-- distribMF u p = liftM ($ p) u

-- TODO: Is there a standard name for distribMF?
-- It's a distribution/transposition.

-- For Kleisli, use tries. Might be too sweeping, in which case, comment out
-- this instance as a suggestion for specific monads or for newtype wrappers
-- around some Klieslis.

-- instance Monad m => ClosedCat (Kleisli m) where
--   type ClosedKon (Kleisli m) u = (HasTrie u, Traversable (Trie u))
--   type Exp (Kleisli m) u v = u :->: v
--   apply   = Kleisli (return . uncurry untrie)
--   curry   = inNew $ \ f -> sequence . trie . curry f
--   uncurry = inNew $ \ h -> uncurry (distribMF . liftM untrie . h)

{- 

Derivations:

apply :: ((a +> b) :* a) `k` b
      :: Kleisli m ((a :->: b) :* a) b
      =~ (a :->: b) :* a -> m b

return . uncurry untrie :: (a :->: b) :* a -> m b
Kleisli (return . uncurry untrie) :: Kleisli m ((a :->: b) :* a) b

curry :: ((a :* b) `k` c) -> a `k` (b +> c)
      :: Kleisli m (a :* b) c -> Kleisli m a (b :->: c)
      =~ (a :* b -> m c) -> (a -> m (b :->: c))

f :: a :* b -> m c
curry f :: a -> b -> m c
trie . curry f :: a -> (b :->: m c)
sequenceA . trie . curry f :: a -> m (b :->: c)

inNew (\ f -> sequenceA . trie . curry f)
  :: Kleisli m (a :* b) c -> Kleisli m a (b :->: c)

uncurry :: a `k` (b +> c) -> ((a :* b) `k` c)
        :: Kleisli m a (b :->: c) -> Kleisli m (a :* b) c
        =~ (a -> m (b :->: c)) -> (a :* b -> m c)

h :: a -> m (b :->: c)
liftM untrie . h :: a -> m (b -> c)
distribMF . liftM untrie . h :: a -> b -> m c
uncurry (distribMF . liftM untrie . h) :: a :* b -> m c

inNew (\ h -> uncurry (distribMF . liftM untrie . h))
 :: Kleisli m a (b :->: c) -> Kleisli m (a :* b) c

-}
