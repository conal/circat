{-# LANGUAGE TypeOperators, TypeFamilies, TupleSections, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}

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
import Control.Monad (liftM,liftM2)
import Data.Traversable (Traversable,sequence)
import GHC.Prim (Constraint)

import FunctorCombo.StrictMemo (HasTrie(..),(:->:))

import Circat.Misc ((:*),(:+),(<~),inNew,inNew2)

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

-- | Operate on left-associated form
inLassocP :: ProductCat (~>) =>
             (((a :* b) :* c) ~> ((a' :* b') :* c'))
          -> ((a :* (b :* c)) ~> (a' :* (b' :* c')))
inLassocP = rassocP <~ lassocP

-- | Operate on right-associated form
inRassocP :: ProductCat (~>) =>
             ((a :* (b :* c)) ~> (a' :* (b' :* c')))
          -> (((a :* b) :* c) ~> ((a' :* b') :* c'))
inRassocP = lassocP <~ rassocP

-- | Left-associate and operate on left
inLassocPF :: ProductCat (~>) =>
              ((a :* b) ~> (a' :* b'))
           -> ((a :* (b :* c)) ~> (a' :* (b' :* c)))
inLassocPF = inLassocP . first

-- | Right-associate and operate on right
inRassocPS :: ProductCat (~>) =>
              ((b :* c) ~> (b' :* c'))
           -> (((a :* b) :* c) ~> ((a :* b') :* c'))
inRassocPS = inRassocP . second


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
  type ConstKon (~>) a b :: Constraint
  type ConstKon (~>) a b = Yes2 a b           -- fix
  const :: ConstKon (~>) a b => b -> (a ~> b)

type ConstCatWith (~>) a b = (ConstCat (~>), ConstKon (~>) a b)

instance ConstCat (->) where
  -- type ConstKon (->) a b = ()           -- fix
  const = P.const

instance Monad m => ConstCat (Kleisli m) where
  -- type ConstKon (Kleisli m) a b = ()  -- why necessary?
  const a = arr (const a)

-- | Category with unit injection. Minimal definition: 'lunit' or 'runit'.
class ProductCat (~>) => UnitCat (~>) where
  type UnitKon (~>) a :: Constraint
  type UnitKon (~>) a = Yes a
  lunit :: a ~> (() :* a)
  lunit = swapP . runit
  runit :: a ~> (a :* ())
  runit = swapP . lunit

type ConstUCat (~>) b = (UnitCat (~>), ConstCatWith (~>) () b)

-- | Inject a constant on the left
lconst :: ConstUCat (~>) a => a -> (b ~> (a :* b))
lconst a = first  (const a) . lunit

-- | Inject a constant on the right
rconst :: ConstUCat (~>) b => b -> (a ~> (a :* b))
rconst b = second (const b) . runit

instance UnitCat (->) where
  lunit = ((),)
  runit = (,())

instance Monad m => UnitCat (Kleisli m) where
  lunit = arr lunit
  runit = arr runit

class ProductCat (~>) => StrongCat (~>) f where
 lstrength :: (a :* f b) ~> f (a :* b)
 rstrength :: (f a :* b) ~> f (a :* b)

-- TODO: Use generalize Functor

instance Functor f => StrongCat (->) f where
  lstrength (a, bs) = fmap (a,) bs
  rstrength (as, b) = fmap (,b) as

-- h :: a :* b :> c
--
-- rconst idTrie :: a                 :> (a :* (b :->: b))
-- lstrength     :: a :* (b :->: b)   :> (b :->: (a :* b))
-- traverseC h   :: (b :->: (a :* b)) :> (b :->: c)
--
-- traverse h . lstrength . rconst idTrie :: a :> (b :->: c)

-- Based on Ed K's CCC from Control.Category.Cartesian.Closed in the categories
-- package:

class ProductCat (~>) => ClosedCat (~>) where
  type ClosedKon (~>) u :: Constraint  -- ^ On the 'Exp' domain
  type ClosedKon (~>) u = ()
  type Exp (~>) u v
  apply   :: ClosedKon (~>) a => (Exp (~>) a b :* a) ~> b
  curry   :: ClosedKon (~>) b => ((a :* b) ~> c) -> (a ~> Exp (~>) b c)
  uncurry :: ClosedKon (~>) b => (a ~> Exp (~>) b c) -> (a :* b) ~> c

type ClosedCatWith (~>) u = (ClosedCat (~>), ClosedKon (~>) u)

instance ClosedCat (->) where
  type Exp (->) u v = u -> v
  type ClosedKon (->) u = ()
  apply (f,a) = f a
  curry       = P.curry
  uncurry     = P.uncurry

-- TODO: Would MemoTrie work as well?

distribMF :: Monad m => m (p -> q) -> (p -> m q)
distribMF u p = liftM ($ p) u

-- TODO: Is there a standard name for distribMF?
-- It's a distribution/transposition.

-- For Kleisli, use tries. Might be too sweeping, in which case, comment out
-- this instance as a suggestion for specific monads or for newtype wrappers
-- around some Klieslis.


instance Monad m => ClosedCat (Kleisli m) where
  type ClosedKon (Kleisli m) u = (HasTrie u, Traversable (Trie u))
  type Exp (Kleisli m) u v = u :->: v
  apply   = Kleisli (return . uncurry untrie)
  curry   = inNew $ \ f -> sequence . trie . curry f
  uncurry = inNew $ \ h -> uncurry (distribMF . liftM untrie . h)

{- 

Derivations:

apply :: ((a +> b) :* a) ~> b
      :: Kleisli m ((a :->: b) :* a) b
      =~ (a :->: b) :* a -> m b

return . uncurry untrie :: (a :->: b) :* a -> m b
Kleisli (return . uncurry untrie) :: Kleisli m ((a :->: b) :* a) b

curry :: ((a :* b) ~> c) -> a ~> (b +> c)
      :: Kleisli m (a :* b) c -> Kleisli m a (b :->: c)
      =~ (a :* b -> m c) -> (a -> m (b :->: c))

f :: a :* b -> m c
curry f :: a -> b -> m c
trie . curry f :: a -> (b :->: m c)
sequenceA . trie . curry f :: a -> m (b :->: c)

inNew (\ f -> sequenceA . trie . curry f)
  :: Kleisli m (a :* b) c -> Kleisli m a (b :->: c)

uncurry :: a ~> (b +> c) -> ((a :* b) ~> c)
        :: Kleisli m a (b :->: c) -> Kleisli m (a :* b) c
        =~ (a -> m (b :->: c)) -> (a :* b -> m c)

h :: a -> m (b :->: c)
liftM untrie . h :: a -> m (b -> c)
distribMF . liftM untrie . h :: a -> b -> m c
uncurry (distribMF . liftM untrie . h) :: a :* b -> m c

inNew (\ h -> uncurry (distribMF . liftM untrie . h))
 :: Kleisli m a (b :->: c) -> Kleisli m (a :* b) c

-}
