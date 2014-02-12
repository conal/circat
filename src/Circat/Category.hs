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
  , ProductCat(..), twiceP, inLassocP, inRassocP, inLassocPF, inRassocPS
  , CoproductCat(..), twiceC
  , ConstCat(..), ConstCatWith, ConstUCat
  , TerminalCat(..), lunit, runit
  , lconst, rconst
  , StrongCat(..), ClosedCat(..), ClosedCatWith
  , constFun -- , constFun2
  , Yes
  ) where

import Prelude hiding (id,(.),const,curry,uncurry,sequence)
import qualified Prelude as P

import Control.Category
import qualified Control.Arrow as A
import Control.Arrow (Kleisli(..),arr)
import Control.Monad (liftM2) -- liftM,
-- import Data.Traversable (Traversable,sequence)
import GHC.Prim (Constraint)

import Control.Newtype

-- import FunctorCombo.StrictMemo (HasTrie(..),(:->:))

import Circat.Misc (Unit,(:*),(:+),(<~),inNew,inNew2) -- ,inNew

infixr 3 ***, &&&

-- | Hack to get around broken constraint defaults like () or ()~().
-- Doesn't seem to do the trick.
class Yes a
instance Yes a

class Yes2 a b
instance Yes2 a b

-- | Category with product. Minimal definition: 'exl', 'exr', and either (a)
-- '(&&&)' or (b) both '(***)' and 'dup'. TODO: Generalize '(:*)' to an
-- associated type. Keep the types fairly pretty.
class Category k => ProductCat k where
  exl     :: (a :* b) `k` a
  exr     :: (a :* b) `k` b
  dup     :: a `k` (a :* a)
  dup     =  id &&& id
  swapP   :: (a :* b) `k` (b :* a)
  swapP   =  exr &&& exl
  (***)   :: (a `k` c) -> (b `k` d) -> ((a :* b) `k` (c :* d))
  f *** g =  f . exl &&& g . exr
  (&&&)   :: (a `k` c) -> (a `k` d) -> (a `k` (c :* d))
  f &&& g =  (f *** g) . dup
  first   :: (a `k` a') -> ((a :* b) `k` (a' :* b))
  first   =  (*** id)
  second  :: (b `k` b') -> ((a :* b) `k` (a :* b'))
  second  =  (id ***)
  lassocP :: (a :* (b :* c)) `k` ((a :* b) :* c)
  lassocP =  second exl &&& (exr . exr)
  rassocP :: ((a :* b) :* c) `k` (a :* (b :* c))
  rassocP =  (exl . exl) &&& first  exr

--   ldistribP :: (a, u :* v) `k` ((a,u) :* (a,v))
--   ldistribP =  transPair . first  dup -- second exl &&& second exr
--   rdistribP :: (u :* v, b) `k` ((u,b) :* (v,b))
--   rdistribP =  transPair . second dup -- first  exl &&& first  exr

-- | Apply to both parts of a product
twiceP :: ProductCat k => (a `k` c) -> ((a :* a) `k` (c :* c))
twiceP f = f *** f

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

-- | Category with co-product. Minimal definition: 'inl', 'inr', and either
-- (a) '(|||)', (b) both '(+++)' and 'jam', or (c) both '(|||)' and '(+++)'.
-- TODO: Generalize '(:+)' to an associated type. Keep the types fairly pretty.
class Category k => CoproductCat k where
  inl       :: a `k` (a :+ b)
  inr       :: b `k` (a :+ b)
  jam       :: (a :+ a) `k` a                  -- dual to dup. standard name?
  jam       =  id ||| id
  (+++)     :: (a `k` c) -> (b `k` d) -> ((a :+ b) `k` (c :+ d))
  f +++ g   =  inl . f ||| inr . g
  (|||)     :: (a `k` c) -> (b `k` c) -> ((a :+ b) `k`  c)
  f ||| g   =  jam . (f +++ g)
  left      :: (a `k` a') -> ((a :+ b) `k` (a' :+ b ))
  left      =  (+++ id)
  right     :: (b `k` b') -> ((a :+ b) `k` (a  :+ b'))
  right     =  (id +++)
  ldistribS :: (a :* (u :+ v)) `k` (a :* u :+ a :* v)
  rdistribS :: ((u :+ v) :* b) `k` (u :* b :+ v :* b)
  swapS     :: (a :+ b) `k` (b :+ a)
  swapS     =  inr ||| inl
  lassocS   :: (a :+ (b :+ c)) `k` ((a :+ b) :+ c)
  rassocS   :: ((a :+ b) :+ c) `k` (a :+ (b :+ c))
  lassocS   =  inl.inl ||| (inl.inr ||| inr)
  rassocS   =  (inl ||| inr.inl) ||| inr.inr

  -- rdistribS = (swapP +++ swapP) . ldistribS . swapP -- Needs ProductCat k

-- | Apply to both parts of a coproduct
twiceC :: CoproductCat k => (a `k` c) -> ((a :+ a) `k` (c :+ c))
twiceC f = f +++ f

instance ProductCat (->) where
  exl   = P.fst
  exr   = P.snd
  (***) = (A.***)
  (&&&) = (A.&&&)

instance CoproductCat (->) where
  inl              = Left
  inr              = Right
  (+++)            = (A.+++)
  (|||)            = (A.|||)
  ldistribS (a,uv) = ((a,) +++ (a,)) uv
  rdistribS (uv,b) = ((,b) +++ (,b)) uv

instance Monad m => ProductCat (Kleisli m) where
  exl   = arr exl
  exr   = arr exr
  dup   = arr dup
  (***) = inNew2 crossM

crossM :: Monad m => (a -> m c) -> (b -> m d) -> (a :* b -> m (c :* d))
(f `crossM` g) (a,b) = liftM2 (,) (f a) (g b)

instance Monad m => CoproductCat (Kleisli m) where
  inl       = arr inl
  inr       = arr inr
  jam       = arr jam
  ldistribS = arr ldistribS
  rdistribS = arr rdistribS
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

class ProductCat k => TerminalCat k where
  it :: a `k` Unit

-- Note: the ProductCat superclass is just for convenience of use elsewhere.
-- TODO: Consider removing.

lunit :: TerminalCat k => a `k` (Unit :* a)
lunit = it &&& id
-- lunit = swapP . runit

runit :: TerminalCat k => a `k` (a :* Unit)
runit = id &&& it
-- runit = swapP . lunit


instance TerminalCat (->) where
  it = const ()

instance Monad m => TerminalCat (Kleisli m) where
  it = arr it

type ConstUCat k b = (TerminalCat k, ConstCatWith k () b)

-- | Inject a constant on the left
lconst :: ConstUCat k a => a -> (b `k` (a :* b))
lconst a = first  (const a) . lunit

-- | Inject a constant on the right
rconst :: ConstUCat k b => b -> (a `k` (a :* b))
rconst b = second (const b) . runit

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

instance Monad m => ClosedCat (Kleisli m) where
  type Exp (Kleisli m) a b = Kleisli m a b
  apply   = pack (apply . first unpack)
  curry   = inNew $ \ h -> return . pack . curry h
  uncurry = inNew $ \ f -> \ (a,b) -> f a >>= ($ b) . unpack

{- Types:

Enhance methods on (->):

> apply                :: (a -> m b) :* a -> m b
> apply . first unpack :: Kleisli m a b :* a -> m b
>                      :: Kleisli m (Kleisli m a b :* a) b
> 
> h                              :: a :* b -> m c
> curry h                        :: a -> b -> m c
> pack . curry h                 :: a -> Kleisli m b c
> return . pack . curry h        :: a -> m (Kleisli m b c)
> pack (return . pack . curry h) :: Kleisli m a (Kleisli m b c)
> 
> f                                   :: a -> m (Kleisli m b c)
> a                                   :: a
> b                                   :: b
> f a                                 :: m (Kleisli m b c)
> liftM unpack (f a)                  :: m (b -> m c)
> liftM (($ b) . unpack) (f a)        :: m (m c)
> join (liftM (($ b) . unpack) (f a)) :: m c
> f a >>= ($ b) . unpack              :: m c

-}

constFun :: (ClosedCat k, ClosedKon k b)
         => (b `k` c) -> (a `k` (Exp k b c))
constFun f = curry (f . exr)

-- f :: b `k` c
-- f . exl :: a :* b `k` c
-- curry (f . exl) :: a `k` (Exp k b c)

-- Combine with currying:

-- constFun2 :: (ClosedCat k, ClosedKon k b, ClosedKon k c)
--           => ((b :* c) `k` d) -> (a `k` (Exp k b (Exp k c d)))
-- constFun2 = constFun . curry
