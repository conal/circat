{-# LANGUAGE TypeOperators, TypeFamilies, TupleSections, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types, ScopedTypeVariables, CPP #-}
{-# LANGUAGE UndecidableInstances #-} -- see below
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE UndecidableSuperClasses #-} -- see below
#endif

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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
  , transposeP, transposeS
  , DistribCat(..)
  -- , ConstCat(..), ConstCatWith, ConstUCat, lconst, rconst
  , TerminalCat(..), lunit, runit
  , StrongCat(..), ClosedCat(..)
  , applyK, curryK, uncurryK 
  , unitFun, unUnitFun -- , constFun -- , constFun2
  , NatCat(..), natA
  , Rep, HasRep(..), RepCat(..)
--   , CoerceCat(..)
  , LoopCat(..), DelayCat(..)
  , BiCCC
  , HasUnitArrow(..), BiCCCC  -- in progress
#if 0
  , CondCat(..),CondCat2, prodCond, funCond  -- experimental
  , guard, if_then_else  -- experimental
#endif
  , Yes, Yes2
  , OkayArr, Uncurriable(..)
  ) where

import Prelude hiding (id,(.),curry,uncurry,sequence)
import qualified Prelude as P

import Control.Category
import qualified Control.Arrow as A
import Control.Arrow (Kleisli(..),arr)
import Control.Monad (liftM2) -- liftM,
-- import Data.Traversable (Traversable,sequence)
import GHC.Exts (Constraint)
import Data.Typeable (Typeable,cast)
import Data.Coerce

import Control.Newtype

import TypeUnary.Nat (Z,S,Nat(..),predN,IsNat(..))

-- import FunctorCombo.StrictMemo (HasTrie(..),(:->:))

import Circat.Misc (Unit,(:*),(:+),(:=>),(<~),inNew,inNew2) -- ,inNew
import Circat.Rep

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

transposeP :: ProductCat k => ((a :* b) :* (c :* d)) `k` ((a :* c) :* (b :* d))
transposeP = (exl.exl &&& exl.exr) &&& (exr.exl &&& exr.exr)

transposeS :: CoproductCat k => ((p :+ q) :+ (r :+ s)) `k` ((p :+ r) :+ (q :+ s))
transposeS = (inl.inl ||| inr.inl) ||| (inl.inr ||| inr.inr)

infixr 2 +++, |||

-- | Category with co-product. Minimal definition: 'inl', 'inr', and either
-- (a) '(|||)', (b) both '(+++)' and 'jam', or (c) both '(|||)' and '(+++)'.
-- TODO: Generalize '(:+)' to an associated type. Keep the types fairly pretty.
class Category k => CoproductCat k where
  inl     :: a `k` (a :+ b)
  inr     :: b `k` (a :+ b)
  jam     :: (a :+ a) `k` a                  -- dual to dup. standard name?
  jam     =  id ||| id
  (+++)   :: (a `k` c) -> (b `k` d) -> ((a :+ b) `k` (c :+ d))
  f +++ g =  inl . f ||| inr . g
  (|||)   :: (a `k` c) -> (b `k` c) -> ((a :+ b) `k`  c)
  f ||| g =  jam . (f +++ g)
  left    :: (a `k` a') -> ((a :+ b) `k` (a' :+ b ))
  left    =  (+++ id)
  right   :: (b `k` b') -> ((a :+ b) `k` (a  :+ b'))
  right   =  (id +++)
  swapS   :: (a :+ b) `k` (b :+ a)
  swapS   =  inr ||| inl
  lassocS :: (a :+ (b :+ c)) `k` ((a :+ b) :+ c)
  rassocS :: ((a :+ b) :+ c) `k` (a :+ (b :+ c))
  lassocS =  inl.inl ||| (inl.inr ||| inr)
  rassocS =  (inl ||| inr.inl) ||| inr.inr

-- | Apply to both parts of a coproduct
twiceC :: CoproductCat k => (a `k` c) -> ((a :+ a) `k` (c :+ c))
twiceC f = f +++ f

class DistribCat k where
  distl :: (a :* (u :+ v)) `k` (a :* u :+ a :* v)
  distr :: ((u :+ v) :* b) `k` (u :* b :+ v :* b)
  -- distr = (swapP +++ swapP) . distl . swapP -- Needs ProductCat k

instance ProductCat (->) where
  exl   = P.fst
  exr   = P.snd
  (***) = (A.***)
  (&&&) = (A.&&&)

instance CoproductCat (->) where
  inl          = Left
  inr          = Right
  (+++)        = (A.+++)
  (|||)        = (A.|||)

instance DistribCat (->) where
  distl (a,uv) = ((a,) +++ (a,)) uv
  distr (uv,b) = ((,b) +++ (,b)) uv

instance Monad m => ProductCat (Kleisli m) where
  exl   = arr exl
  exr   = arr exr
  dup   = arr dup
  (***) = inNew2 crossM

crossM :: Monad m => (a -> m c) -> (b -> m d) -> (a :* b -> m (c :* d))
(f `crossM` g) (a,b) = liftM2 (,) (f a) (g b)

instance Monad m => CoproductCat (Kleisli m) where
  inl   = arr inl
  inr   = arr inr
  jam   = arr jam
  (|||) = inNew2 (|||)

instance Monad m => DistribCat (Kleisli m) where
  distl = arr distl
  distr = arr distr

#if 0
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

type ConstUCat k b = (TerminalCat k, ConstCatWith k () b)

-- | Inject a constant on the left
lconst :: ConstUCat k a => a -> (b `k` (a :* b))
lconst a = first  (const a) . lunit

-- | Inject a constant on the right
rconst :: ConstUCat k b => b -> (a `k` (a :* b))
rconst b = second (const b) . runit
#endif

class ProductCat k => TerminalCat k where
  it :: a `k` Unit

-- Note: the ProductCat superclass is just for convenience of use elsewhere.
-- TODO: Consider removing.

lunit :: TerminalCat k => a `k` (Unit :* a)
lunit = it &&& id

runit :: TerminalCat k => a `k` (a :* Unit)
runit = id &&& it

instance TerminalCat (->) where
  it = const ()

instance Monad m => TerminalCat (Kleisli m) where
  it = arr it

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

class ProductCat k => ClosedCat k where
  apply   :: ((a :=> b) :* a) `k` b
  curry   :: ((a :* b) `k` c) -> (a `k` (b :=> c))
  uncurry :: (a `k` (b :=> c)) -> ((a :* b) `k` c)

instance ClosedCat (->) where
  apply (f,a) = f a
  curry       = P.curry
  uncurry     = P.uncurry

applyK   :: Monad m => Kleisli m (Kleisli m a b :* a) b
curryK   :: Monad m => Kleisli m (a :* b) c -> Kleisli m a (Kleisli m b c)
uncurryK :: Monad m => Kleisli m a (Kleisli m b c) -> Kleisli m (a :* b) c

applyK   = pack (apply . first unpack)
curryK   = inNew $ \ h -> return . pack . curry h
uncurryK = inNew $ \ f -> \ (a,b) -> f a >>= ($ b) . unpack

{- Types:

Enhance methods on (->):

> apply                       :: (a -> m b) :* a -> m b
> apply . first unpack        :: Kleisli m a b :* a -> m b
> pack (apply . first unpack) :: Kleisli m (Kleisli m a b :* a) b
> 
> h                              :: a :* b -> m c
> curry h                        :: a -> b -> m c
> pack . curry h                 :: a -> Kleisli m b c
> return . pack . curry h        :: a -> m (Kleisli m b c)
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

-- instance Monad m => ClosedCat (Kleisli m) where
--   type Exp (Kleisli m) a b = Kleisli m a b
--   apply   = applyK
--   curry   = curryK
--   uncurry = uncurryK

constFun :: ClosedCat k => (b `k` c) -> (a `k` (b :=> c))
constFun f = curry (f . exr)

-- f :: b `k` c
-- f . exl :: a :* b `k` c
-- curry (f . exl) :: a `k` (Exp k b c)

-- Combine with currying:

-- constFun2 :: ClosedCat k
--           => ((b :* c) `k` d) -> (a `k` (Exp k b (Exp k c d)))
-- constFun2 = constFun . curry

unitFun :: ClosedCat k => (b `k` c) -> (Unit `k` (b :=> c))
unitFun = constFun

unUnitFun :: (ClosedCat k, TerminalCat k) =>
             (Unit `k` (a :=> b)) -> (a `k` b)
unUnitFun g = uncurry g . (it &&& id)

-- | Bi-cartesion (cartesian & co-cartesian) closed categories.
-- Also lumps in terminal and distributive, though should probably be moved out.
type BiCCC k = (ClosedCat k, CoproductCat k, TerminalCat k, DistribCat k)

class HasUnitArrow k p where
  unitArrow :: p b -> Unit `k` b

class Category k => NatCat k where
  zeroA :: () `k` Nat Z
  succA :: IsNat m => Nat m `k` Nat (S m) 
  predA :: Nat (S m) `k` Nat m

natA :: forall k n. (NatCat k, IsNat n) => () `k` Nat n
natA = mk nat
 where
   mk :: Nat m -> (() `k` Nat m)
   mk Zero     = zeroA
   mk (Succ m) = succA . mk m

instance NatCat (->) where
  zeroA = const Zero
  succA = Succ
  predA = predN

#if 0
-- | Categories with coercion. The 'Typeable' constraints help with non-standard
-- types. This interface may change.
class CoerceCat k where
  coerceC :: (Typeable a, Typeable b, Coercible a b) => a `k` b

instance CoerceCat (->) where
  coerceC = coerce
#else

class RepCat k where
  reprC :: (HasRep a, Rep a ~ a') => a `k` a'
  abstC :: (HasRep a, Rep a ~ a') => a' `k` a

instance RepCat (->) where
  reprC = repr
  abstC = abst

#endif

class ProductCat k => LoopCat k where
  type LoopKon k s :: Constraint
  type LoopKon k s = Yes s
  loopC :: LoopKon k s => ((a :* s) `k` (b :* s)) -> (a `k` b)

class DelayCat k where
  type DelayKon k s :: Constraint
  type DelayKon k s = Yes s
  delayC :: DelayKon k s => s -> (s `k` s)

-- | 'BiCCC' with constant arrows.
type BiCCCC k p = (BiCCC k, RepCat k, HasUnitArrow k p, LoopCat k, DelayCat k)

#if 0
{--------------------------------------------------------------------
    Experimental
--------------------------------------------------------------------}

-- | Conditional, taking (condition,(else,then)).
-- Note the unusual order, which aligns with tries.
class CondCat k a where
  cond :: (Bool :* (a :* a)) `k` a

-- Overlaps with Unit, product, and function instances.

instance CondCat (->) a where
  cond (i,(e,t)) = if i then t else e

instance Monad m => CondCat (Kleisli m) a where
  cond = arr cond

type CondCat2 k a b = (CondCat k a, CondCat k b)

#endif

#if 0

-- Templates for instances. Overlaps with (->) in all cases and non-optimal in
-- others.

instance TerminalCat k => CondCat k Unit where cond = it

instance (ProductCat k, CondCat2 k a b)
      => CondCat k (a :*  b) where cond = prodCond

--     Variable `k' occurs more often than in the instance head
--       in the constraint: CondCat2 k a b
--     (Use -XUndecidableInstances to permit this)

instance (ClosedCat k, CondCat k b)
      => CondCat k (a :=> b) where cond = funCond

#endif

#if 0
prodCond :: forall k a b. (ProductCat k, CondCat2 k a b) =>
            (Bool :* ((a :* b) :* (a :* b))) `k` (a :* b)
prodCond = half exl &&& half exr
 where
   half :: CondCat k c => (u `k` c) -> ((Bool :* (u :* u)) `k` c)
   half f = cond . second (twiceP f)

-- funCond = \ (p,(f,g)) a -> cond (p,(f a,g a))
--         = curry \ ((p,(f,g)),a) -> cond (p,(f a,g a))

funCond :: (ClosedCat k, CondCat k b) =>
           (Bool :* ((a :=> b) :* (a :=> b))) `k` (a :=> b)
funCond = curry (cond . (exl . exl &&& (half exl &&& half exr)))
 where
   half ex = apply . first (ex . exr)

-- funCond = curry (cond . (exl . exl &&& (apply . first (exl . exr) &&& apply . first (exr . exr))))

-- instance                 CondCat (a :+  b) where cond = sumCond

-- instance                 CondCat Bool where cond = muxC

{--------------------------------------------------------------------
    Conditionals
--------------------------------------------------------------------}

type BoolUU = Unit :+ Unit

guard :: (ProductCat k, CoproductCat k, DistribCat k) =>
         (a `k` BoolUU) -> (a `k` (a :+ a))
guard p = (exl +++ exl) . distl . (id &&& p)

if_then_else :: (ProductCat k, CoproductCat k, DistribCat k) =>
                (a `k` BoolUU) -> (a `k` b) -> (a `k` b) -> (a `k` b)
if_then_else p f g = (f ||| g) . guard p

#endif

type family OkayArr (k :: * -> * -> *) a b :: Constraint

class OkayArr k (OkayDom k a b) (OkayRan k a b) => Uncurriable k a b where
  type OkayDom k a b
  type OkayRan k a b
  type OkayDom k a b = a
  type OkayRan k a b = b
  uncurries :: (a `k` b) -> (OkayDom k a b `k` OkayRan k a b)

instance ( ClosedCat k, Uncurriable k (a :* b) c
         , OkayArr k (OkayDom k (a :* b) c) (OkayRan k (a :* b) c) -- added for GHC 8.0
         )
       => Uncurriable k a (b -> c) where
  type OkayDom k a (b -> c) = OkayDom k (a :* b) c
  type OkayRan k a (b -> c) = OkayRan k (a :* b) c
  uncurries = uncurries . uncurry

instance OkayArr k a Unit   => Uncurriable k a Unit   where uncurries = id
instance OkayArr k a Bool   => Uncurriable k a Bool   where uncurries = id
instance OkayArr k a Int    => Uncurriable k a Int    where uncurries = id
instance OkayArr k a Double => Uncurriable k a Double where uncurries = id

instance OkayArr k a (c :* d) => Uncurriable k a (c :* d) where uncurries = id

--     Illegal constraint 'OkayArr k a Bool' in a superclass/instance context
--       (Use UndecidableInstances to permit this)
