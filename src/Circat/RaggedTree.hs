{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds, GADTs, KindSignatures, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.RaggedTree
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Shape-typed ragged trees
----------------------------------------------------------------------

module Circat.RaggedTree where

-- TODO: explicit exports

import Data.Monoid ((<>))
import Data.Functor ((<$>))
import Control.Applicative (Applicative(..))
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))

import Circat.Show (showsApp1,showsApp2)

-- | Tree shape data kind
data TS = LS | BS TS TS

-- Singleton type. 
-- TODO: Use the singletons package
data TSing :: TS -> * where
  LSsing :: TSing LS
  BSsing :: -- (HasTSing p, HasTSing q) =>
            TSing p -> TSing q -> TSing (BS p q)

-- TODO: Could I use HasTSing constraints in place of the TSing arguments?

class HasTSing x where tSing :: TSing x

instance HasTSing LS where tSing = LSsing
instance (HasTSing p, HasTSing q) => HasTSing (BS p q) where tSing = BSsing tSing tSing

data T :: TS -> * -> * where
  L :: a -> T LS a
  B :: T p a -> T q a -> T (BS p q) a

left  :: T (BS p q) a -> T p a
left  (B u _) = u

right :: T (BS p q) a -> T q a
right (B _ v) = v

instance Show a => Show (T p a) where
  showsPrec p (L a)   = showsApp1 "L" p a
  showsPrec p (B u v) = showsApp2 "B" p u v

instance Functor (T u) where
  fmap f (L a)   = L (f a)
  fmap f (B u v) = B (fmap f u) (fmap f v)

instance Foldable (T u) where
  foldMap f (L a)   = f a
  foldMap f (B u v) = foldMap f u <> foldMap f v

instance Traversable (T u) where
  traverse f (L a)   = L <$> f a
  traverse f (B u v) = B <$> traverse f u <*> traverse f v

-- instance Applicative (T u) where
--   L f <*> L a = L (f a)
--   B fs gs <*> B xs ys = B (fs <*> xs) (gs <*> ys)

instance HasTSing r => Applicative (T r) where
  pure  = pureT tSing
  (<*>) = apT   tSing

-- pureT :: TSing p -> a -> T p a
-- pureT LSsing a = L a
-- pureT (BSsing p q) a = B (pureT p a) (pureT q a)

pureT :: forall a r. TSing r -> a -> T r a
pureT r a = go r
 where
   go :: TSing q -> T q a
   go LSsing = L a
   go (BSsing p q) = B (go p) (go q)

apT :: TSing r -> T r (a -> b) -> T r a -> T r b
apT LSsing       = \ (L f) (L x) -> L (f x)
apT (BSsing p q) = \ (B fs gs) (B xs ys) -> B (apT p fs xs) (apT q gs ys)

-- TODO: Define inL and inB, and rework fmap and apT

instance HasTSing r => Monad (T r) where
  return = pure
  t >>= f = joinT tSing (f <$> t)

joinT :: TSing r -> T r (T r a) -> T r a
joinT LSsing       = \ (L t) -> t
joinT (BSsing p q) = \ (B u v) -> B (joinT p (left <$> u)) (joinT q (right <$> v))

#if 0
p :: TS p
q :: TS q
B u v :: T (BS p q) (T (BS p q) a)
u :: T p (T (BS p q) a)
v :: T q (T (BS p q) a)
left  <$> u :: T p (T p a)
right <$> v :: T q (T q a)
joinT p (left  <$> u) :: T p
joinT q (right <$> v) :: T q
B (joinT p (left  <$> u)) (joinT q (right <$> v)) :: T (BS p q)
#endif

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

t1 :: T LS Bool
t1 = L False

t2 :: T (BS LS LS) Bool
t2 = B (L False) (L True)

t3 :: T (BS LS (BS LS LS)) Bool
t3 = B t1 t2

t4 :: T (BS LS (BS LS LS)) Bool
t4 = not <$> t3
