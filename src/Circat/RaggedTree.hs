{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds, GADTs, KindSignatures, ScopedTypeVariables #-}
-- {-# LANGUAGE InstanceSigs #-} -- experiment
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
  BSsing :: (HasTSing p, HasTSing q) => TSing (BS p q)

-- TODO: Could I use HasTSing constraints in place of the TSing arguments?

class HasTSing x where tSing :: TSing x

instance HasTSing LS where tSing = LSsing
instance (HasTSing p, HasTSing q) => HasTSing (BS p q) where tSing = BSsing

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

#if 0
pureT :: forall r a. HasTSing r => a -> T r a
pureT a = go
 where
   go :: forall p. HasTSing p => T p a
   go = case (tSing :: TSing p) of
          LSsing -> L a
          BSsing -> B go go

apT :: forall r a b. HasTSing r => T r (a -> b) -> T r a -> T r b
apT = case (tSing :: TSing r) of
        LSsing -> \ (L f)     (L x)     -> L (f x)
        BSsing -> \ (B fs gs) (B xs ys) -> B (apT fs xs) (apT gs ys)

-- TODO: Define inL and inB, and rework fmap and apT

instance HasTSing r => Applicative (T r) where
  pure  = pureT
  (<*>) = apT
#else
instance HasTSing r => Applicative (T r) where
#if 0
  pure :: forall a. a -> T r a
  pure a = go
   where
     go :: forall p. HasTSing p => T p a
     go = case (tSing :: TSing p) of
            LSsing -> L a
            BSsing -> B go go
#else
  -- pure :: forall a. a -> T r a
  pure a = case (tSing :: TSing r) of
             LSsing -> L a
             BSsing -> B (pure a) (pure a)
#endif
  -- (<*>) :: forall a b. T r (a -> b) -> T r a -> T r b
  (<*>) = case (tSing :: TSing r) of
            LSsing -> \ (L f)     (L x)     -> L (f x)
            BSsing -> \ (B fs gs) (B xs ys) -> B (fs <*> xs) (gs <*> ys)

-- TODO: Define inL and inB, and rework fmap and apT
#endif

joinT :: forall r a. HasTSing r => T r (T r a) -> T r a
joinT = case (tSing :: TSing r) of
          LSsing -> \ (L t)   -> t
          BSsing -> \ (B u v) -> B (joinT (left <$> u)) (joinT (right <$> v))

#if 0
B u v :: T (BS p q) (T (BS p q) a)
u :: T p (T (BS p q) a)
v :: T q (T (BS p q) a)
left  <$> u :: T p (T p a)
right <$> v :: T q (T q a)
joinT (left  <$> u) :: T p
joinT (right <$> v) :: T q
B (joinT (left  <$> u)) (joinT (right <$> v)) :: T (BS p q)
#endif

instance HasTSing r => Monad (T r) where
  return = pure
  t >>= f = joinT (f <$> t)


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
