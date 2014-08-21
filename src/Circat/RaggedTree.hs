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

-- data Tree a = L a | B (Tree a) (Tree a)

-- | Tree shape data kind, simplified from non-indexed Tree ()
data TU = LU | BU TU TU

-- Singleton type. 
-- TODO: Use the singletons package
data ST :: TU -> * where
  SL :: ST LU
  SB :: (HasSingT p, HasSingT q) => ST (BU p q)

class HasSingT x where singT :: ST x

instance HasSingT LU where singT = SL
instance (HasSingT p, HasSingT q) => HasSingT (BU p q) where singT = SB

data T :: TU -> * -> * where
  L :: a -> T LU a
  B :: T p a -> T q a -> T (BU p q) a

left  :: T (BU p q) a -> T p a
left  (B u _) = u

right :: T (BU p q) a -> T q a
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
pureT :: forall r a. HasSingT r => a -> T r a
pureT a = go
 where
   go :: forall p. HasSingT p => T p a
   go = case (singT :: ST p) of
          SL -> L a
          SB -> B go go

apT :: forall r a b. HasSingT r => T r (a -> b) -> T r a -> T r b
apT = case (singT :: ST r) of
        SL -> \ (L f)     (L x)     -> L (f x)
        SB -> \ (B fs gs) (B xs ys) -> B (apT fs xs) (apT gs ys)

-- TODO: Define inL and inB, and rework fmap and apT

instance HasSingT r => Applicative (T r) where
  pure  = pureT
  (<*>) = apT
#else
instance HasSingT r => Applicative (T r) where
#if 0
  pure :: forall a. a -> T r a
  pure a = go
   where
     go :: forall p. HasSingT p => T p a
     go = case (singT :: ST p) of
            SL -> L a
            SB -> B go go
#else
  -- pure :: forall a. a -> T r a
  pure a = case (singT :: ST r) of
             SL -> L a
             SB -> B (pure a) (pure a)
#endif
  -- (<*>) :: forall a b. T r (a -> b) -> T r a -> T r b
  (<*>) = case (singT :: ST r) of
            SL -> \ (L f)     (L x)     -> L (f x)
            SB -> \ (B fs gs) (B xs ys) -> B (fs <*> xs) (gs <*> ys)

-- TODO: Define inL and inB, and rework fmap and apT
#endif

joinT :: forall r a. HasSingT r => T r (T r a) -> T r a
joinT = case (singT :: ST r) of
          SL -> \ (L t)   -> t
          SB -> \ (B u v) -> B (joinT (left <$> u)) (joinT (right <$> v))

#if 0
B u v :: T (BU p q) (T (BU p q) a)
u :: T p (T (BU p q) a)
v :: T q (T (BU p q) a)
left  <$> u :: T p (T p a)
right <$> v :: T q (T q a)
joinT (left  <$> u) :: T p
joinT (right <$> v) :: T q
B (joinT (left  <$> u)) (joinT (right <$> v)) :: T (BU p q)
#endif

instance HasSingT r => Monad (T r) where
  return = pure
  t >>= f = joinT (f <$> t)

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

t1 :: T LU Bool
t1 = L False

t2 :: T (BU LU LU) Bool
t2 = B (L False) (L True)

t3 :: T (BU LU (BU LU LU)) Bool
t3 = B t1 t2

t4 :: T (BU LU (BU LU LU)) Bool
t4 = not <$> t3
