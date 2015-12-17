{-# LANGUAGE CPP #-}
-- #define Testing

{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds, GADTs, KindSignatures, ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable #-}
-- {-# LANGUAGE InstanceSigs #-} -- experiment
-- {-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}  -- See below

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}

#ifdef Testing
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP
#endif
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

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

module Circat.RaggedTree
  ( GTree(..),Tree,TU(..)
  , R1, R2, R3, R4, R5, R8, R11, R13
  , tree1, tree2, tree3, tree4, tree5, tree8, tree11, tree13,
  ) where

import Prelude hiding (zipWith)

import Data.Monoid ({-Monoid(..),-}(<>))
-- import Data.Functor ((<$>))
import Control.Applicative ({-Applicative(..),-}liftA2)
-- import Data.Foldable (Foldable(..))
-- import Data.Traversable (Traversable(..))
import Data.Typeable (Typeable)

import Circat.Misc ((:*))
import Circat.Show (showsApp1,showsApp2)
import Circat.Rep
-- import Circat.If
import Circat.Scan

-- data Tree a = L a | B (Tree a) (Tree a)

-- | Tree shape data kind, simplified from non-indexed Tree ()
data TU = LU | BU TU TU

deriving instance Typeable LU
deriving instance Typeable BU

-- Singleton type. 
-- TODO: Use the singletons package
data ST :: TU -> * where
  SL :: ST LU
  SB :: (HasSingT p, HasSingT q) => ST (BU p q)

class HasSingT p where singT :: ST p

instance HasSingT LU where singT = SL
instance (HasSingT p, HasSingT q) => HasSingT (BU p q) where singT = SB

data GTree :: TU -> * -> * where
  L :: a -> Tree LU a
  B :: Tree p a -> Tree q a -> Tree (BU p q) a

deriving instance Typeable GTree

type Tree = GTree

deriving instance Eq  a => Eq  (Tree n a)
deriving instance Ord a => Ord (Tree n a)

-- instance Ord a => Ord (Tree n a) where
--   compare (L a  ) = \ (L a'   ) -> a     `compare` a'
--   compare (B u v) = \ (B u' v') -> (u,v) `compare` (u',v')

-- TODO: Redo in 'case singT' style

type instance Rep (ST LU) = ()
instance HasRep (ST LU) where
  repr SL = ()
  abst () = SL

type instance Rep (ST (BU p q)) = ST p :* ST q
instance (HasSingT p, HasSingT q) => HasRep (ST (BU p q)) where
  repr SB = (singT :: ST p , singT :: ST q)
  abst _  = SB

type instance Rep (Tree LU a) = a
instance HasRep (Tree LU a) where
  repr (L a) = a
  abst a = L a

type instance Rep (Tree (BU p q) a) = Tree p a :* Tree q a
instance HasRep (Tree (BU p q) a) where
  repr (B u v) = (u,v)
  abst (u,v) = B u v

left  :: Tree (BU p q) a -> Tree p a
left  (B u _) = u

right :: Tree (BU p q) a -> Tree q a
right (B _ v) = v

instance Show a => Show (Tree p a) where
  showsPrec p (L a)   = showsApp1 "L" p a
  showsPrec p (B u v) = showsApp2 "B" p u v

instance Functor (Tree r) where
  fmap f (L a)   = L (f a)
  fmap f (B u v) = B (fmap f u) (fmap f v)
  {-# INLINE fmap #-}

instance Foldable (Tree r) where
  foldMap f (L a)   = f a
  foldMap f (B u v) = foldMap f u <> foldMap f v
  {-# INLINE foldMap #-}

instance Traversable (Tree r) where
  traverse f (L a)   = L <$> f a
  traverse f (B u v) = B <$> traverse f u <*> traverse f v
  {-# INLINE traverse #-}

instance HasSingT r => Applicative (Tree r) where
  pure a = case (singT :: ST r) of
             SL -> L a
             SB -> B (pure a) (pure a)
  (<*>)  = case (singT :: ST r) of
             SL -> \ (L f)     (L x)     -> L (f x)
             SB -> \ (B fs gs) (B xs ys) -> B (fs <*> xs) (gs <*> ys)
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

-- TODO: Define inL and inB, and rework fmap and apT

instance HasSingT r => Monad (Tree r) where
  return = pure
  t >>= f = joinT (f <$> t)
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}

joinT :: forall r a. HasSingT r => Tree r (Tree r a) -> Tree r a
joinT = case (singT :: ST r) of
          SL -> \ (L t)   -> t
          SB -> \ (B u v) -> B (joinT (left <$> u)) (joinT (right <$> v))
{-# INLINE joinT #-}

#if 0
B u v :: Tree (BU p q) (Tree (BU p q) a)
u :: Tree p (Tree (BU p q) a)
v :: Tree q (Tree (BU p q) a)
left  <$> u :: Tree p (Tree p a)
right <$> v :: Tree q (Tree q a)
joinT (left  <$> u) :: Tree p
joinT (right <$> v) :: Tree q
B (joinT (left <$> u)) (joinT (right <$> v)) :: Tree (BU p q)
#endif

#if 0
-- Experiment in dropping the HasSingT constraint.
-- Sadly, I still need it for pure/return.

apT :: Tree r (a -> b) -> Tree r a -> Tree r b
L f     `apT` L x     = L (f x)
B fs gs `apT` B xs ys = B (fs `apT` xs) (gs `apT` ys)
-- GHC complains of non-exhaustive patterns. Alternatively,
apT' :: Tree r (a -> b) -> Tree r a -> Tree r b
apT' (L f)     = \ (L x)     -> L (f x)
apT' (B fs gs) = \ (B xs ys) -> B (fs `apT'` xs) (gs `apT'` ys)

joinT' :: Tree r (Tree r a) -> Tree r a
joinT' (L t)   = t
joinT' (B u v) = B (joinT' (left <$> u)) (joinT' (right <$> v))
#endif

#if 0
instance LScan (Tree LU) where
  lscan (L a) = (L mempty, a)

instance (LScan (Tree p), LScan (Tree q)) => LScan (Tree (BU p q)) where
  lscan (B u v) = (B u' v', tot)
   where
     ((u',v'),tot) = lscanProd (u,v)
#else

instance HasSingT r => LScan (Tree r) where
  lscan = case (singT :: ST r) of
            SL -> \ (L a)   -> (L mempty, a)
            SB -> \ (B u v) -> let ((u',v'),tot) = lscanProd (u,v) in (B u' v', tot)
  {-# INLINE lscan #-}

#endif

#if 0
instance (HasIf (Rep (Tree r a)), HasRep (Tree r a)) =>
  HasIf (Tree r a) where if_then_else = repIf

--     Constraint is no smaller than the instance head
--       in the constraint: HasIf (Rep (Vec n a))
--     (Use UndecidableInstances to permit this)
#endif
instance HasSingT r => Zippable (Tree r) where
  zipWith = case (singT :: ST r) of
              SL -> \ f (L  a ) (L  b ) -> L (f a b)
              SB -> \ f (B u v) (B s t) -> B (zipWith f u s) (zipWith f v t)
  {-# INLINE zipWith #-}

#if 0
B u v :: Tree (BU p q) a
B s t :: Tree (BU p q) b
u :: Tree p a
v :: Tree q a
s :: Tree p b
t :: Tree q b
zipWith f u s :: Tree p c
zipWith f v t :: Tree q c
B (zipWith f u s) (zipWith f v t) :: Tree (BU p q) c
#endif

{--------------------------------------------------------------------
    Construction (for examples)
--------------------------------------------------------------------}

type R1  = LU
type R2  = BU R1 R1
type R3  = BU R2 R1
type R4  = BU R2 R2
type R5  = BU R3 R2
type R8  = BU R3 R5
type R11 = BU R8 R3
type R13 = BU R8 R5

-- type R8'  = BU R4  R4
-- type R13' = BU R8' R3

tree1 :: a -> Tree R1 a
tree1 a = L a

tree2 :: a -> a -> Tree R2 a
tree2 a b = B (tree1 a) (tree1 b)

tree3 :: a -> a -> a -> Tree R3 a
tree3 a b c = B (tree2 a b) (tree1 c)

tree4 :: a -> a -> a -> a -> Tree R4 a
tree4 a b c d = B (tree2 a b) (tree2 c d)

tree5 :: a -> a -> a -> a -> a -> Tree R5 a
tree5 a b c d e = B (tree3 a b c) (tree2 d e)

tree8 :: a -> a -> a -> a -> a -> a -> a -> a -> Tree R8 a
tree8 a b c d e f g h = B (tree3 a b c) (tree5 d e f g h)

tree11 :: a -> a -> a -> a -> a -> a -> a -> a
       -> a -> a -> a
       -> Tree R11 a
tree11 a b c d e f g h i j k =
  B (tree8 a b c d e f g h) (tree3 i j k)

tree13 :: a -> a -> a -> a -> a -> a -> a -> a
       -> a -> a -> a -> a -> a
       -> Tree R13 a
tree13 a b c d e f g h i j k l m =
  B (tree8 a b c d e f g h) (tree5 i j k l m)

#ifdef Testing

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

t1 :: Tree R1 Bool
t1 = L False

t2 :: Tree R2 Bool
t2 = B (L False) (L True)

t3 :: Tree R3 Bool
t3 = B t2 t1

t4 :: Tree R3 Bool
t4 = not <$> t3

#endif

{--------------------------------------------------------------------
    Numeric instances via the applicative-numbers package
--------------------------------------------------------------------}

-- Generate bogus (error-producing) Enum
#define INSTANCE_Enum

#define CONSTRAINTS HasSingT r, 

#define APPLICATIVE Tree r
#include "ApplicativeNumeric-inc.hs"
