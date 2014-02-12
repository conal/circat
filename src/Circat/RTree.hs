{-# LANGUAGE GADTs, KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables, Rank2Types #-}
{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-} -- see below

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.RTree
-- Copyright   :  (c) 2012 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Right-folded trees. For now, just binary.
----------------------------------------------------------------------

module Circat.RTree where

-- TODO: explicit exports

import Prelude hiding (id,(.))

import Data.Functor ((<$),(<$>))
import Control.Applicative (Applicative(..),liftA2)
import Control.Monad (join)
import Data.Foldable
import Data.Traversable (Traversable(..))
import Control.Arrow (arr,Kleisli)

import TypeUnary.Nat hiding ((:*:))

import Circat.Misc (Unop,(<~),(:*))
import Circat.Show (showsApp1)
import Circat.Category
import Circat.Classes
import Circat.Pair -- (Pair(..),PairCat(..))
import Circat.State (pureState,StateFun,StateExp)

-- TODO: Use the generalization from numbers-vectors-trees, factoring out Pair

data Tree :: * -> * -> * where
  L :: a -> Tree Z a
  B :: IsNat n => Pair (Tree n a) -> Tree (S n) a

deriving instance Eq a => Eq (Tree n a)

instance Show a => Show (Tree n a) where
  showsPrec p (L a)  = showsApp1 "L" p a
  showsPrec p (B uv) = showsApp1 "B" p uv

class PairCat k => TreeCat k where
  toL :: a `k` Tree Z a
  unL :: Tree Z a `k` a
  toB :: IsNat n => Pair (Tree n a) `k` Tree (S n) a
  unB :: IsNat n => Tree (S n) a `k` Pair (Tree n a)

toB' :: (TreeCat k, IsNat n) => (Tree n a :* Tree n a) `k` Tree (S n) a
toB' = toB . toPair

unB' :: (TreeCat k, IsNat n) => Tree (S n) a `k` (Tree n a :* Tree n a)
unB' = unPair . unB

instance TreeCat (->) where
  toL a     = L a
  unL (L a) = a
  toB p     = (B p)
  unB (B p) = p

instance Monad m => TreeCat (Kleisli m) where
  toL = arr toL
  unL = arr unL
  toB = arr toB
  unB = arr unB

instance (TerminalCat k, TreeCat k) => TreeCat (StateFun k s) where
  toL = pureState toL
  unL = pureState unL
  toB = pureState toB
  unB = pureState unB

instance (ClosedCatWith k s, TerminalCat k, TreeCat k)
      => TreeCat (StateExp k s) where
  toL = pureState toL
  unL = pureState unL
  toB = pureState toB
  unB = pureState unB

inL :: TreeCat k => (a `k` b) -> (Tree Z a `k` Tree Z b)
inL = toL <~ unL

inB :: (TreeCat k, IsNat m, IsNat n) =>
       (Pair (Tree m a) `k` Pair (Tree n b))
    -> (Tree (S m) a `k` Tree (S n) b)
inB = toB <~ unB

inL2 :: TreeCat k => (a -> b `k` c) -> (Tree Z a -> Tree Z b `k` Tree Z c)
inL2 = inL <~ unL

inB2 :: (TreeCat k, IsNat m, IsNat n, IsNat o) =>
        (Pair (Tree m a) -> Pair (Tree n b) `k` Pair (Tree o c))
     -> (Tree (S m) a -> Tree (S n) b `k` Tree (S o) c)
inB2 = inB <~ unB

-- TODO: Maybe resurrect my category-generalized Newtype and use in place of inL
-- etc. What would become of TreeCat and VecCat?

instance IsNat n => Functor (Tree n) where
  fmap = fmap' nat
   where
     fmap' :: Nat m -> (a -> b) -> (Tree m a -> Tree m b)
     fmap' Zero     = inL
     fmap' (Succ n) = inB . fmap . fmap' n

-- TODO: Categorical generalization (easy)

instance IsNat n => Applicative (Tree n) where
  pure a = a <$ units nat
  (<*>)  = ap' nat
   where
     ap' :: Nat m -> Tree m (a -> b) -> Tree m a -> Tree m b
     ap' Zero     = inL2 ($)
     ap' (Succ n) = inB2 (liftA2 (ap' n))

units :: Nat n -> Tree n ()
units Zero     = L ()
units (Succ n) = B (pure (units n))

instance Foldable (Tree n) where
  foldMap f (L  a) = f a
  foldMap f (B uv) = (foldMap . foldMap) f uv

instance IsNat n => Traversable (Tree n) where
  traverse f (L a ) = L <$> f a
  traverse f (B uv) = B <$> (traverse.traverse) f uv

instance IsNat n => Monad (Tree n) where
  return = pure
  m >>= f = joinT (fmap f m)

joinT :: Tree n (Tree n a) -> Tree n a
joinT (L t)  = t
joinT (B uv) = B . fmap joinT . join . fmap sequenceA . (fmap . fmap) unB $ uv

{-

-- joinT (B uv) = B . joinMMT . (fmap . fmap) unB $ uv

-- TODO: Generalize this construction past (->). Rework def without sequenceA.
-- TODO: Generalize past Tree. Use pack/unpack?

-- TODO: joinT' to use inB

joinT' :: Nat n -> Tree n (Tree n a) -> Tree n a
joinT' Zero = unL
joinT' (Succ m) = B . fmap (joinT' m) . join . fmap sequenceA . unB . fmap unB

-- uv :: P (Tree m (Tree (S m) a))

-- (fmap . fmap) unB $ uv :: P (Tree m (P (Tree m a)))

-- fmap sequenceA $ '' :: P (P (Tree m (Tree m a)))
-- join $ '' :: P (Tree m (Tree m a))
-- fmap join $ '' :: P (Tree m a)
-- B $ '' :: Tree (S m) a

--   B
-- . fmap join
-- . join
-- . fmap sequenceA
-- . (fmap . fmap) unB

-}

instance CTraversable (Tree Z) where
  type CTraversableKon (Tree Z) k = TreeCat k
  traverseC = inL

instance (IsNat n, CTraversable (Tree n)) => CTraversable (Tree (S n)) where
  type CTraversableKon (Tree (S n)) k =
    (TreeCat k, CTraversableKon (Tree n) k)
  traverseC = inB . traverseC . traverseC

{--------------------------------------------------------------------
    Addition
--------------------------------------------------------------------}

instance (ConstCat k, AddCat k, TreeCat k, IsNat n)
      => AddsCat k (Tree n) where
  adds = addTN nat

type AddTP n = forall k. (ConstCat k, AddCat k, TreeCat k) =>
               Adds k (Tree n)

addTN :: Nat n -> AddTP n
addTN Zero     = first toL . fullAdd . second unL
addTN (Succ n) =
    first toB' . lassocP . second (addTN n)
  . inLassocP (first (addTN n)) . second unB'

-- swapP because I want to consider the left as LSB.

{- Derivation:

-- C carry, A addend pair, R result

second unB'      :: C * As (S n) `k` C * (As n * As n)
lassocP          ::              `k` (C * As n) * As n
first (addTN n)  ::              `k` (Rs n * C) * As n
rassocP          ::              `k` Rs n * (C * As n)
second (addTN n) ::              `k` Rs n * (Rs n * C)
lassocP          ::              `k` (Rs n * Rs n) * C
first toB'       ::              `k` Rs (S n) * C

-}

{--------------------------------------------------------------------
    Miscellany. May remove later, or might prove useful.
--------------------------------------------------------------------}

tree :: (a -> b)
     -> (forall m. (IsNat m, S m ~ n) => Pair (Tree m a) -> b)
     -> (Tree n a -> b)
tree l _ (L a) = l a
tree _ b (B u) = b u

-- Fold for trees. How does it relate to the Foldable instance? We can easily
-- define fold or foldMap via foldT. What about conversely?
foldT :: forall a b n. (a -> b) -> (Pair b -> b) -> (Tree n a -> b)
foldT l b = foldT'
 where
   foldT' :: forall m. Tree m a -> b
   foldT' = tree l (b . fmap foldT')

-- foldT l b = tree l (b . fmap (foldT l b))

-- foldT l b = foldT'
--  where
--    foldT' :: Tree m a -> b
--    foldT' (L a) = l a
--    foldT' (B p) = b (foldT' <$> p)

retree :: (a -> b)
       -> (forall m. (IsNat m, S m ~ n) => Pair (Tree m a) -> Pair (Tree m b))
       -> (Tree n a -> Tree n b)
retree l _ (L a) = (L . l) a
retree _ b (B u) = (B . b) u

-- I'd rather say
--   retree l b = tree (L . l) (B . b)
-- but I get
--   Couldn't match type `S m' with `Z'

-- | Reverse a tree. Transform away later
reverseT :: Unop (Tree n a)
reverseT = retree id (inPair swapP . fmap reverseT)

-- Or
-- reverseT = retree id (fmap reverseT . swapP)

fromList :: IsNat n => [a] -> Tree n a
fromList = fromList' nat

fromList' :: Nat n -> [a] -> Tree n a
fromList' Zero     [a] = L a
fromList' Zero     _   = error "fromList': length mismatch"
fromList' (Succ n) as  = B (fromList' n <$> halves as)

halves :: [a] -> Pair [a]
halves as = toPair (splitAt (length as `div` 2) as)

