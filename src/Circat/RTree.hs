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

-- TODO: Use the generalization from numbers-vectors-trees, factoring out Pair

data T :: * -> * -> * where
  L :: a -> T Z a
  B :: IsNat n => Pair (T n a) -> T (S n) a

deriving instance Eq a => Eq (T n a)

instance Show a => Show (T n a) where
  showsPrec p (L a)  = showsApp1 "L" p a
  showsPrec p (B uv) = showsApp1 "B" p uv

class PairCat (~>) => TreeCat (~>) where
  toL :: a ~> T Z a
  unL :: T Z a ~> a
  toB :: IsNat n => Pair (T n a) ~> T (S n) a
  unB :: IsNat n => T (S n) a ~> Pair (T n a)

toB' :: (TreeCat (~>), IsNat n) => (T n a :* T n a) ~> T (S n) a
toB' = toB . toPair

unB' :: (TreeCat (~>), IsNat n) => T (S n) a ~> (T n a :* T n a)
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

inL :: TreeCat (~>) => (a ~> b) -> (T Z a ~> T Z b)
inL = toL <~ unL

inB :: (TreeCat (~>), IsNat m, IsNat n) =>
       (Pair (T m a) ~> Pair (T n b))
    -> (T (S m) a ~> T (S n) b)
inB = toB <~ unB

inL2 :: TreeCat (~>) => (a -> b ~> c) -> (T Z a -> T Z b ~> T Z c)
inL2 = inL <~ unL

inB2 :: (TreeCat (~>), IsNat m, IsNat n, IsNat o) =>
        (Pair (T m a) -> Pair (T n b) ~> Pair (T o c))
     -> (T (S m) a -> T (S n) b ~> T (S o) c)
inB2 = inB <~ unB

-- TODO: Maybe resurrect my category-generalized Newtype and use in place of inL
-- etc. What would become of TreeCat and VecCat?

instance IsNat n => Functor (T n) where
  fmap = fmap' nat
   where
     fmap' :: Nat m -> (a -> b) -> (T m a -> T m b)
     fmap' Zero     = inL
     fmap' (Succ n) = inB . fmap . fmap' n

-- TODO: Categorical generalization (easy)

instance IsNat n => Applicative (T n) where
  pure a = a <$ units nat
  (<*>)  = ap' nat
   where
     ap' :: Nat m -> T m (a -> b) -> T m a -> T m b
     ap' Zero     = inL2 ($)
     ap' (Succ n) = inB2 (liftA2 (ap' n))

units :: Nat n -> T n ()
units Zero     = L ()
units (Succ n) = B (pure (units n))

instance Foldable (T n) where
  foldMap f (L  a) = f a
  foldMap f (B uv) = (foldMap . foldMap) f uv

instance IsNat n => Traversable (T n) where
  traverse f (L a ) = L <$> f a
  traverse f (B uv) = B <$> (traverse.traverse) f uv

instance IsNat n => Monad (T n) where
  return = pure
  m >>= f = joinT (fmap f m)

joinT :: T n (T n a) -> T n a
joinT (L t)  = t
joinT (B uv) = B . fmap joinT . join . fmap sequenceA . (fmap . fmap) unB $ uv

{-

-- joinT (B uv) = B . joinMMT . (fmap . fmap) unB $ uv

-- TODO: Generalize this construction past (->). Rework def without sequenceA.
-- TODO: Generalize past T. Use pack/unpack?

-- TODO: joinT' to use inB

joinT' :: Nat n -> T n (T n a) -> T n a
joinT' Zero = unL
joinT' (Succ m) = B . fmap (joinT' m) . join . fmap sequenceA . unB . fmap unB

-- uv :: P (T m (T (S m) a))

-- (fmap . fmap) unB $ uv :: P (T m (P (T m a)))

-- fmap sequenceA $ '' :: P (P (T m (T m a)))
-- join $ '' :: P (T m (T m a))
-- fmap join $ '' :: P (T m a)
-- B $ '' :: T (S m) a

--   B
-- . fmap join
-- . join
-- . fmap sequenceA
-- . (fmap . fmap) unB

-}

instance CTraversable (T Z) where
  type CTraversableConstraint (T Z) (~>) = TreeCat (~>)
  traverseC = inL

instance (IsNat n, CTraversable (T n)) => CTraversable (T (S n)) where
  type CTraversableConstraint (T (S n)) (~>) =
    (TreeCat (~>), CTraversableConstraint (T n) (~>))
  traverseC = inB . traverseC . traverseC

{--------------------------------------------------------------------
    Addition
--------------------------------------------------------------------}

instance (ConstCat (~>), AddCat (~>), TreeCat (~>), IsNat n)
      => AddsCat (~>) (T n) where
  adds = addTN nat

type AddTP n = forall (~>). (ConstCat (~>), AddCat (~>), TreeCat (~>)) =>
               Adds (~>) (T n)

addTN :: Nat n -> AddTP n
addTN Zero     = first toL . fullAdd . second unL
addTN (Succ n) =
    first toB' . lassocP . second (addTN n)
  . inLassocP (first (addTN n)) . second unB'

-- swapP because I want to consider the left as LSB.

{- Derivation:

-- C carry, A addend pair, R result

second unB'      :: C * As (S n) ~> C * (As n * As n)
lassocP          ::              ~> (C * As n) * As n
first (addTN n)  ::              ~> (Rs n * C) * As n
rassocP          ::              ~> Rs n * (C * As n)
second (addTN n) ::              ~> Rs n * (Rs n * C)
lassocP          ::              ~> (Rs n * Rs n) * C
first toB'       ::              ~> Rs (S n) * C

-}

{--------------------------------------------------------------------
    Miscellany. May remove later, or might prove useful.
--------------------------------------------------------------------}

tree :: (a -> b)
     -> (forall m. (IsNat m, S m ~ n) => Pair (T m a) -> b)
     -> (T n a -> b)
tree l _ (L a) = l a
tree _ b (B u) = b u

-- Fold for trees. How does it relate to the Foldable instance? We can easily
-- define fold or foldMap via foldT. What about conversely?
foldT :: forall a b n. (a -> b) -> (Pair b -> b) -> (T n a -> b)
foldT l b = foldT'
 where
   foldT' :: forall m. T m a -> b
   foldT' = tree l (b . fmap foldT')

-- foldT l b = tree l (b . fmap (foldT l b))

-- foldT l b = foldT'
--  where
--    foldT' :: T m a -> b
--    foldT' (L a) = l a
--    foldT' (B p) = b (foldT' <$> p)

retree :: (a -> b)
       -> (forall m. (IsNat m, S m ~ n) => Pair (T m a) -> Pair (T m b))
       -> (T n a -> T n b)
retree l _ (L a) = (L . l) a
retree _ b (B u) = (B . b) u

-- I'd rather say
--   retree l b = tree (L . l) (B . b)
-- but I get
--   Couldn't match type `S m' with `Z'

-- | Reverse a tree. Transform away later
reverseT :: Unop (T n a)
reverseT = retree id (inPair swapP . fmap reverseT)

-- Or
-- reverseT = retree id (fmap reverseT . swapP)

fromList :: IsNat n => [a] -> T n a
fromList = fromList' nat

fromList' :: Nat n -> [a] -> T n a
fromList' Zero     [a] = L a
fromList' Zero     _   = error "fromList': length mismatch"
fromList' (Succ n) as  = B (fromList' n <$> halves as)

halves :: [a] -> Pair [a]
halves as = toPair (splitAt (length as `div` 2) as)

