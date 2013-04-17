{-# LANGUAGE GADTs, KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables, Rank2Types #-}
{-# LANGUAGE TypeFamilies, TypeOperators #-}
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

import TypeUnary.Nat hiding ((:*:))

import Circat.Misc (Unop,(<~))
import Circat.Category
import Circat.Classes
import Circat.Pair -- (Pair(..),PairCat(..))

-- TODO: Use the generalization from numbers-vectors-trees, factoring out Pair

data T :: * -> * -> * where
  L :: a -> T Z a
  B :: IsNat n => Pair (T n a) -> T (S n) a

deriving instance Eq a => Eq (T n a)

class PairCat (~>) => TreeCat (~>) where
  toL :: a ~> T Z a
  unL :: T Z a ~> a
  toB :: IsNat n => Pair (T n a) ~> T (S n) a
  unB :: IsNat n => T (S n) a ~> Pair (T n a)

instance TreeCat (->) where
  toL a     = L a
  unL (L a) = a
  toB p     = (B p)
  unB (B p) = p

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

{--------------------------------------------------------------------
    Addition
--------------------------------------------------------------------}

type AddTP n = forall (~>). (ConstCat (~>), AddCat (~>), TreeCat (~>)) =>
               Adds (~>) (T n)

addTN :: Nat n -> AddTP n
addTN Zero     = second toL . fullAdd . first unL

addTN (Succ n) =
  second (toB.toPair) . rassocP . first (addTN n) . lassocP . second (addTN n) . rassocP . first (unPair.unB) 


{- Derivation:

-- C carry, A addend pair, R result

first (unPair.unB)  :: As (S n) :* C       :> (As n :* As n) :* C
rassocP             :: (As n :* As n) :* C :> As n :* (As n :* C)
second (addTN n)    :: As n :* (As n :* C) :> As n :* (C :* Rs n)
lassocP             :: As n :* (C :* Rs n) :> (As n :* C) :* Rs n
first (addTN n)     :: (As n :* C) :* Rs n :> (C :* Rs n) :* Rs n
rassocP             :: (C :* Rs n) :* Rs n :> C :* (Rs n :* Rs n)
second (toB.toPair) :: C :* (Rs n :* Rs n) :> C :* Rs (S n)

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

