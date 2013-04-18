{-# LANGUAGE TypeOperators, TypeFamilies, ConstraintKinds, GADTs #-}
{-# LANGUAGE Rank2Types, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-} -- see below

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Classes
-- Copyright   :  (c) 2013 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Additional type classes for circuit-friendly operations
----------------------------------------------------------------------

module Circat.Classes where

-- TODO: explicit exports

import Prelude hiding (id,(.),const,not,and,or,fst,snd)
import qualified Prelude as P
import Control.Arrow (arr,Kleisli)

import GHC.Prim (Constraint)

import TypeUnary.Vec (Vec(..),Z,S,Nat(..),IsNat(..))

import Circat.Misc ((:*),(<~))
import Circat.Category -- (Category(..),ProductCat(..),inRassocP,UnitCat(..))
import Circat.Pair
import Circat.State (StateCat(..),pureState,FState)

-- | Category with boolean operations.
-- The 'ProductCat' superclass is just for convenient use.
class ProductCat (~>) => BoolCat (~>) where
  type BoolT (~>)
  not :: BoolT (~>) ~> BoolT (~>)
  and, or, xor :: (BoolT (~>) :* BoolT (~>)) ~> BoolT (~>)

-- | Convenient notational alternative
type BCat (~>) b = (BoolCat (~>), b ~ BoolT (~>))

-- The Category superclass is just for convenience.

instance BoolCat (->) where
  type BoolT (->) = Bool
  not = P.not
  and = P.uncurry (&&)
  or  = P.uncurry (||)
  xor = P.uncurry (/=)

class BoolCat (~>) => EqCat (~>) where
  type EqKon (~>) a :: Constraint
  type EqKon (~>) a = Yes a
  eq, neq :: (Eq a, EqKon (~>) a) => (a :* a) ~> BoolT (~>)
  neq = not . eq

-- TODO: Revisit the type constraints for EqCat.

-- | Convenient notational alternative
type ECat (~>) b = (EqCat (~>), b ~ BoolT (~>))

instance EqCat (->) where
  type EqKon (->) a = Yes a
  eq  = P.uncurry (==)
  neq = P.uncurry (/=)

class (UnitCat (~>), ProductCat (~>)) => VecCat (~>) where
  toVecZ :: () ~> Vec Z a
  unVecZ :: Vec Z a ~> ()
  toVecS :: (a :* Vec n a) ~> Vec (S n) a
  unVecS :: Vec (S n) a ~> (a :* Vec n a)

reVecZ :: VecCat (~>) => Vec Z a ~> Vec Z b
reVecZ = toVecZ . unVecZ

inVecS :: VecCat (~>) =>
          ((a :* Vec m a) ~> (b :* Vec n b))
       -> (Vec  (S m)  a ~> Vec  (S n)   b)
inVecS = toVecS <~ unVecS

instance VecCat (->) where
  toVecZ ()        = ZVec
  unVecZ ZVec      = ()
  toVecS (a,as)    = a :< as
  unVecS (a :< as) = (a,as)

instance Monad m => VecCat (Kleisli m) where
  toVecZ = arr toVecZ
  unVecZ = arr unVecZ
  toVecS = arr toVecS
  unVecS = arr unVecS

instance VecCat (~>) => VecCat (FState (~>) s) where
  toVecZ = pureState toVecZ
  unVecZ = pureState unVecZ
  toVecS = pureState toVecS
  unVecS = pureState unVecS

class (PairCat (~>), BoolCat (~>)) => AddCat (~>) where
  -- | Half adder: addends in; sum and carry out. Default via logic.
  halfAdd :: b ~ BoolT (~>) => (b :* b) ~> (b :* b)
  halfAdd = xor &&& and
  -- | Full adder: carry and addend pairs in; sum and carry out.
  -- Default via 'halfAdd'.
  fullAdd :: b ~ BoolT (~>) => (b :* Pair b) ~> (b :* b)
  fullAdd = second or . inLassocP (first halfAdd) . second (halfAdd . unPair)

{-

second (halfAdd.unPair) :: C * A       -> C * (C * S)
lassocP                 :: C * (S * C) -> (C * S) * C
first halfAdd           :: (C * S) * C -> (S * C) * C
rassocP                 :: (S * C) * C -> S * (C * C)
second or               :: S * (C * C) -> S * C

-}

instance AddCat (->)  -- use defaults

-- Structure addition with carry in & out

type Adds (~>) f = 
  (BoolT (~>) :* f (Pair (BoolT (~>)))) ~> (f (BoolT (~>)) :* BoolT (~>))

class AddCat (~>) => AddsCat (~>) f where
  adds :: Adds (~>) f

instance (ConstUCat (~>), AddCat (~>), VecCat (~>), IsNat n)
      => AddsCat (~>) (Vec n) where
  adds = addVN nat

-- Illegal irreducible constraint ConstKon (~>) ()
-- in superclass/instance head context (Use -XUndecidableInstances to permit this)

type AddVP n = forall (~>).
  (ConstUCat (~>), AddCat (~>), VecCat (~>)) =>
  Adds (~>) (Vec n)

addVN :: Nat n -> AddVP n
addVN Zero     = lconst ZVec . fst

addVN (Succ n) = first toVecS . lassocP . second (addVN n)
               . rassocP . first fullAdd . lassocP
               . second unVecS

{- Derivation:

-- C carry, A addend pair, R result

second unVecS    :: C :* As (S n) ~> C :* (A :* As n)
lassocP          ::               ~> (C :* A) :* As n
first fullAdd    ::               ~> (S :* C) :* As n
rassocP          ::               ~> S :* (C :* As n)
second (addVN n) ::               ~> S :* (Rs n :* C)
lassocP          ::               ~> (S :* Rs n) :* C
first toVecS     ::               ~> Rs (S n) :* C

-}

class CTraversable t where
  type CTraversableKon t (~>) :: Constraint
  type CTraversableKon t (~>) = () ~ () -- or just (), if it works
  traverseC :: CTraversableKon t (~>) => (a ~> b) -> (t a ~> t b)

instance CTraversable Pair where
  type CTraversableKon Pair (~>) = PairCat (~>)
  traverseC f = inPair (f *** f)

instance CTraversable (Vec Z) where
  type CTraversableKon (Vec Z) (~>) = VecCat (~>)
  traverseC _ = reVecZ

instance CTraversable (Vec n) => CTraversable (Vec (S n)) where
  type CTraversableKon (Vec (S n)) (~>) =
    (VecCat (~>), CTraversableKon (Vec n) (~>))
  traverseC f = inVecS (f *** traverseC f)

-- TODO: Move Vec support to a new Vec module, alongside the RTree module.

{--------------------------------------------------------------------
    Addition via state and traversal
--------------------------------------------------------------------}

-- | Full adder with 'StateCat' interface
fullAddS :: (AddCat ar, b ~ BoolT ar, StateCat st ar) => st ar b (Pair b) b
fullAddS = state fullAdd

-- | Structure adder with 'StateCat' interface
addS :: (AddCat (~>), b ~ BoolT (~>), StateCat st (~>), (~~>) ~ st (~>) b) =>
        (CTraversable f, CTraversableKon f (~~>)) =>
        f (Pair b) ~~> f b
addS = traverseC fullAddS
