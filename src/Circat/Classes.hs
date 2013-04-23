{-# LANGUAGE TypeOperators, TypeFamilies, ConstraintKinds, GADTs #-}
{-# LANGUAGE Rank2Types, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
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
import Circat.State -- (StateCat(..),pureState,StateFun)

-- | Category with boolean operations.
class ProductCat (~>) => BoolCat (~>) where
  not :: Bool ~> Bool
  and, or, xor :: (Bool :* Bool) ~> Bool

-- The Category superclass is just for convenience.

instance BoolCat (->) where
  not = P.not
  and = P.uncurry (&&)
  or  = P.uncurry (||)
  xor = P.uncurry (/=)

class BoolCat (~>) => EqCat (~>) where
  type EqKon (~>) a :: Constraint
  type EqKon (~>) a = Yes a
  eq, neq :: (Eq a, EqKon (~>) a) => (a :* a) ~> Bool
  neq = not . eq

-- TODO: Revisit the type constraints for EqCat.

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

instance VecCat (~>) => VecCat (StateFun (~>) s) where
  toVecZ = pureState toVecZ
  unVecZ = pureState unVecZ
  toVecS = pureState toVecS
  unVecS = pureState unVecS

instance (ClosedCatWith (~>) s, VecCat (~>)) => VecCat (StateExp (~>) s) where
  toVecZ = pureState toVecZ
  unVecZ = pureState unVecZ
  toVecS = pureState toVecS
  unVecS = pureState unVecS

class (PairCat (~>), BoolCat (~>)) => AddCat (~>) where
  -- | Half adder: addends in; sum and carry out. Default via logic.
  halfAdd :: (Bool :* Bool) ~> (Bool :* Bool)
  halfAdd = xor &&& and
  -- | Full adder: carry and addend pairs in; sum and carry out.
  -- Default via 'halfAdd'.
  fullAdd :: (Bool :* Pair Bool) ~> (Bool :* Bool)
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
  (Bool :* f (Pair (Bool))) ~> (f (Bool) :* Bool)

class AddCat (~>) => AddsCat (~>) f where
  adds :: Adds (~>) f

type AddK (~>) = (ConstUCat (~>) (Vec Z (Bool)), AddCat (~>), VecCat (~>))

instance (AddK (~>), IsNat n) => AddsCat (~>) (Vec n) where
  adds = addVN nat

-- Illegal irreducible constraint ConstKon (~>) () in superclass/instance head
-- context (Use -XUndecidableInstances to permit this)

type AddVP n = forall (~>). AddK (~>) => Adds (~>) (Vec n)

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

-- TODO: Do I really need CTraversableKon, or can I make (~>) into an argument?
-- Try, and rename "CTraversable" to "TraversableCat". The Kon becomes superclass constraints.

class CTraversable t where
  type CTraversableKon t (~>) :: Constraint
  type CTraversableKon t (~>) = () ~ () -- or just (), if it works
  traverseC :: CTraversableKon t (~>) => (a ~> b) -> (t a ~> t b)

type CTraversableWith t (~>) = (CTraversable t, CTraversableKon t (~>))

instance CTraversable (Vec Z) where
  type CTraversableKon (Vec Z) (~>) = VecCat (~>)
  traverseC _ = reVecZ

instance CTraversable (Vec n) => CTraversable (Vec (S n)) where
  type CTraversableKon (Vec (S n)) (~>) =
    (VecCat (~>), CTraversableKon (Vec n) (~>))
  traverseC f = inVecS (f *** traverseC f)

instance CTraversable Pair where
  type CTraversableKon Pair (~>) = PairCat (~>)
  traverseC f = inPair (f *** f)

-- TODO: Maybe move Vec support to a new Vec module, alongside the RTree module.

traverseCurry :: 
  ( ConstUCat (~>) (t b), CTraversableWith t (~>), StrongCat (~>) t
    , StrongKon (~>) t a b ) =>
  t b -> ((a :* b) ~> c) -> (a ~> t c)
traverseCurry q h = traverseC h . lstrength . rconst q

{- Derivation:

q :: t b
h :: a :* b :> c

rconst q    :: a          ~> (a :* t b)
lstrength   :: a :* t b   ~> t (a :* b)
traverseC h :: t (a :* b) ~> t c

traverse h . lstrength . rconst idTrie :: a ~> t c

-}

-- Special case. To remove.

-- trieCurry :: ( HasTrie b, StrongCat (~>) (Trie b)
--              , CTraversableWith (Trie b) (~>)
--              , UnitCat (~>), ConstUCat (~>) (b :->: b) ) =>
--              ((a :* b) ~> c) -> (a ~> (b :->: c))
-- trieCurry = traverseCurry idTrie

-- TODO: Move CTraversable and trieCurry to Category.


{--------------------------------------------------------------------
    Addition via state and traversal
--------------------------------------------------------------------}

type AddState (~~>) =
  (StateCat (~~>), StateKon (~~>), StateT (~~>) ~ Bool, AddCat (StateBase(~~>)))

-- Simpler but exposes (~>):
-- 
--   type AddState (~~>) (~>) b =
--     (StateCatWith (~~>) (~>) b, AddCat (~>), b ~ Bool)

-- | Full adder with 'StateCat' interface
fullAddS :: AddState (~~>) => Pair Bool ~~> Bool
fullAddS = state fullAdd

-- | Structure adder with 'StateCat' interface
addS :: (AddState (~~>), CTraversableWith f (~~>)) =>
        f (Pair Bool) ~~> f Bool
addS = traverseC fullAddS

-- TODO: Rewrite halfAdd & fullAdd via StateCat. Hopefully much simpler.
