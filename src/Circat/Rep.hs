{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-} -- experiment
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Rep
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Convert to and from standard representations
----------------------------------------------------------------------

module Circat.Rep (Rep,HasRep(..),abst',repr',bottom) where

import Data.Monoid
import Data.Newtypes.PrettyDouble
import Control.Applicative (WrappedMonad(..))

import Control.Monad.Trans.State (StateT(..))
import Data.Functor.Identity (Identity(..))
-- TODO: more

-- import Data.Constraint

import Circat.Misc ((:*),(:+),Parity(..))
import TypeUnary.TyNat (Z,S)
import TypeUnary.Nat (Nat(..),IsNat(..))
import TypeUnary.Vec (Vec(..))

type family Rep a

-- | Convert to and from standard representations. Used for transforming case
-- expression scrutinees and constructor applications. The 'repr' method should
-- convert to a standard representation (unit, products, sums), or closer to
-- such a representation, via another type with a 'HasRep' instance. The 'abst'
-- method should reveal a constructor so that we can perform the
-- case-of-known-constructor transformation.
class HasRep a where
  repr :: Rep a ~ a' => a -> a'
  abst :: Rep a ~ a' => a' -> a

-- Note types:
-- 
--   repr :: forall a. HasRep a => forall a'. Rep a ~ a' => a -> a'
--   abst :: forall a. HasRep a => forall a'. Rep a ~ a' => a' -> a
-- 
-- Note: Using Rep a ~ a' rather than the reverse to make the calls a little
-- easier to construct (using normaliseType and no mkSymCo).

-- -- Identity as @'abst' . 'repr'@.
-- abstRepr :: HasRep a => a -> a
-- abstRepr = abst . repr

-- Non-inlinable 'repr'
repr' :: forall a. HasRep a => forall a'. Rep a ~ a' => a -> a'
repr' = repr
{-# NOINLINE repr' #-}

-- Non-inlinable 'abst'
abst' :: forall a. HasRep a => forall a'. Rep a ~ a' => a' -> a
abst' = abst
{-# NOINLINE abst' #-}

-- TODO: Move repr' and abst' to the compiler, since they're about controlling
-- inlining etc.

type instance Rep (a,b,c) = ((a,b),c)
instance HasRep (a,b,c) where
  repr (a,b,c) = ((a,b),c)
  abst ((a,b),c) = (a,b,c)

type instance Rep (a,b,c,d) = ((a,b),(c,d))
instance HasRep (a,b,c,d) where
  repr (a,b,c,d) = ((a,b),(c,d))
  abst ((a,b),(c,d)) = (a,b,c,d)

type instance Rep (Vec Z a) = ()
instance HasRep (Vec Z a) where
  repr ZVec = ()
  abst () = ZVec

type instance Rep (Vec (S n) a) = (a,Vec n a)
instance HasRep (Vec (S n) a) where
  repr (a :< as) = (a, as)
  abst (a, as) = (a :< as)

#define WrapRep(abstT,reprT,con) \
type instance Rep (abstT) = reprT; \
instance HasRep (abstT) where { repr (con a) = a ; abst a = con a }

WrapRep(Sum a,a,Sum)
WrapRep(PrettyDouble,Double,PrettyDouble)
WrapRep(Product a,a,Product)
WrapRep(All,Bool,All)
WrapRep(Any,Bool,Any)
WrapRep(Dual a,a,Dual)
WrapRep(Endo a,a->a,Endo)
WrapRep(WrappedMonad m a,m a,WrapMonad)
WrapRep(Identity a,a,Identity)
WrapRep(StateT s m a, s -> m (a,s), StateT)

WrapRep(Parity,Bool,Parity)

-- TODO: Generate these dictionaries on the fly during compilation, so we won't
-- have to list them here.

type instance Rep (Nat Z) = ()
instance HasRep (Nat Z) where
  repr Zero = ()
  abst () = Zero

type instance Rep (Nat (S n)) = () :* Nat n
instance IsNat n => HasRep (Nat (S n)) where
  repr (Succ n) = ((),n)
  abst ((),n) = Succ n
-- The IsNat constraint comes from Succ.
-- TODO: See about eliminating that constructor constraint.

-- Experimental treatment of Maybe
type instance Rep (Maybe a) = Bool :* a
instance HasRep (Maybe a) where
  repr (Just a) = (True,a)
  repr Nothing  = (False,bottom)
  abst (True,a ) = Just a
  abst (False,_) = Nothing 

bottom :: a
bottom = error "bottom: Bottom!"
{-# NOINLINE bottom #-}

-- TODO: LambdaCCC.Prim has an BottomP primitive. If the error ever occurs, add
-- a string argument and tweak the reification.

-- Generalize Maybe to sums:

type instance Rep (a :+ b) = Bool :* (a :* b)
instance HasRep (a :+ b) where
  repr (Left  a) = (False,(a,bottom)) -- error "repr on Maybe: undefined value"
  repr (Right b) = (True,(bottom,b))
  abst (False,(a,_)) = Left  a
  abst (True ,(_,b)) = Right b

-- -- TODO: Redefine `Maybe` representation as sum:
-- 
-- type instance Rep (Maybe a) = Unit :+ a
-- ...
