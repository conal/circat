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

module Circat.Rep (HasRep(..)) where

import Data.Monoid
-- import Data.Newtypes.PrettyDouble
import Control.Applicative (WrappedMonad(..))
import qualified GHC.Generics as G

import Control.Monad.Trans.State (StateT(..))
import Data.Functor.Identity (Identity(..))
-- TODO: more

import Circat.Complex

-- import Data.Constraint

-- TODO: Eliminate most of the following when I drop these types.
import Circat.Misc ((:*),(:+),Parity(..))
import TypeUnary.TyNat (Z,S)
import TypeUnary.Nat (Nat(..),IsNat(..))
import TypeUnary.Vec (Vec(..))

-- | Convert to and from standard representations. Used for transforming case
-- expression scrutinees and constructor applications. The 'repr' method should
-- convert to a standard representation (unit, products, sums), or closer to
-- such a representation, via another type with a 'HasRep' instance. The 'abst'
-- method should reveal a constructor so that we can perform the
-- case-of-known-constructor transformation.

class HasRep a where
  type Rep a
  repr :: a -> Rep a
  abst :: Rep a -> a

-- -- Identity as @'abst' . 'repr'@.
-- abstRepr :: HasRep a => a -> a
-- abstRepr = abst . repr

instance HasRep (a,b,c) where
  type Rep (a,b,c) = ((a,b),c)
  repr (a,b,c) = ((a,b),c)
  abst ((a,b),c) = (a,b,c)

instance HasRep (a,b,c,d) where
  type Rep (a,b,c,d) = ((a,b),(c,d))
  repr (a,b,c,d) = ((a,b),(c,d))
  abst ((a,b),(c,d)) = (a,b,c,d)

instance HasRep (Vec Z a) where
  type Rep (Vec Z a) = ()
  repr ZVec = ()
  abst () = ZVec

instance HasRep (Vec (S n) a) where
  type Rep (Vec (S n) a) = (a,Vec n a)
  repr (a :< as) = (a, as)
  abst (a, as) = (a :< as)

#define WrapRep(abstT,reprT,con) \
instance HasRep (abstT) where { type Rep (abstT) = reprT; repr (con a) = a ; abst a = con a }

WrapRep(Sum a,a,Sum)
-- WrapRep(PrettyDouble,Double,PrettyDouble)
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

instance HasRep (Nat Z) where
  type Rep (Nat Z) = ()
  repr Zero = ()
  abst () = Zero

instance IsNat n => HasRep (Nat (S n)) where
  type Rep (Nat (S n)) = () :* Nat n
  repr (Succ n) = ((),n)
  abst ((),n) = Succ n
-- The IsNat constraint comes from Succ.
-- TODO: See about eliminating that constructor constraint.

-- Experimental treatment of Maybe
instance HasRep (Maybe a) where
  type Rep (Maybe a) = Bool :* a
  repr (Just a) = (True,a)
  repr Nothing  = (False,undefined)
  abst (True,a ) = Just a
  abst (False,_) = Nothing 

-- TODO: LambdaCCC.Prim has an BottomP primitive. If the error ever occurs,
-- replace with ErrorP (taking a string argument) and tweak the reification.

-- Generalize Maybe to sums:

instance HasRep (a :+ b) where
  type Rep (a :+ b) = Bool :* (a :* b)
  repr (Left  a) = (False,(a,undefined)) -- error "repr on Maybe: undefined value"
  repr (Right b) = (True,(undefined,b))
  abst (False,(a,_)) = Left  a
  abst (True ,(_,b)) = Right b

-- -- TODO: Redefine `Maybe` representation as sum:
-- 
-- type instance Rep (Maybe a) = Unit :+ a
-- ...

instance HasRep (Complex a) where
  type Rep (Complex a) = a :* a
  repr (a :+ a') = (a,a')
  abst (a,a') = (a :+ a')

instance HasRep (G.U1 p) where
  type Rep (G.U1 p) = ()
  repr G.U1 = ()
  abst () = G.U1

instance HasRep (G.Par1 p) where
  type Rep (G.Par1 p) = p
  repr = G.unPar1
  abst = G.Par1

instance HasRep (G.K1 i c p) where
  type Rep (G.K1 i c p) = c
  repr = G.unK1
  abst = G.K1

instance HasRep (G.M1 i c f p) where
  type Rep (G.M1 i c f p) = f p
  repr = G.unM1
  abst = G.M1

instance HasRep ((G.:+:) f g p) where
  type Rep ((G.:+:) f g p) = f p :+ g p
  repr (G.L1 x) = Left  x
  repr (G.R1 x) = Right x
  abst = either G.L1 G.R1

instance HasRep ((G.:*:) f g p) where
  type Rep ((G.:*:) f g p) = f p :* g p
  repr (x G.:*: y) = (x,y)
  abst (x,y) = (x G.:*: y)

instance HasRep ((G.:.:) f g p) where
  type Rep ((G.:.:) f g p) = f (g p)
  repr = G.unComp1
  abst = G.Comp1

-- TODO: Can I *replace* HasRep with Generic?
