{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Misc
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Miscellany
----------------------------------------------------------------------

module Circat.Misc where

-- TODO: explicit exports

import Prelude hiding (id,(.))

-- import Data.Monoid (Monoid(..))
-- import Data.Traversable (Traversable(sequenceA))
import Control.Category (Category(..))
-- import Control.Applicative (Applicative)

import Unsafe.Coerce (unsafeCoerce)     -- see below

import GHC.Generics hiding (C)

import Control.Newtype
import Data.Proof.EQ ((:=:)(..))

import Control.Compose ((:.)(..))

-- import TypeUnary.Nat (Nat(..),natToZ)

-- | Unary transformation
type Unop a = a -> a

-- | Binary transformation
type Binop a = a -> Unop a

-- | Ternary transformation
type Ternop a = a -> Binop a

-- Sum & product type synonyms

infixl 7 :*
infixl 6 :+
infixr 1 :=>

type Unit  = ()

type (:*)  = (,)
type (:+)  = Either
type (:=>) = (->)

dup :: a -> (a,a)
dup a = (a,a)

infixr 3 `xor`

xor :: Binop Bool
xor = (/=)
{-# NOINLINE xor #-}

newtype Parity = Parity { getParity :: Bool }

instance Newtype Parity where
  type O Parity = Bool
  pack = Parity
  unpack (Parity x) = x

instance Monoid Parity where
  mempty = Parity False
  Parity a `mappend` Parity b = Parity (a `xor` b)

boolToInt :: Bool -> Int
boolToInt c = if c then 1 else 0
{-# INLINE boolToInt #-}

loop :: forall a b s. (a :* s -> b :* s) -> (a -> b)
loop f a = b where (b,s) = f (a,s)
{-# NOINLINE loop #-}

delay :: s -> (s -> s)
delay _ _ = error "There is no delay for functions. Sorry!"
{-# NOINLINE delay #-}

-- Note: with one or no "_", delay still gets inlined

-- Note: Circat re-introduces a 'boolToInt' circuit primitive.

inNew :: (Newtype n, Newtype n') =>
         (O n -> O n') -> (n -> n')
inNew = pack <~ unpack

inNew2 :: (Newtype n, Newtype n', Newtype n'') =>
          (O n -> O n' -> O n'') -> (n -> n' -> n'')
inNew2 = inNew <~ unpack

infixl 1 <~
infixr 1 ~>

-- | Add post- and pre-processing
(<~) :: Category cat =>
        (b `cat` b') -> (a' `cat` a) -> ((a `cat` b) -> (a' `cat` b'))
(h <~ f) g = h . g . f

-- | Add pre- and post-processing
(~>) :: Category cat =>
        (a' `cat` a) -> (b `cat` b') -> ((a `cat` b) -> (a' `cat` b'))
f ~> h = h <~ f

-- | Compose list of unary transformations
compose :: [Unop a] -> Unop a
compose = foldr (.) id

transpose :: (Traversable t, Applicative f) => t (f a) -> f (t a)
transpose = sequenceA

inTranspose :: (Applicative f, Traversable t, Applicative f', Traversable t')
            => (f (t a) -> t' (f' a)) -> (t (f a) -> f' (t' a))
inTranspose h = transpose . h . transpose

-- TODO: Maybe generalize the type of compose to Unop' (~>) a

class Reversible f where
  reverse :: f a -> f a
  -- Regrettable hack-around for single-method classes
  regrettable_hack_reverse :: f a
  regrettable_hack_reverse = undefined

instance Reversible [] where
  reverse = Prelude.reverse

-- TODO: Remove Reversible?

infix 4 ===, ==?

-- | Equality when we don't know that the types match. Important requirement:
-- when the result is True, then it must be that a and b are the same type.
-- See '(==?)'.
class Eq' a b where
  (===) :: a -> b -> Bool

-- TODO: Maybe make (==?) the method and drop (===), moving the type proofs into
-- the instances and using unsafeCoerce only where necessary. Experiment in a
-- new branch. Alternatively, make (===) and (==?) *both* be methods, with
-- defaults defined in terms of each other.

-- | Test for equality. If equal, generate a type equality proof. The proof
-- generation is done with @unsafeCoerce@, so it's very important that equal
-- terms really do have the same type.
(==?) :: Eq' a b => a -> b -> Maybe (a :=: b)
a ==? b | a === b   = unsafeCoerce (Just Refl)
        | otherwise = Nothing

{--------------------------------------------------------------------
    Evaluation
--------------------------------------------------------------------}

class Evalable e where
  type ValT e
  eval :: e -> ValT e

{--------------------------------------------------------------------
    Statically sized functors
--------------------------------------------------------------------}

-- TODO: Remove this code when I phase out the data types in circat (replaced by
-- shaped-types).

class Sized f where
  size :: f () -> Int -- ^ Argument is ignored at runtime
  -- Temporary hack to avoid newtype-like representation.
  sizeDummy :: f a
  sizeDummy = undefined

-- TODO: Switch from f () to f Void or Proxy

-- | Generic 'size'
genericSize :: (Generic1 f, Sized (Rep1 f)) => f () -> Int
genericSize = size . from1

-- The argument to size is unfortunate. When GHC Haskell has explicit type
-- application (<https://ghc.haskell.org/trac/ghc/wiki/TypeApplication>),
-- replace "size (undefined :: f ())" with "size @f".
-- Meanwhile, a macro helps.

#define tySize(f) (size (undefined :: (f) ()))

-- | Useful default for 'size'.
sizeAF :: forall f. (Applicative f, Foldable f) => f () -> Int
sizeAF = const (sum (pure 1 :: f Int))

instance Sized Par1 where
  size = const 1
  {-# INLINE size #-}

instance (Sized g, Sized f) => Sized (g :.: f) where
  size = const (tySize(g) * tySize(f))
  {-# INLINE size #-}

-- Phasing out, in favor of Generics version ((:.:))
instance (Sized g, Sized f) => Sized (g :. f) where
  size = const (tySize(g) * tySize(f))
  {-# INLINE size #-}

-- -- | @2 ^ n@
-- twoNat :: Integral m => Nat n -> m
-- twoNat n = 2 ^ (natToZ n :: Int)

-- | @'showsUnary' n d x@ produces the string representation of a unary data
-- constructor with name @n@ and argument @x@, in precedence context @d@.
showsUnary :: (Show a) => String -> Int -> a -> ShowS
showsUnary name d x = showParen (d > 10) $
    showString name . showChar ' ' . showsPrec 11 x

-- I swiped showsUnary from Data.Functor.Classes in transformers >= 0.4.0.0
