{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses #-}
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

import Control.Category (Category(..))
import Control.Applicative (Applicative)
import Data.Traversable (Traversable(sequenceA))

import Unsafe.Coerce (unsafeCoerce)     -- see below

import Control.Newtype
import Data.Proof.EQ ((:=:)(..))

dup :: a -> (a,a)
dup a = (a,a)

infixr 3 `xor`

xor :: Binop Bool
xor = (/=)
{-# NOINLINE xor #-}

boolToInt :: Bool -> Int
boolToInt c = if c then 1 else 0
{-# INLINE boolToInt #-}

-- Note: Circat re-introduces a 'boolToInt' circuit primitive.

-- | Unary transformation
type Unop a = a -> a

-- | Binary transformation
type Binop a = a -> Unop a

-- Sum & product type synonyms

infixl 7 :*
infixl 6 :+
infixr 1 :=>

type Unit  = ()

type (:*)  = (,)
type (:+)  = Either
type (:=>) = (->)

inNew :: (Newtype n o, Newtype n' o') =>
         (o -> o') -> (n -> n')
inNew = pack <~ unpack

inNew2 :: (Newtype n o, Newtype n' o', Newtype n'' o'') =>
          (o -> o' -> o'') -> (n -> n' -> n'')
inNew2 = inNew <~ unpack

infixl 1 <~

-- | Add post- and pre-processing
(<~) :: Category cat =>
        (b `cat` b') -> (a' `cat` a) -> ((a `cat` b) -> (a' `cat` b'))
(h <~ f) g = h . g . f

-- | Compose list of unary transformations
compose :: [Unop a] -> Unop a
compose = foldr (.) id

transpose :: (Traversable t, Applicative f) => t (f a) -> f (t a)
transpose = sequenceA

-- TODO: Maybe generalize the type of compose to Unop' (~>) a

class Reversible f where
  reverse :: f a -> f a
  -- Regrettable hack-around for single-method classes
  regrettable_hack_reverse :: f a
  regrettable_hack_reverse = undefined

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
