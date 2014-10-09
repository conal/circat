{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, ViewPatterns, PatternGuards, CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE UndecidableInstances #-} -- see below

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=35 #-}  -- for N32

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Prim
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Primitives
----------------------------------------------------------------------

module Circat.Prim
  ( Lit(..), HasLit(..), litSS
  , Prim(..),litP -- ,xor,cond,ifThenElse
  , primArrow
  , PrimBasics(..), EvalableP(..)
  ) where

-- #define LitSources

import Prelude hiding (id,(.),curry,uncurry)

-- import Control.Arrow ((&&&))
import Data.Constraint (Dict(..))

import Circat.Category
import Circat.Classes (BoolCat(..),IfCat(..),NumCat(..),BottomCat(..))

import Circat.Circuit (GenBuses,(:>)
#ifdef LitSources
                      , litUnit,litBool,litInt
#else
                      , constC
#endif
                      )

-- import TypeEncode.Encode (EncodeCat(..))

-- TODO: sort out the two uses of xor and simplify the Circat.Classes imports
-- and uses.

import Circat.Misc
import Circat.ShowUtils (Show'(..))

{--------------------------------------------------------------------
    Literals
--------------------------------------------------------------------}

-- | Literals
data Lit :: * -> * where
  UnitL  :: Unit -> Lit Unit
  BoolL  :: Bool -> Lit Bool
  IntL   :: Int  -> Lit Int

-- The Unit argument is just for uniformity

instance Eq' (Lit a) (Lit b) where
  UnitL x === UnitL y = x == y
  BoolL x === BoolL y = x == y
  IntL  x === IntL  y = x == y
  _       === _       = False

instance Eq (Lit a) where (==) = (===)

-- | Convenient 'Lit' construction
class HasLit a where toLit :: a -> Lit a

instance HasLit Unit where toLit = UnitL
instance HasLit Bool where toLit = BoolL
instance HasLit Int  where toLit = IntL

-- TODO: Do I still need this stuff?

-- Proofs

litHasShow :: Lit a -> Dict (Show a)
litHasShow (UnitL _) = Dict
litHasShow (BoolL _) = Dict
litHasShow (IntL  _) = Dict

#define LSh (litHasShow -> Dict)

-- instance Show (Lit a) where
--   showsPrec p UnitL     = showsPrec p ()
--   showsPrec p (BoolL b) = showsPrec p b
--   showsPrec p (IntL  b) = showsPrec p b

instance Show (Lit a) where
  showsPrec p l@LSh = showsPrec p (eval l)

litGenBuses :: Lit a -> Dict (GenBuses a)
litGenBuses (UnitL _) = Dict
litGenBuses (BoolL _) = Dict
litGenBuses (IntL  _) = Dict

#define LSo (litGenBuses -> Dict)

litSS :: Lit a -> Dict (Show a, GenBuses a)
litSS l | (Dict,Dict) <- (litHasShow l,litGenBuses l) = Dict

#define LS (litSS -> Dict)

instance Evalable (Lit a) where
  type ValT (Lit a) = a
  eval (UnitL x) = x
  eval (BoolL x) = x
  eval (IntL  x) = x

instance HasUnitArrow (->) Lit where
  unitArrow x = const (eval x)

instance HasUnitArrow (:>) Lit where
#ifdef LitSources
  unitArrow (UnitL x) = litUnit x
  unitArrow (BoolL x) = litBool x
  unitArrow (IntL  x) = litInt  x
#else
  unitArrow l@LS = constC (eval l)
#endif

{--------------------------------------------------------------------
    Primitives
--------------------------------------------------------------------}

-- | Primitives
data Prim :: * -> * where
  LitP          :: Lit a -> Prim a
  NotP          :: Prim (Bool -> Bool)
  AndP,OrP,XorP :: Prim (Bool -> Bool -> Bool)
  AddP,MulP     :: Prim (Int -> Int -> Int)
  ExlP          :: Prim (a :* b -> a)
  ExrP          :: Prim (a :* b -> b)
  InlP          :: Prim (a -> a :+ b)
  InrP          :: Prim (b -> a :+ b)
  PairP         :: Prim (a -> b -> a :* b)
#if 0
  CondBP        :: Prim (Bool :* (Bool :* Bool) -> Bool)  -- mux on Bool
  CondIP        :: Prim (Bool :* (Int  :* Int ) -> Int )  -- mux on Int
#else
  IfP           :: IfCat (:>) a => Prim (Bool :* (a :* a) -> a)
#endif
  AbstP         :: (HasRep a, Rep a ~ a') => Prim (a' -> a)
  ReprP         :: (HasRep a, Rep a ~ a') => Prim (a -> a')
  BottomP       :: BottomCat (:>) a => Prim (Unit -> a)

instance Eq' (Prim a) (Prim b) where
  LitP a    === LitP b    = a === b
  NotP      === NotP      = True
  AndP      === AndP      = True
  OrP       === OrP       = True
  XorP      === XorP      = True
  AddP      === AddP      = True
  MulP      === MulP      = True
  ExlP      === ExlP      = True
  ExrP      === ExrP      = True
  InlP      === InlP      = True
  InrP      === InrP      = True
  PairP     === PairP     = True
#if 0
  CondBP    === CondBP    = True
  CondIP    === CondIP    = True
#else
  IfP       === IfP       = True
#endif
  AbstP     === AbstP     = True
  ReprP     === ReprP     = True
  BottomP   === BottomP   = True
  _         === _         = False

instance Eq (Prim a) where (==) = (===)

instance Show (Prim a) where
  showsPrec p (LitP a)   = showsPrec p a
  showsPrec _ NotP       = showString "not"
  showsPrec _ AndP       = showString "(&&)"
  showsPrec _ OrP        = showString "(||)"
  showsPrec _ XorP       = showString "xor"
  showsPrec _ AddP       = showString "add"
  showsPrec _ MulP       = showString "mul"
  showsPrec _ ExlP       = showString "exl"
  showsPrec _ InlP       = showString "Left"
  showsPrec _ InrP       = showString "Right"
  showsPrec _ ExrP       = showString "exr"
  showsPrec _ PairP      = showString "(,)"
#if 0
  showsPrec _ CondBP     = showString "muxB"
  showsPrec _ CondIP     = showString "muxI"
#else
  showsPrec _ IfP        = showString "ifC"
#endif
  showsPrec _ AbstP      = showString "abst"
  showsPrec _ ReprP      = showString "repr"
  showsPrec _ BottomP    = showString "bottomC"

instance Show' Prim where showsPrec' = showsPrec

primArrow :: Prim (a :=> b) -> (a :> b)
primArrow NotP      = notC
primArrow AndP      = curry andC
primArrow OrP       = curry orC
primArrow XorP      = curry xorC
primArrow AddP      = curry add
primArrow MulP      = curry mul
primArrow ExlP      = exl
primArrow ExrP      = exr
primArrow InlP      = inl
primArrow InrP      = inr
primArrow PairP     = curry id
#if 0
primArrow CondBP    = muxB
primArrow CondIP    = muxI
#else
primArrow IfP       = ifC
#endif
primArrow AbstP     = abstC
primArrow ReprP     = reprC
primArrow BottomP   = -- bottomC
                      error "primArrow: BottomP"
primArrow (LitP _)  = error ("primArrow: LitP with function type?!")

instance -- (ClosedCat k, CoproductCat k, BoolCat k, NumCat k Int, RepCat k)
         (k ~ (:>))
      => HasUnitArrow k Prim where
  unitArrow NotP      = unitFun notC
  unitArrow AndP      = unitFun (curry andC)
  unitArrow OrP       = unitFun (curry orC)
  unitArrow XorP      = unitFun (curry xorC)
  unitArrow AddP      = unitFun (curry add)
  unitArrow MulP      = unitFun (curry mul)
  unitArrow ExlP      = unitFun exl
  unitArrow ExrP      = unitFun exr
  unitArrow InlP      = unitFun inl
  unitArrow InrP      = unitFun inr
  unitArrow PairP     = unitFun (curry id)
#if 0
  unitArrow CondBP    = unitFun muxB
  unitArrow CondIP    = unitFun muxI
#else
  unitArrow IfP       = unitFun ifC
#endif
  unitArrow AbstP     = unitFun abstC
  unitArrow ReprP     = unitFun reprC
  unitArrow BottomP   = -- bottomC
                        unitFun bottomC
                        -- error "unitArrow on Prim: BottomP"
  unitArrow (LitP l)  = unitArrow l

--     Variable `k' occurs more often than in the instance head
--       in the constraint: BiCCC k
--     (Use -XUndecidableInstances to permit this)

instance Evalable (Prim a) where
  type ValT (Prim a) = a
  eval (LitP l)      = eval l
  eval NotP          = not
  eval AndP          = (&&)
  eval OrP           = (||)
  eval XorP          = xor
  eval AddP          = (+)
  eval MulP          = (*)
  eval ExlP          = fst
  eval ExrP          = snd
  eval InlP          = Left
  eval InrP          = Right
  eval PairP         = (,)
#if 0
  eval CondBP        = muxB
  eval CondIP        = muxI
#else
  eval IfP           = ifC
#endif
  eval AbstP         = abstC
  eval ReprP         = reprC
  eval BottomP       = error "eval on Prim: Bottom!"

-- TODO: replace fst with exl, etc.

-- TODO: Split LitP out of Prim, and make Prim have domain and range. Then
-- revisit 'HasConstArrow', and implement Evalable (Prim a b) homomorphically.
-- See convertP in LambdaCCC.CCC.

litP :: HasLit a => a -> Prim a
litP = LitP . toLit

{--------------------------------------------------------------------
    Some prim classes. Move later.
--------------------------------------------------------------------}

class PrimBasics p where
  unitP :: p Unit
  pairP :: p (a :=> b :=> a :* b)

instance PrimBasics Prim where
  unitP = LitP (UnitL ())
  pairP = PairP

class EvalableP p where evalP :: p a -> a

instance EvalableP Prim where evalP = eval
