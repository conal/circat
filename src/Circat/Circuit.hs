{-# LANGUAGE CPP #-}

-- #define NoOptimizeCircuit

-- #define NoIfBotOpt
-- #define NoIdempotence
-- #define NoHashCons

-- #define MealyToArrow

{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification, TypeSynonymInstances, GADTs #-}
{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-} -- see below
-- {-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-} -- for LU & BU
{-# LANGUAGE PatternSynonyms #-}

-- For Church sum experiment
{-# LANGUAGE LiberalTypeSynonyms, ImpredicativeTypes #-}
{-# LANGUAGE ViewPatterns, TupleSections, EmptyDataDecls #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=36 #-} -- for add

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Circuit
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Circuit representation
----------------------------------------------------------------------

#define NoSums
-- #define StaticSums
-- #define TaggedSums
-- #define ChurchSums

module Circat.Circuit
  ( CircuitM, (:>)
  , PinId, Width, Bus(..), Source(..)
  , GenBuses(..), genBusesRep', delayCRep, tyRep, bottomRep, unDelayName
  , namedC, constS, constC
--   , litUnit, litBool, litInt
  -- , (|||*), fromBool, toBool
  , CompS(..), compNum, compName, compIns, compOuts
  , CompNum, DGraph, circuitGraph, outGWith, outG, Attr
  , UU, outDotG, mkGraph,Name,Report
  , simpleComp, tagged
  , systemSuccess
  , unitize
  , MealyC(..)
  , mealyAsArrow  -- Warning: <<loop>>
  , unitizeMealyC
  ) where

import Prelude hiding (id,(.),curry,uncurry,sequence)
-- import qualified Prelude as P

import Data.Monoid (mempty,(<>),Sum,Product)
import Data.Functor ((<$>))
import Control.Applicative (Applicative(..),liftA2)
import Control.Arrow (arr,Kleisli(..),loop)
import Data.Foldable (foldMap,toList)
-- import Data.Typeable                    -- TODO: imports
import Data.Tuple (swap)
import Data.Function (on)
import Data.Maybe (fromMaybe)
import Data.List (intercalate,group,sort,stripPrefix)
#ifndef MealyToArrow
import Data.List (partition)
#endif
import Data.Map (Map)
import qualified Data.Map as M
-- import Data.Set (Set)
import qualified Data.Set as S
import Data.Sequence (Seq,singleton)
import Text.Printf (printf)
-- import Debug.Trace (trace)
-- import Data.Coerce                      -- TODO: imports
#if !defined NoHashCons
import Unsafe.Coerce -- experiment
#endif

import qualified System.Info as SI
import System.Process (system) -- ,readProcess
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode(ExitSuccess))

-- mtl
import Control.Monad.State (State,execState,runState)
import qualified Control.Monad.State as Mtl

import TypeUnary.Vec hiding (get)

import Circat.Misc (Unit,(:*),(<~),Unop,Binop)
import Circat.Category
import Circat.Classes
import Circat.Pair
import qualified Circat.RTree as RTree
import qualified Circat.LTree as LTree
import Circat.RaggedTree (TU(..))
import qualified Circat.RaggedTree as Rag

{--------------------------------------------------------------------
    Buses
--------------------------------------------------------------------}

newtype PinId = PinId Int deriving (Eq,Ord,Show,Enum)
type PinSupply = [PinId]

-- TODO: Maybe stop using the name "pin", since it's a bus.

-- undefinedPinId :: PinId
-- undefinedPinId = PinId (-1)

-- | Bus width
type Width = Int

-- Data bus: Id, bit width, prim name, arguments, output index
data Bus = Bus PinId Width

-- undefinedBus :: Width -> Bus
-- undefinedBus = Bus undefinedPinId

-- | An information source: its bus and a description of its construction, which
-- contains the primitive, argument sources, and which output of that
-- application (usually 0th).

type Sources = [Source]

data Source = Source Bus PrimName Sources Int

-- undefinedSource :: Width -> Source
-- undefinedSource w = Source (undefinedBus w) "undefined" [] 0

sourceBus :: Source -> Bus
sourceBus (Source b _ _ _) = b

busId :: Bus -> PinId
busId (Bus i _) = i

sourceId :: Source -> PinId
sourceId = busId . sourceBus

instance Eq  Bus where (==) = (==) `on` busId
instance Ord Bus where compare = compare `on` busId

instance Eq  Source where (==) = (==) `on` sourceId
instance Ord Source where compare = compare `on` sourceId

instance Show Bus where
  show (Bus (PinId i) w) = "B" ++ show i ++ (if w /= 1 then ":" ++ show w else "")

instance Show Source where
  show (Source b prim ins o) = printf "Source %s %s %s %d" (show b) (show prim) (show ins) o

newPinId :: CircuitM PinId
newPinId = do { (p:ps',comps) <- Mtl.get ; Mtl.put (ps',comps) ; return p }

newBus :: Width -> CircuitM Bus
newBus w = flip Bus w <$> newPinId

newSource ::  Width -> String -> Sources -> Int -> CircuitM Source
newSource w prim ins o = (\ b -> Source b prim ins o) <$> newBus w

{--------------------------------------------------------------------
    Buses representing a given type
--------------------------------------------------------------------}

-- | Typed aggregate of buses. @'Buses' a@ carries a value of type @a@.
data Buses :: * -> * where
  UnitB  :: Buses Unit
  BoolB  :: Source -> Buses Bool
  IntB   :: Source -> Buses Int
  PairB  :: Buses a -> Buses b -> Buses (a :* b)
--   MaybeB :: Buses a -> Buses Bool -> Buses (Maybe a)
  FunB   :: (a :> b) -> Buses (a -> b)
  -- | Isomorphic form. Note: b must not have one of the standard forms.
  -- If it does, we'll get a run-time error when consuming.
  IsoB   :: Buses (Rep a) -> Buses a

instance Eq (Buses a) where
  UnitB     == UnitB        = True
  BoolB s   == BoolB s'     = s == s'
  IntB s    == IntB s'      = s == s'
  PairB a b == PairB a' b'  = a == a' && b == b'
  IsoB r    == IsoB r'      = r == r'
  FunB _    == FunB _       = False             -- TODO: reconsider
  _         == _            = False

-- deriving instance Typeable Buses
-- deriving instance Show (Buses a)

-- Deriving would need GenBuses a.

instance Show (Buses a) where
  show UnitB        = "()"
  show (BoolB b)    = show b
  show (IntB b)     = show b
  show (PairB a b)  = "("++show a++","++show b++")"
  show (FunB _)     = "<function>"
  show (IsoB b)     = "IsoB ("++show b++")"

-- TODO: Improve to Show instance with showsPrec

data Ty = UnitT | BoolT | IntT | PairT Ty Ty deriving (Eq,Ord)

genBuses :: GenBuses b => Prim a b -> Sources -> CircuitM (Buses b)
genBuses prim ins = fst <$> genBuses' (primName prim) ins 0

class GenBuses a where
  genBuses' :: String -> Sources -> Int -> CircuitM (Buses a,Int)
  delayC :: a -> (a :> a)
  ty :: a -> Ty                         -- dummy argument

genBus :: (Source -> Buses a) -> Width
       -> String -> Sources -> Int -> CircuitM (Buses a,Int)
genBus wrap w prim ins o = do src <- newSource w prim ins o
                              return (wrap src,o+1)

instance GenBuses Unit where
  genBuses' _ _ o = return (UnitB,o)
  delayC () = id
  ty = const UnitT

instance GenBuses Bool where
  genBuses' = genBus BoolB  1
  delayC = primDelay
  ty = const BoolT

delayPrefix :: String
delayPrefix = "Cons "
              -- "delay "

delayName :: String -> String
delayName = (delayPrefix ++)

unDelayName :: String -> Maybe String
unDelayName = stripPrefix delayPrefix

primDelay :: (GenBuses a, Show a) => a -> (a :> a)
primDelay a0 = namedC (delayName (show a0))

-- constComp' :: GenBuses b => String -> CircuitM (Buses b)

instance GenBuses Int  where
  genBuses' = genBus IntB  32
  delayC = primDelay
  ty = const IntT

instance (GenBuses a, GenBuses b) => GenBuses (a :* b) where
  genBuses' prim ins o =
    do (a,oa) <- genBuses' prim ins o
       (b,ob) <- genBuses' prim ins oa
       return (PairB a b, ob)
  delayC (a,b) = delayC a *** delayC b
  ty ~(a,b) = PairT (ty a) (ty b)

flattenB :: String -> Buses a -> Sources
flattenB name b = fromMaybe err (flattenMb b)
 where
   err = error $ "flattenB/"++name++": unhandled " ++ show b

flattenMb :: Buses a -> Maybe Sources
flattenMb = fmap toList . flat
 where
   flat :: Buses a -> Maybe (Seq Source)
   flat UnitB       = Just mempty
   flat (BoolB b)   = Just (singleton b)
   flat (IntB b)    = Just (singleton b)
   flat (PairB a b) = liftA2 (<>) (flat a) (flat b)
   flat (IsoB b)    = flat b
   flat _           = Nothing

isoErr :: String -> x
isoErr nm = error (nm ++ ": IsoB")

pairB :: Buses a :* Buses b -> Buses (a :* b)
pairB (a,b) = PairB a b

unPairB :: Buses (a :* b) -> Buses a :* Buses b
#if 0
unPairB (PairB a b) = (a,b)
unPairB (IsoB _)    = isoErr "unPairB"
#else
-- Lazier
unPairB w = (a,b)
 where
--    a = case w of
--          PairB p _ -> p
--          IsoB _    -> isoErr "unPairB"
--    b = case w of
--          PairB _ q -> q
--          IsoB _    -> isoErr "unPairB"

   (a,b) = case w of
             PairB p q -> (p,q)
             IsoB _    -> isoErr "unPairB"
#endif

unFunB :: Buses (a -> b) -> (a :> b)
unFunB (FunB circ) = circ
unFunB (IsoB _)    = isoErr "unFunB"

exlB :: Buses (a :* b) -> Buses a
exlB = fst . unPairB

exrB :: Buses (a :* b) -> Buses b
exrB = snd . unPairB

abstB :: Buses (Rep a) -> Buses a
abstB = IsoB

reprB :: Buses a -> Buses (Rep a)
reprB (IsoB a) = a
reprB b = error ("repB: non-IsoB: " ++ show b)

-- Alternatively,
-- 
--   abstB :: Rep a ~ a' => Buses a' -> Buses a
--   reprB :: Rep a ~ a' => Buses a -> Buses a'

{--------------------------------------------------------------------
    The circuit monad
--------------------------------------------------------------------}

type PrimName = String

-- | Primitive of type @a -> b@
newtype Prim a b = Prim { primName :: PrimName }

instance Show (Prim a b) where show = primName

-- Component: primitive instance with inputs & outputs
data Comp = forall a b. Comp (Prim a b) (Buses a) (Buses b)

deriving instance Show Comp

type Reuses = Int
#if !defined NoHashCons
-- Tracks prim applications (including output type) and reuses per component.
type CompInfo = Map (PrimName,Sources,Ty) (Comp,Reuses)
#else
type CompInfo = [Comp]
#endif

-- The circuit monad.
type CircuitM = State (PinSupply,CompInfo)

type BCirc a b = Buses a -> CircuitM (Buses b)

-- Instantiate a 'Prim'
genComp :: forall a b. GenBuses b => Prim a b -> BCirc a b
#if !defined NoHashCons
genComp prim a = do mb <- Mtl.gets (M.lookup key . snd)
                    case mb of
                      Just (Comp _ _ b', _) ->
                        do Mtl.modify (second (M.adjust (second succ) key))
                           return (unsafeCoerce b')
                      _                  ->
                        do b <- genBuses prim ins
                           let comp = Comp prim a b
                           Mtl.modify (second (M.insert key (comp,0)))
                           return b
 where
   ins  = flattenB "genComp" a
   name = primName prim
   key  = (name,ins,ty (undefined :: b))

-- TODO: Key on result type as well. Particularly important for polymorphic
-- constants such as bottom (and one day, zero).

#else
genComp prim a = do b <- genBuses prim (flattenB "genComp" a)
                    Mtl.modify (second (Comp prim a b :))
                    return b
#endif

constComp' :: GenBuses b => String -> CircuitM (Buses b)
constComp' str = genComp (Prim str) UnitB

constComp :: GenBuses b => String -> BCirc a b
constComp str = const (constComp' str)

-- TODO: eliminate constComp in favor of a more restrictive version in which a
-- == (), defined as flip genComp UnitB. Add domain flexibility in lambda-ccc
-- instead.

constM :: (Show b, GenBuses b) => b -> BCirc a b
constM b = constComp (constName b)

constName :: Show b => b -> String
constName = show

{--------------------------------------------------------------------
    Circuit category
--------------------------------------------------------------------}

infixl 1 :>, :+>

-- | Internal representation for '(:>)'.
type a :+> b = Kleisli CircuitM (Buses a) (Buses b)

-- | Circuit category
newtype a :> b = C { unC :: a :+> b }

instance RepCat (:>) where
  reprC = C (arr reprB)
  abstC = C (arr abstB)

-- pattern CK bc = C (Kleisli bc)

mkCK :: BCirc a b -> (a :> b)
mkCK = C . Kleisli

unmkCK :: (a :> b) -> BCirc a b
unmkCK = runKleisli . unC

-- TODO: Eliminate mkCK in favor of CK

inCK :: (BCirc a a' -> BCirc b b')
     -> ((a :> a') -> (b :> b'))
inCK = mkCK <~ unmkCK

inCK2 :: (BCirc a a' -> BCirc b b' -> BCirc c c')
      -> ((a :> a') -> (b :> b') -> (c :> c'))
inCK2 = inCK <~ unmkCK

namedC :: GenBuses b => String -> a :> b
namedC name = primOpt name noOpt

type Opt b = Sources -> CircuitM (Maybe (Buses b))

justA :: Applicative f => a -> f (Maybe a)
justA = pure . Just

nothingA :: Applicative f => f (Maybe a)
nothingA = pure Nothing

newComp :: (a :> b) -> Buses a -> CircuitM (Maybe (Buses b))
newComp cir = fmap Just . unmkCK cir

newComp1 :: SourceToBuses a => (a :> b) -> Source -> CircuitM (Maybe (Buses b))
newComp1 cir a = newComp cir (toBuses a)

newComp2 :: (SourceToBuses a, SourceToBuses b) =>
            (a :* b :> c) -> Source -> Source -> CircuitM (Maybe (Buses c))
newComp2 cir a b = newComp cir (PairB (toBuses a) (toBuses b))

newComp3L :: (SourceToBuses a, SourceToBuses b, SourceToBuses c) =>
             ((a :* b) :* c :> d) -> Source -> Source -> Source -> CircuitM (Maybe (Buses d))
newComp3L cir a b c = newComp cir (PairB (PairB (toBuses a) (toBuses b)) (toBuses c))

newComp3R :: (SourceToBuses a, SourceToBuses b, SourceToBuses c) =>
             (a :* (b :* c) :> d) -> Source -> Source -> Source -> CircuitM (Maybe (Buses d))
newComp3R cir a b c = newComp cir (PairB (toBuses a) (PairB (toBuses b) (toBuses c)))

newVal :: (Show b, GenBuses b) => b -> CircuitM (Maybe (Buses b))
newVal b = Just <$> constM' b

constM' :: (Show b, GenBuses b) => b -> CircuitM (Buses b)
constM' b = constComp' (constName b)

noOpt :: Opt b
noOpt = const nothingA

orOpt :: Binop (Opt b)
orOpt f g a = do mb <- f a
                 case mb of
                   Nothing -> g a
                   Just _  -> return mb

primOpt, primOptSort :: GenBuses b => String -> Opt b -> a :> b
#if !defined NoOptimizeCircuit
primOpt name opt =
  mkCK $ \ a -> let plain = genComp (Prim name) a in
                  case flattenMb a of
                    Nothing   -> plain
                    Just srcs -> opt srcs >>= maybe plain return

-- primOpt name opt =
--   mkCK $ \ a -> opt (flattenB ("primOpt/"++name) a)
--                  >>= maybe (genComp (Prim name) a) return

tryCommute :: a :> a
tryCommute = mkCK try
 where
   try (PairB (BoolB a) (BoolB a')) | a > a' = return (PairB (BoolB a') (BoolB a))
   try (PairB (IntB  a) (IntB  a')) | a > a' = return (PairB (IntB  a') (IntB  a))
   try b = return b

-- Like primOpt, but sorts. Use for commutative operations to improve reuse
-- (cache hits).
primOptSort name opt = primOpt name opt . tryCommute
#else
primOpt name _ = mkCK (genComp (Prim name))
primOptSort = primOpt
#endif

-- | Constant circuit from source generator (experimental)
constSM :: CircuitM (Buses b) -> (a :> b)
constSM mkB = mkCK (const mkB)

-- | Constant circuit from source
constS :: Buses b -> (a :> b)
constS b = constSM (return b)

constC :: (Show b, GenBuses b) => b -> a :> b
constC = mkCK . constM

-- Phasing out constC

-- pureC :: Buses b -> a :> b
-- pureC = mkCK . pure . pure

#if 0
litUnit :: Unit -> a :> Unit
litUnit = pureC . const UnitB

litInt :: Int -> a :> Int
litInt = pureC . IntB . IntS

litBool :: Bool -> a :> Bool
litBool = pureC . BoolB . BoolS
#endif

inC :: (a :+> b -> a' :+> b') -> (a :> b -> a' :> b')
inC = C <~ unC

inC2 :: (a :+> b -> a' :+> b' -> a'' :+> b'')
     -> (a :>  b -> a' :>  b' -> a'' :>  b'')
inC2 = inC <~ unC

instance Category (:>) where
  id  = C id
  (.) = inC2 (.)

-- onPairBM :: Functor m =>
--             (Buses a :* Buses b -> m (Buses a' :* Buses b'))
--          -> (Buses (a :* b) -> m (Buses (a' :* b')))
-- onPairBM f = fmap pairB . f . unPairB

crossB :: Applicative m =>
          (Buses a -> m (Buses c)) -> (Buses b -> m (Buses d))
       -> (Buses (a :* b) -> m (Buses (c :* d)))
crossB f g = (\ ~(a,b) -> liftA2 PairB (f a) (g b)) . unPairB

-- or drop crossB in favor of forkB with fstB and sndB

forkB :: Applicative m =>
         (Buses a -> m (Buses c)) -> (Buses a -> m (Buses d))
      -> (Buses a -> m (Buses (c :* d)))
forkB f g a = liftA2 PairB (f a) (g a)

-- or drop forkB in favor of dupB and crossB

dupB :: Applicative m =>
        Buses a -> m (Buses (a :* a))
dupB a = pure (PairB a a)

instance ProductCat (:>) where
  exl   = C (arr exlB)
  exr   = C (arr exrB)
  dup   = mkCK dupB
  (***) = inCK2 crossB  -- or default
  (&&&) = inCK2 forkB   -- or default

instance ClosedCat (:>) where
  apply   = C (applyK . first (arr (unC . unFunB)) . arr unPairB)
  curry   = inC $ \ h -> arr (FunB . C) . curryK (h . arr pairB)
  uncurry = inC $ \ f -> uncurryK (arr (unC . unFunB) . f) . arr unPairB 

#if defined TypeDerivation

-- ClosedCat type derivations:

type KC = Kleisli CircuitM

-- apply:

unC :: (a :> b) -> (a :+> b)
unFunB :: Buses (a -> b) -> (a :> b)
unC . unFunB :: Buses (a -> b) -> (a :+> b)
arr (unC . unFunB) :: KC (Buses (a -> b)) (a :+> b)
first (arr (unC . unFunB))
  :: KC (Buses (a -> b) :* Buses a) ((a :+> b) :* Buses a)
applyK . first (arr (unC . unFunB))
  :: KC (Buses (a -> b) :* Buses a) (Buses b)
applyK . first (arr (unC . unFunB)) . arr unPairB
  :: KC (Buses ((a -> b) :* a)) (Buses b)
  :: ((a -> b) :* a) :+> b
C (applyK . first (arr (unC . unFunB)) . arr unPairB) :: ((a -> b) :* a) :> b

-- curry:

h :: a :* b :> c
unC h :: a :* b :+> c
      :: KC (Buses (a :* b)) (Buses c)
unC h . arr pairB :: KC (Buses a :* Buses b) (Buses c)
curryK (unC h . arr pairB) :: KC (Buses a) (KC (Buses b) (Buses c))
arr C . curryK (unC h . arr pairB) :: KC (Buses a) (b :> c)
arr (FunB . C) . curryK (unC h . arr pairB) :: KC (Buses a) (Buses (b -> c))
C (arr (FunB . C) . curryK (unC h . arr pairB)) :: a :> (b -> c)

-- Derive uncurry by inverting curry:

f == arr (FunB . C) . curryK (h . arr pairB)
arr (unC . unFunB) . f == curryK (h . arr pairB)
uncurryK (arr (unC . unFunB) . f) == h . arr pairB
uncurryK (arr (unC . unFunB) . f) . arr unPairB == h

#endif

instance TerminalCat (:>) where
  -- it = C (const UnitB . it)
  -- it = mkCK (const (return UnitB))
  it = C (arr (pure UnitB))

-- instance ConstCat (:>) where
--   type ConstKon (:>) a b = (Show b, GenBuses b)
--   const = constC

#if 0
class MaybeCat k where
  nothing :: Unit `k` Maybe a
  just    :: a `k` Maybe a
  maybe   :: (Unit `k` c) -> (a `k` c) -> (Maybe a `k` c)

type Maybe a = a :* Bool

nothing = (undefined,False)
just a  = (a,True )

maybe n j (a,p) = if p then n else j a

newtype a :> b = C { unC :: a :+> b }
type a :+> b = Kleisli CircuitM (Buses a) (Buses b)

constM' :: (Show b, GenBuses b) => b -> CircuitM (Buses b)

#endif

#if 1

-- bottomScalar :: GenBuses b => CircuitM (Buses b)
bottomScalar :: GenBuses b => Unit :> b
bottomScalar = mkCK (constComp "undefined")

instance BottomCat (:>) Bool where bottomC = bottomScalar
instance BottomCat (:>) Int  where bottomC = bottomScalar

instance BottomCat (:>) Unit where
--   bottomC = mkCK (const (return UnitB))
  bottomC = C (arr (const UnitB))

instance (BottomCat (:>) a, BottomCat (:>) b) => BottomCat (:>) (a :* b) where
  bottomC = bottomC &&& bottomC

instance BottomCat (:>) b => BottomCat (:>) (a -> b) where
  bottomC = curry (bottomC . exl)

#if defined TypeDerivation
bottomC :: Unit :> b
bottomC . exl :: Unit :* a :> b
curry (bottomC . exl) :: Unit :> (a -> b)
#endif

#elif 0
instance GenBuses a => BottomCat (:>) a where
  bottomC = mkCK (const mkBot)
#elif 0
instance BottomCat (:>) where
  type BottomKon (:>) a = GenBuses a
  bottomC = mkCK (const (genBuses (Prim "undefined") []))
-- See the note at BottomCat
#elif 0
instance BottomCat (:>) where
  type BottomKon (:>) a = GenBuses a
  bottomC = mkCK (const mkBot)
#endif

pattern ConstS name <- Source _ name [] 0
pattern Val x       <- ConstS (reads -> [(x,"")])

pattern TrueS    <- ConstS "True"
pattern FalseS   <- ConstS "False"
pattern NotS a   <- Source _ "not" [a] 0
pattern XorS a b <- Source _ "xor" [a,b] 0

class SourceToBuses a where toBuses :: Source -> Buses a
instance SourceToBuses Bool where toBuses = BoolB
instance SourceToBuses Int  where toBuses = IntB

sourceB :: SourceToBuses a => Source -> CircuitM (Maybe (Buses a))
sourceB = justA . toBuses

#define Sat(pred) ((pred) -> True)
#define Eql(x) Sat(==(x))

instance BoolCat (:>) where
  notC = primOpt "not" $ \ case
           [NotS a]     -> sourceB a
           [Val x]      -> newVal (not x)
           _            -> nothingA
  andC = primOptSort "and" $ \ case
           [TrueS ,y]   -> sourceB y
           [x,TrueS ]   -> sourceB x
           [x@FalseS,_] -> sourceB x
           [_,y@FalseS] -> sourceB y
#if !defined NoIdempotence
           [x,Eql(x)]   -> sourceB x
#endif
           [x,NotS (Eql(x))] -> newVal False
           [NotS x,Eql(x)]   -> newVal False
           _            -> nothingA
  orC  = primOptSort "or"  $ \ case
           [FalseS,y]   -> sourceB y
           [x,FalseS]   -> sourceB x
           [x@TrueS ,_] -> sourceB x
           [_,y@TrueS ] -> sourceB y
#if !defined NoIdempotence
           [x,Eql(x)]   -> sourceB x
#endif
           [x,NotS (Eql(x))] -> newVal True
           [NotS x,Eql(x)]   -> newVal True
           -- not a || not b == not (a && b)
           -- TODO: Handle more elegantly.
           [NotS x, NotS y] -> do o <- unmkCK andC (PairB (BoolB x) (BoolB y))
                                  newComp notC o
           _            -> nothingA
  xorC = primOptSort "xor" $ \ case
           [FalseS,y]   -> sourceB y
           [x,FalseS]   -> sourceB x
           [TrueS,y ]   -> newComp1 notC y
           [x,TrueS ]   -> newComp1 notC x
           [x,Eql(x)]   -> newVal False
           [x,NotS (Eql(x))] -> newVal True
           [NotS x,Eql(x)]   -> newVal True
           _            -> nothingA

boolToIntC :: Bool :> Int
boolToIntC = namedC "boolToInt"

-- instance BoolCat (:>) where
--   notC = namedC "not"
--   andC = namedC "and"
--   orC  = namedC "or"
--   xorC = namedC "xor"


-- TODO: After I have more experience with these graph optimizations, reconsider
-- the interface.

-- instance NumCat (:>) Int  where { add = namedC "add" ; mul = namedC "mul" }

-- Zero or one, yielding the False or True, respectively.
pattern BitS b <- Source _ (readBit -> Just b) [] 0

readBit :: String -> Maybe Bool
readBit "0" = Just False
readBit "1" = Just True
readBit _   = Nothing

pattern ZeroS <- ConstS "0"
pattern OneS  <- ConstS "1"

pattern BToIS a <- Source _ "boolToInt" [a] 0

instance NumCat (:>) Int where
 add = primOptSort "add" $ \ case
         [Val x, Val y] -> newVal (x+y)
         [ZeroS,y]      -> sourceB y
         [x,ZeroS]      -> sourceB x
         _              -> nothingA
 mul = primOptSort "mul" $ \ case
         [Val x, Val y] -> newVal (x*y)
         [OneS ,y]      -> sourceB y
         [x,OneS ]      -> sourceB x
         [x@ZeroS,_]    -> sourceB x
         [_,y@ZeroS]    -> sourceB y
         _              -> nothingA

-- instance NumCat (:>) Int where
--  add = namedC "add"
--  mul = namedC "mul"

-- Simplifications for all types:
-- 
--   if' (False,(_,a))     = a
--   if' (True ,(b,_))     = b
--   if' (_    ,(a,a))     = a
--   if' (a,(b,bottom))    = b
--   if' (a,(bottom,c))    = c
--
-- Simplifications for Bool values:
-- 
--   if' (c,(True,False))  = c
--   if' (c,(False,True))  = not c
--   if' (a,(b,False))     =     a && b
--   if' (a,(False,b))     = not a && b
--   if' (a,(True ,b))     =     a || b
--   if' (a,(b,True ))     = not a || b
--   if' (c,(not a,a))     = c `xor` a
--   if' (c,(a,not a))     = c `xor` not a
--   if' (b,(c `xor` a,a)) = (b && c) `xor` a
--   if' (b,(a `xor` c,a)) = (b && c) `xor` a

ifOptB :: Opt Bool
ifOptB = \ case
  [c,TrueS,FalseS]       -> sourceB c
  [c,FalseS,TrueS]       -> newComp1 notC c
  [a,b,FalseS]           -> newComp2 andC a b
  [a,FalseS,b]           -> newComp2 (andC . first notC) a b -- not a && b
  [a,TrueS, b]           -> newComp2 orC  a b
  [a,b ,TrueS]           -> newComp2 (orC  . first notC) a b -- not a || b
  [c,NotS a,Eql(a)]      -> newComp2 xorC c a
  [c,a,b@(NotS(Eql(a)))] -> newComp2 xorC c b
  [b,c `XorS` a,Eql(a)]  -> newComp3L (xorC . first andC) b c a -- (b && c) `xor` a
  [b,a `XorS` c,Eql(a)]  -> newComp3L (xorC . first andC) b c a -- ''
  _                      -> nothingA

#if !defined NoIfBotOpt
pattern BottomS <- ConstS "undefined"
#endif

ifOpt :: SourceToBuses a => Opt a
ifOpt = \ case
  [FalseS,_,a]  -> sourceB a
  [ TrueS,b,_]  -> sourceB b
  [_,a,Eql(a)]  -> sourceB a
#if !defined NoIfBotOpt
  [_,b,BottomS] -> sourceB b
  [_,BottomS,c] -> sourceB c
#endif
  _             -> nothingA

ifOptI :: Opt Int
#if 1
-- if c then 0 else b == if c then boolToInt False else b
-- if c then 1 else b == if c then boolToInt True  else b
-- 
-- if c then a else 0 == if c then a else boolToInt False
-- if c then a else 1 == if c then a else boolToInt True
-- 
-- if c then boolToInt a else boolToInt b = boolToInt (if c then a else b)
ifOptI = \ case
  [c,BitS x,b]         -> newComp2 (ifC . second (bToIConst x &&& id)) c b
  [c,a,BitS y]         -> newComp2 (ifC . second (id &&& bToIConst y)) c a
  [c,BToIS a, BToIS b] -> newComp3R (boolToIntC . ifC) c a b
  _                    -> nothingA

bToIConst :: Bool -> (a :> Int)
bToIConst x = boolToIntC . constC x

#else
-- (if c then 1 else 0) = boolToInt c
-- (if c then 0 else 1) = boolToInt (not c)
ifOptI = \ case
  [c,OneS,ZeroS] -> newComp1 boolToIntC c
  [c,ZeroS,OneS] -> newComp1 (boolToIntC . notC) c
  _              -> nothingA
#endif

instance IfCat (:>) Bool where ifC = primOpt "if" (ifOpt `orOpt` ifOptB)
instance IfCat (:>) Int  where ifC = primOpt "if" (ifOpt `orOpt` ifOptI)

-- instance IfCat (:>) Bool where ifC = namedC "if"
-- instance IfCat (:>) Int  where ifC = namedC "if"

instance IfCat (:>) Unit where ifC = unitIf

instance (IfCat (:>) a, IfCat (:>) b) => IfCat (:>) (a :* b) where
  ifC = prodIf

instance IfCat (:>) b => IfCat (:>) (a -> b) where
  ifC = funIf

instance GenBuses a => Show (a :> b) where
  show = show . runC

--     Application is no smaller than the instance head
--       in the type family application: RepT :> a
--     (Use -XUndecidableInstances to permit this)

-- Turn a circuit into a list of components, including fake In & Out.
runC :: GenBuses a => (a :> b) -> [(Comp,Reuses)]
runC = runU . unitize

type UU = Unit :> Unit

runU :: UU -> [(Comp,Reuses)]
runU cir = getComps compInfo
 where
   compInfo :: CompInfo
   (_,compInfo) = execState (unmkCK cir UnitB) (PinId <$> [0 ..],mempty)
#if !defined NoHashCons
   getComps = M.elems 
#else
   getComps = map (,0)
#endif

-- Wrap a circuit with fake input and output
unitize :: GenBuses a => (a :> b) -> UU
unitize = namedC "Out" <~ namedC "In"

{--------------------------------------------------------------------
    Visualize circuit as dot graph
--------------------------------------------------------------------}

-- I could use the language-dot API, but it's easier not to.
-- TODO: Revisit this choice if the string manipulation gets complicated.

systemSuccess :: String -> IO ()
systemSuccess cmd = 
  do status <- system cmd
     case status of
       ExitSuccess -> return ()
       _ -> fail (printf "command \"%s\" failed." cmd)


type Attr = (String,String)

outG :: GenBuses a => String -> [Attr] -> (a :> b) -> IO ()
outG = outGWith ("pdf","")

-- Some options:
-- 
-- ("pdf","")
-- ("svg","")
-- ("png","-Gdpi=200")
-- ("jpg","-Gdpi=200")

renameC :: Unop String
renameC = id
#if defined NoOptimizeCircuit
        . (++"-unopt")
#else
#if defined NoIdempotence
        . (++"-no-idem")
#endif
#if defined NoIfBotOpt
        . (++"-no-ifbot")
#endif
#endif
#if defined NoHashCons
        . (++"-no-hash")
#endif

type Name = String
type Report = String

-- TODO: Phase out
outGWith :: GenBuses a => (String,String) -> Name -> [Attr] -> (a :> b) -> IO ()
outGWith ss s ats circ = outGWithU ss s ats (unitize circ)

outGWithU :: (String,String) -> Name -> [Attr] -> UU -> IO ()
outGWithU ss name ats uu = outDotG ss ats (mkGraph name uu)

mkGraph :: Name -> UU -> (Name,DGraph,Report)
mkGraph (renameC -> name') uu = (name', connectState graph,report)
 where
   (graph,depth) = uuGraph uu
   report | depth == 0 = "No components.\n"  -- except In & Out
          | otherwise  =
              printf "Components: %s.%s Depth: %d.\n"
                (summary graph)
#if !defined NoHashCons
                (let reused :: Map PrimName Reuses
                     reused = M.fromListWith (+)
                               [(nm,reuses) | CompS _ nm _ _ reuses <- graph]
                 in
                   case showCounts (M.toList reused) of
                     ""  -> ""
                     str -> printf " Reuses: %s." str)
#else          
                ""
#endif         
                depth
outDotG :: (String,String) -> [Attr] -> (Name,DGraph,Report) -> IO ()
outDotG (outType,res) attrs (name,graph,report) = 
  do createDirectoryIfMissing False outDir
     writeFile (outFile "dot")
       (graphDot name attrs graph ++ "\n// "++ report)
     -- putStr report
     systemSuccess $
       printf "dot %s -T%s %s -o %s" res outType (outFile "dot") (outFile outType)
     printf "Wrote %s\n" (outFile outType)
     systemSuccess $
       printf "%s %s" open (outFile outType)
 where
   outDir = "out"
   outFile suff = outDir++"/"++name++"."++suff
   open = case SI.os of
            "darwin" -> "open"
            "linux"  -> "display" -- was "xdg-open"
            _        -> error "unknown open for OS"

-- Replace the state pseudo-components with connected-up delay elements.
connectState :: Unop DGraph
#ifdef MealyToArrow
connectState = id
#else
-- Drop OldState and NewState pseudo-components. Replace uses of OldState's
-- output with corresponding uses of NewState's inputs.
connectState g0 = g3
 where
   (new,g1) = gDrop "NewState" g0
   (old,g2) = gDrop "OldState" g1
   g3 = patchG (compOuts old) (compIns new) g2
   gDrop :: Name -> DGraph -> (CompS,DGraph)
   gDrop name g =
     case partition ((== name) . compName) g of
       ([c],g') -> (c,g')
       (cs,_)   -> error ("connectState: " ++ name ++ ": " ++ show cs)

patchG :: [Bus] -> [Bus] -> Unop DGraph
patchG olds news = map patchC
 where
   patchC :: Unop CompS
   patchC = (onInputs.fmap) patchIn
   patchIn :: Unop Bus
   patchIn b = fromMaybe b (M.lookup b patchMap)
   patchMap = M.fromList (olds `zip` news)

onInputs :: Unop [Input] -> Unop CompS
onInputs f (CompS n p i o m) = CompS n p (f i) o m

-- TODO: Rewrite connectState entirely, with more elegance and efficiency. Avoid
-- multiple linear list traversals!
#endif

showCounts :: [(PrimName,Int)] -> String
showCounts = intercalate ", "
           . map (\ (nm,num) -> printf "%d %s" num nm)
           . (\ ps -> if length ps <= 1 then ps
                       else ps ++ [("total",sum (snd <$> ps))])
           . filter (\ (nm,n) -> n > 0 && not (isOuterPrim nm))

summary :: DGraph -> String
summary = showCounts
        . histogram
        . map compName

histogram :: Ord a => [a] -> [(a,Int)]
histogram = map (head &&& length) . group . sort

-- TODO: Instead of failing, emit a message about the generated file. Perhaps
-- simply use "echo".

type Input  = Bus
type Output = Bus

data CompS = CompS CompNum PrimName [Input] [Output] Reuses deriving Show

compNum :: CompS -> CompNum
compNum (CompS n _ _ _ _) = n
compName :: CompS -> PrimName
compName (CompS _ nm _ _ _) = nm
compIns :: CompS -> [Input]
compIns (CompS _ _ ins _ _) = ins
compOuts :: CompS -> [Output]
compOuts (CompS _ _ _ outs _) = outs

instance Eq CompS where (==) = (==) `on` compNum
instance Ord CompS where compare = compare `on` compNum

type DGraph = [CompS]

type Dot = String

uuGraph :: UU -> (DGraph,Depth)
uuGraph = trimDGraph . map simpleComp . tagged . runU

circuitGraph :: GenBuses a => (a :> b) -> (DGraph,Depth)
circuitGraph = uuGraph . unitize
-- circuitGraph = trimDGraph . map simpleComp . tagged . runC

type Depth = Int

-- #define SkipTrim

-- Remove unused components.
-- Depth-first search from the "Out" component.
-- Explicitly include other outer prims as well, in case any are ignored.
trimDGraph :: DGraph -> (DGraph, Depth)
#ifdef SkipTrim
trimDGraph g = (g,0)
#else
type TrimM = State (Map CompS Depth)

trimDGraph g =
  (M.keys *** pred . maximum) . swap $
    runState (mapM searchComp startComps) M.empty
 where
   startComps = filter (isOuterPrim . compName) g
   searchComp :: CompS -> TrimM Depth
   searchComp c =
    do mb <- Mtl.gets (M.lookup c)
       case mb of
         Nothing ->
           do depths <- mapM searchOut (compIns c)
              let depth = if null depths then 0 else 1 + maximum depths
              Mtl.modify (M.insert c depth)
              return depth
         Just depth -> return depth
    where
      searchOut :: Output -> TrimM Depth
      searchOut o = searchComp (fromMaybe (error msg) (M.lookup o sourceComps))
       where
         msg = printf "trimDGraph: mystery output %s in comp #%d. Graph: %s."
                       (show o) (compNum c) (show g)
   sourceComps :: Map Output CompS
   sourceComps = foldMap (\ c -> M.fromList [(o,c) | o <- compOuts c]) g
--    comps :: Map CompNum CompS
--    comps = M.fromList [(compNum c,c) | c <- g]
#endif

-- The pred eliminates counting both In (constants) *and* Out.

graphDot :: String -> [Attr] -> DGraph -> Dot
graphDot name attrs comps =
  printf "digraph %s {\n%s}\n" (tweak <$> name)
         (concatMap wrap (prelude ++ recordDots comps))
 where
   prelude = [ "rankdir=LR"
             , "node [shape=Mrecord]"
             , "bgcolor=transparent"
             -- , "ratio=1"
             --, "ranksep=1"
             -- , fixedsize=true
             ] ++ [a ++ "=" ++ show v | (a,v) <- attrs]
   wrap  = ("  " ++) . (++ ";\n")
   tweak '-' = '_'
   tweak c   = c

type Statement = String

simpleComp :: (CompNum,(Comp,Reuses)) -> CompS
simpleComp (n, (Comp prim a b,reuses)) = CompS n name (flat a) (flat b) reuses
 where
   name = show prim
   flat :: forall t. Buses t -> [Bus]
   flat = map sourceBus . flattenB name


-- Working here in converting away from flattening


data Dir = In | Out deriving Show
type PortNum = Int
type CompNum = Int

taggedFrom :: Int -> [a] -> [(Int,a)]
taggedFrom n = zip [n ..]

tagged :: [a] -> [(Int,a)]
tagged = taggedFrom 0

recordDots :: [CompS] -> [Statement]
recordDots comps = nodes ++ edges
 where
   nodes = node <$> comps
    where
      node :: CompS -> String
      -- -- drop if no ins or outs
      -- node (_,prim,[],[]) = "// removed disconnected " ++ prim
      node (CompS nc prim ins outs _) =
        printf "%s [label=\"{%s%s%s}\"]" (compLab nc) 
          (ports "" (labs In ins) "|") prim (ports "|" (labs Out outs) "")
       where
         ports _ "" _ = ""
         ports l s r = printf "%s{%s}%s" l s r
         labs :: Dir -> [Bus] -> String
         labs dir bs = intercalate "|" (portSticker <$> tagged bs)
          where
            portSticker :: (Int,Bus) -> String
            portSticker (p, _) = bracket (portLab dir p) -- ++ show p -- show p for port # debugging
--             portSticker (p,BusS  _) = bracket (portLab dir p) -- ++ show p -- show p for port # debugging
--             portSticker (_,BoolS x) = show x  -- or showBool x
--             portSticker (_,IntS  x) = show x
   bracket = ("<"++) . (++">")
   portLab :: Dir -> PortNum -> String
   portLab dir np = printf "%s%d" (show dir) np
   srcMap = sourceMap comps
   edges = concatMap compEdges comps
    where
      compEdges (CompS snkComp _ ins _ _) = edge <$> tagged ins
       where
         edge (ni, Bus i width) =
           printf "%s -> %s%s"
             (port Out (srcMap M.! i)) (port In (width,snkComp,ni)) (label width)
          where
            label 1 = ""
            label w = printf " [label=\"%d\",fontsize=10]" w
--          edge (ni, BoolS x) = litComment ni x
--          edge (ni, IntS  x) = litComment ni x
--          litComment :: Show a => CompNum -> a -> String
--          litComment ni x = "// "  ++ show x ++ " -> " ++ port In (0,snkComp,ni)
   port :: Dir -> (Width,CompNum,PortNum) -> String
   -- TODO: Use the width, perhaps to label the arrows
   port dir (_w,nc,np) = printf "%s:%s" (compLab nc) (portLab dir np)
   compLab nc = 'c' : show nc

-- showBool :: Bool -> String
-- showBool False = "F"
-- showBool True  = "T"

-- Map each pin to its width, source component and output port number
type SourceMap = Map PinId (Width,CompNum,PortNum)

-- TODO: Try removing width.

-- data SourceInfo = BusInfo Width CompNum PortNum
--                 | LitInfo String

sourceMap :: [CompS] -> SourceMap
sourceMap = foldMap $ \ (CompS nc _ _ outs _) ->
              M.fromList [(p,(wid,nc,np)) | (np,Bus p wid) <- tagged outs ]

{-

-- Stateful addition via StateFun

outSG :: (IsSourceP s, IsSourceP2 a b, StateCatWith sk (:>) s) =>
         String -> (a `sk` b) -> IO ()
outSG name = outG name . runState

type (:->) = StateFun (:>) Bool

-}

{-

-- TODO: Revisit this whole line of thinking now that I have a ClosedCat instance for (:>)

{--------------------------------------------------------------------
    Temporary hack for StateExp
--------------------------------------------------------------------}

-- For ClosedCat, we'll use tries.

-- instance ClosedCat (:>) where
--   type Exp (:>) u v = u :->: v
--   type ClosedKon (:>) u = HasTrie u
--   apply = muxC
--   curry = undefined
--   uncurry = undefined

--     Could not deduce (IsSource (Buses b),
--                       IsSource (Buses a),
--                       IsSource (Buses (Trie a b)))
--       arising from a use of `muxC'

{-
newtype a :> b = Circ (Kleisli CircuitM (Buses a) (Buses b))

apply   :: ((a :->: b) :* a) :> b
curry   :: ((a :* b) :> c) -> (a :> (b :->: c))
uncurry :: (a :> (b :->: c)) -> (a :* b) :> c
-}

--   apply   :: ClosedKon k a => (Exp k a b :* a) `k` b
--   curry   :: ClosedKon k b => ((a :* b) `k` c) -> (a `k` Exp k b c)
--   uncurry :: ClosedKon k b => (a `k` Exp k b c) -> (a :* b) `k` c

applyC :: ( HasTrie a, IsSource2 a b, IsSource (a :->: b) ) =>
          ((a :->: b) :* a) :> b
applyC = muxC

curryC :: ( HasTrie b, Show (b :->: b), CTraversableWith (Trie b) (:>)
          , IsSource (b :->: b)
          -- , StrongCat (:>) (Trie b), StrongKon (:>) (Trie b) a b
          , b ~ bool
          ) => 
          ((a :* b) :> c) -> (a :> (b :->: c))
curryC = traverseCurry idTrie

-- TODO: Give StrongCat instance and drop constraint the Strong or bool
-- constraint above.

-- uncurryC :: (a :> (b :->: c)) -> (a :* b) :> c

uncurryC :: (HasTrie b, IsSource2 b c, IsSource (b :->: c)) =>
            (a :> (b :->: c)) -> ((a :* b) :> c)
uncurryC h = applyC . first h

{-

h :: a :> (b :->: c)
first h :: (a :* b) :> ((b :->: c) :* b)
apply . first h :: (a :* b) :> c

-}

-- instance ClosedCatU k s => StateCat (StateExp k s) where
--   type StateKon  (StateExp k s) = ClosedKon k s
--   type StateBase (StateExp k s) = k
--   type StateT    (StateExp k s) = s
--   state    f  = StateExp (curry (f . swapP))
--   runState st = uncurry (unStateExp st) . swapP


infixr 1 :+>
-- Temporary specialization of StateExp to (:>) and bool
newtype (a :+> b) =
  BStateExp { unBStateExp :: a :> (bool :->: (b :* bool)) }

pureBState :: (a :> b) -> a :+> b
pureBState f = bstate (swapP . second f)

inBState :: (s ~ t, s ~ bool, IsSource b) =>
            (((s :* a) :> (b :* s)) -> ((t :* c) :> (d :* t)))
         -> (a :+> b                -> c :+> d)
inBState = bstate <~ runBState

inBState2 :: (s ~ t, u ~ s, s ~ bool, IsSource b, IsSource d) =>
             (((s :* a) :> (b :* s)) -> ((t :* c) :> (d :* t)) -> ((u :* e) :> (f :* u)))
         -> (a :+> b                -> c :+> d                -> e :+> f)
inBState2 = inBState <~ runBState


-- Oh. I don't think I can define a Category instance, because of the IsSource
-- constraints.


-- Temporary specialization of state and runState

bstate :: (s ~ bool) =>
          (s :* a) :> (b :* s) -> a :+> b
bstate f  = BStateExp (curryC (f . swapP))

runBState :: (s ~ bool, IsSource b) =>
             a :+> b -> (s :* a) :> (b :* s)
runBState st = uncurryC (unBStateExp st) . swapP

-- | Full adder with 'StateCat' interface
fullAddBS :: Pair bool :+> bool
fullAddBS = bstate fullAdd

-- | Structure adder with 'StateCat' interface
addBS :: CTraversableWith t (:+>) =>
         t (Pair bool) :+> t bool
addBS = traverseC fullAddBS

outBSG :: IsSource2 a b =>
          String -> (a :+> b) -> IO ()
outBSG name = outG name . runBState

type AddBS f = f (Pair bool) :+> f bool

type AddVBS n = AddBS (Vec  n)
type AddTBS n = AddBS (Tree n)

addVBS1 :: AddVBS N1
addVBS1 = addBS

-- addVBS2 :: AddVBS N2
-- addVBS2 = addBS

addTBS1 :: AddTBS N1
addTBS1 = addBS

-}

{--------------------------------------------------------------------
    Another pass at ClosedCat
--------------------------------------------------------------------}

{-
type family Unpins a

type instance Unpins PinId = Bool

-- Everything else distributes:
type instance Unpins ()         = ()
type instance Unpins ( a :* b ) = Unpins a :* Unpins b
type instance Unpins (Pair a  ) = Pair (Unpins a)
type instance Unpins (Vec n a ) = Vec  n (Unpins a)
type instance Unpins (Tree n a) = Tree n (Unpins a)

distribMF :: Monad m => m (p -> q) -> (p -> m q)
distribMF u p = liftM ($ p) u

-- instance ClosedCat (:>) where
--   type ClosedKon (:>) u =
--     (IsSource u, HasTrie (Unpins u), Traversable (Trie (Unpins u)))
--   type Exp (:>) u v = Unpins u :->: v
--   apply = muxC

--     Could not deduce (IsSource b, IsSource (Trie (Unpins a) b))
--       arising from a use of `muxC'



--   curry   = inNew $ \ f -> sequence . trie . curry f
--   uncurry = inNew $ \ h -> uncurry (distribMF . liftM untrie . h)

--   apply   :: ClosedKon k a => (Exp k a b :* a) `k` b
--   curry   :: ClosedKon k b => ((a :* b) `k` c) -> (a `k` Exp k b c)
--   uncurry :: ClosedKon k b => (a `k` Exp k b c) -> (a :* b) `k` c

  apply   :: ClosedKon (:>) a => ((Unpins a :->: b) :* a) :> b
  curry   :: ClosedKon (:>) b => ((a :* b) :> c) -> (a :> (Unpins b :->: c))
  uncurry :: ClosedKon (:>) b => (a :> (Unpins b :->: c)) -> ((a :* b) :> c)

uncurry untrie :: ((k :->: v) :* k) -> v
uncurry untrie :: ((Unpins a :->: b) :* Unpins a) -> b

-}

#if defined NoSums

-- type BusSum a b = ()

sumErr :: String -> a
sumErr str = error (str ++ " for (:>): not defined. Sorry")

instance CoproductCat (:>) where
  inl   = sumErr "inl"
  inr   = sumErr "inr"
  (|||) = sumErr "(|||)"

instance DistribCat (:>) where
  distl = sumErr "distl"
  distr = sumErr "distr"

#endif

#if defined StaticSums

type instance Buses (a :+ b) = Buses a :+ Buses b

instance CoproductCat (:>) where
  inl   = C inl
  inr   = C inr
  (|||) = inC2 (|||)

instance DistribCat (:>) where
  distl = C distl
  distr = C distr

{- Types:

Abbreviations:

> type KC = Kleisli CircuitM
> type S = Source

Consider `Source`- specialized versions of `KC`:

> inl :: KC (S a) (S a :+ S b)
>     == KC (S a) (S (a :+ b))
>     == a :+> a :+ b
>
> inr :: KC (S b) (S a :+ S b)
>     == KC (S b) (S (a :+ b))
>     == b :+> a :+ b
>
> (|||) :: KC (S a) (S c) -> KC (S b) (S c) -> KC (S a :+ S b) (S c)
>       == KC (S a) (S c) -> KC (S b) (S c) -> KC (S (a :+ b)) (S c)
>       == a :+> c -> b :+> c -> (a :+ b) :+> c
>
> distl :: KC (S a :* (S u :+ S v)) (S a :* S u :+ S a :* S v)
>       == KC (S (a :* (u :+ v))) (S (a :* u :+ a :* v))
>       == (a :* (u :+ v)) :+> (a :* u :+ a :* v)
>
> distr :: KC ((S u :+ S v) :* S b) (S u :* S b :+ S v :* S b)
>       == KC (S ((u :+ v) :* b)) (S (u :* b :+ v :* b))
>       == ((u :+ v) :* b) :+> (u :* b :+ v :* b)

-}

#elif defined TaggedSums

{--------------------------------------------------------------------
    Coproducts
--------------------------------------------------------------------}

-- Move elsewhere

infixl 6 :++

data a :++ b = UP { sumBuses :: Seq PinId, sumFlag :: PinId } deriving Show

type instance Buses (a :+ b) = Buses a :++ Buses b

instance IsSource2 a b => IsSource (a :++ b) where
  toBuses (UP ps f) = ps <> singleton f
  genSource =
    liftM2 UP (Seq.replicateM (numBuses (undefined :: (a :++ b)) - 1) newPinId)
              newPinId
  numBuses _ =
    (numBuses (undefined :: a) `max` numBuses (undefined :: b)) + 1

unsafeInject :: forall q a b. (IsSourceP q, IsSourceP2 a b) =>
                Bool -> q :> a :+ b
unsafeInject flag = mkCK $ \ q ->
  do x <- constM flag q
     let nq  = numBuses (undefined :: Buses q)
         na  = numBuses (undefined :: Buses a)
         nb  = numBuses (undefined :: Buses b)
         pad = Seq.replicate (max na nb - nq) x
     return (UP (toBuses q <> pad) x)

inlC :: IsSourceP2 a b => a :> a :+ b
inlC = unsafeInject False

inrC :: IsSourceP2 a b => b :> a :+ b
inrC = unsafeInject True

infixr 2 |||*

{-
(|||*) :: (IsSourceP2 a b, IsSourceP c) =>
          (a :> c) -> (b :> c) -> (a :+ b :> c)
f |||* g = muxC . ((f *** g) . extractBoth &&& pureC sumFlag)

cond :: IsSource (Buses c) => ((c :* c) :* Bool) :> c
cond = muxCT . first toPair

muxCT :: (IsSourceP2 ((u :->: v) :* u) v, HasTrie u) =>
         ((u :->: v) :* u) :> v
muxCT = namedC "mux"
-}

(|||*) :: (IsSourceP2 a b, IsSourceP c) =>
          (a :> c) -> (b :> c) -> (a :+ b :> c)
f |||* g = muxC . (pureC sumFlag &&& (f *** g) . extractBoth)

-- TODO: Reduce muxC to several one-bit muxes.

-- unsafeExtract :: IsSource (Buses c) => a :+ b :> c
-- unsafeExtract = pureC (pinsSource . sumBuses)

extractBoth :: IsSourceP2 a b => a :+ b :> a :* b
extractBoth = pureC ((pinsSource &&& pinsSource) . sumBuses)

pinsSource :: IsSource a => Seq PinId -> a
pinsSource pins = Mtl.evalState genSource (toList pins)

pureC :: (Buses a -> Buses b) -> (a :> b)
pureC = C . arr

-- TODO: Generalize CoproductCat to accept constraints like IsSourceP, and then
-- move inlC, inrC, (|||*) into a CoproductCat instance. Tricky.

#elif defined ChurchSums

{--------------------------------------------------------------------
    Yet another sum experiment: Church encoding
--------------------------------------------------------------------}

type instance Buses (a :+ b) = PSum a b

newtype PSum a b =
  PSum { unPSum :: forall c. CondCat (:>) c => (a :=> c) :* (b :=> c) :> c }

psc :: (forall c. CondCat (:>) c => (a :> c) :* (b :> c) -> CircuitM (Buses c)) -> PSum a b
psc q = PSum (mkCK q)

unPsc :: PSum a b -> (forall c. CondCat (:>) c => (a :> c) :* (b :> c) -> CircuitM (Buses c))
unPsc ps = unmkCK (unPSum ps)

inlC :: a :> a :+ b
inlC = mkCK (\ a -> return (psc (\ (f,_) -> unmkCK f a)))

inrC :: b :> a :+ b
inrC = mkCK (\ b -> return (psc (\ (_,g) -> unmkCK g b)))

infixr 2 |||*

(|||*) :: forall a b c. CondCat (:>) c =>
          (a :> c) -> (b :> c) -> (a :+ b :> c)
f |||* g = mkCK (\ q -> unPsc q (f,g))

distlC :: forall u a b. (u :* (a :+ b)) :> (u :* a :+ u :* b)
distlC = mkCK (\ (u,q) -> return (psc (\ (f,g) -> unPsc q (injl u f, injl u g))))

{-
u :: Buses u
q :: Buses (a :+ b)
  == PSum a b
unPSum q :: forall c. CondCat (:>) c => (a :> c) :* (b :> c) -> CircuitM (Buses c)

f :: u :* a :> c
g :: u :* b :> c

injl u f :: a :> c
injl u g :: b :> c

unPSum q (injl u f) (injl v f) :: CircuitM (Buses c)

-}

distrC :: forall v a b. ((a :+ b) :* v) :> (a :* v :+ b :* v)
distrC = mkCK (\ (q,v) -> return (psc (\ (f,g) -> unPsc q (injr v f, injr v g))))

injl :: Buses u -> (u :* a :> c) -> (a :> c)
injl u = inCK (. (u,))

injr :: Buses v -> (a :* v :> c) -> (a :> c)
injr v = inCK (. (,v))

-- (. (u,)) :: (Buses (u :* a) -> CircuitM (Buses c)) -> (Buses a -> CircuitM (Buses c))
-- inCK (. (u,)) :: (u :* a : c) -> (a :> c)

#if 0
instance                        CondCat (:>) Unit      where cond = it
instance                        CondCat (:>) Bool      where cond = mux
instance (CondCat2 (:>) a b) => CondCat (:>) (a :*  b) where cond = prodCond
instance (CondCat (:>) b)    => CondCat (:>) (a :=> b) where cond = funCond
instance CondCat (:>) (a :+ b)                         where cond = sumCond
#endif

sumToFun' :: (t :> a :+ b)
          -> forall c. CondCat (:>) c => t :> ((a :=> c) :* (b :=> c) :=> c)
sumToFun' = (inCK.fmap.fmap) unPSum

sumToFun :: forall a b c. CondCat (:>) c => (a :+ b :> ((a :=> c) :* (b :=> c) :=> c))
sumToFun = sumToFun' id

-- sumToFun = (inCK.fmap.fmap) unPSum (id :: a :+ b :> a :+ b)

funToSum' :: forall t a b.
             (forall c. CondCat (:>) c => t :> ((a :=> c) :* (b :=> c) :=> c))
          -> (t :> a :+ b)
funToSum' q = mkCK (return . foo)
 where
   foo :: Buses t -> Buses (a :+ b)
   foo t = PSum (mkCK r)
    where
      r :: forall c. CondCat (:>) c => (a :> c) :* (b :> c) -> CircuitM (Buses c)
      r fg = do h <- unmkCK q t
                unmkCK h fg

#if 0

q :: forall c. CondCat (:>) c => t :> ((a :=> c) :* (b :=> c) :=> c)

unmkCK q :: forall c. CondCat (:>) c => Buses t -> CircuitM (Buses ((a :=> c) :* (b :=> c) :=> c))
         :: forall c. CondCat (:>) c => Buses t -> CircuitM ((a :=> c) :* (b :=> c) :> c)

fg :: (a :> c) :* (b :> c)

unmkCK q t :: forall c. CondCat (:>) c => CircuitM ((a :=> c) :* (b :=> c) :> c)
h :: (a :=> c) :* (b :=> c) :> c
unmkCK h :: (a :> b) :* (b :> c) -> CircuitM (Buses c)
unmkCK h fg :: CircuitM (Buses c)

#endif

type CondArr a = Bool :* (a :* a) :> a
type CondFun a = forall t. (t :> Bool) -> Binop (t :> a)

condArrToFun :: CondArr a -> CondFun a
condArrToFun condArr p q r = condArr . (p &&& (q &&& r))

condFunToArr :: CondFun a -> CondArr a
condFunToArr condFun = condFun exl (exl . exr) (exr . exr)

cond' :: CondCat (:>) a => CondFun a
cond' = condArrToFun cond
-- cond' p q r = cond . (p &&& (q &&& r))

-- cond'' :: CondCat a => CondArr a
-- cond'' = condFunToArr cond'
-- -- cond'' = cond' exl (exl . exr) (exr . exr)

sumCond' :: (t :> Bool) -> Binop (t :> a :+ b)
sumCond' p q r = funToSum' (cond' p (sumToFun' q) (sumToFun' r))
-- sumCond' p q r = funToSum' (condArrToFun cond p (sumToFun' q) (sumToFun' r))
-- sumCond' p q r = funToSum' (cond . (p &&& (sumToFun' q &&& sumToFun' r)))

sumCond :: Bool :* ((a :+ b) :* (a :+ b)) :> a :+ b
sumCond = condFunToArr sumCond'
-- sumCond = sumCond' exl (exl . exr) (exr . exr)
-- sumCond = funToSum' (cond . (exl &&& (sumToFun' (exl . exr) &&& sumToFun' (exr . exr))))

-- The CondCat (:>) constraint in cond as used in 'fromBool' is what leads to CondCat in
-- PSum and hence breaks (|||). I'm looking for an alternative.

fromBool :: Bool :> Unit :+ Unit
fromBool = cond . (id &&& (inl &&& inr) . it)

toBool :: Unit :+ Unit :> Bool
toBool = constC False |||* constC True

instance CoproductCat (:>) where
  inl   = inlC
  inr   = inrC
  (|||) = error "(|||) for (:>): Sorry -- no unconstrained method yet. Use (|||*)"

instance DistribCat (:>) where
  distl = distlC
  distr = distrC

#endif

{--------------------------------------------------------------------
    Mealy machines
--------------------------------------------------------------------}

data MealyC a b = forall s. GenBuses s => MealyC (a :* s :> b :* s) s

loopC :: (a :* c :> b :* c) -> (a :> b)
loopC (C f) = C (loop (arr unPairB . f . arr (uncurry PairB)))

-- I'm getting a <<loop>> (black hole).
-- Try some experiments

#ifdef TypeDerivation
f :: KC (Buses (a :* c)) (Buses (b :* c))
arr (uncurry PairB) :: KC (Buses a :* Buses c) (Buses (a :* c))
arr unPairB :: KC (Buses (b :* c)) (Buses b :* Buses c)
arr unPairB . f . arr (uncurry PairB)
 :: KC (Buses a :* Buses c) (Buses b :* Buses c)
#endif

mealyAsArrow :: GenBuses a => MealyC a b -> (a :> b)
mealyAsArrow (MealyC f s0) = loopC (f . second (delayC s0))

unitizeMealyC :: GenBuses a => MealyC a b -> UU

#ifdef MealyToArrow
unitizeMealyC = unitize . mealyAsArrow
#else
unitizeMealyC = unitizeLoopC . preLoopC

-- Ready for loop.
data LoopC a b = forall s. GenBuses s => LoopC (a :* s :> b :* s)

-- Like mealyAsArrow but without the loopC.
preLoopC :: GenBuses a => MealyC a b -> LoopC a b
preLoopC (MealyC f s0) = LoopC (f . second (delayC s0))

unitizeLoopC :: GenBuses a => LoopC a b -> UU
unitizeLoopC (LoopC f) = undup . f' . dup
 where
   f' = (namedC "Out" *** namedC "NewState")
      . f
      . (namedC "In"  *** namedC "OldState")
   undup :: Unit :* Unit :> Unit
   undup = it

#endif

outerPrims :: [PrimName]
outerPrims = ["In","Out", "OldState","NewState","InitialState"]

isOuterPrim :: PrimName -> Bool
isOuterPrim = flip S.member (S.fromList outerPrims)

{--------------------------------------------------------------------
    Type-specific support
--------------------------------------------------------------------}

-- GenBuses needed for data types appearing the external interfaces (and hence
-- not removed during compilation).

genBusesRep' :: GenBuses (Rep a) =>
                String -> Sources -> Int -> CircuitM (Buses a,Int)
genBusesRep' prim ins o = first abstB <$> genBuses' prim ins o

bottomRep :: (HasRep a, BottomCat (:>) (Rep a)) => Unit :> a
bottomRep = abstC . bottomC

tyRep :: forall a. GenBuses (Rep a) => a -> Ty
tyRep = const (ty (undefined :: Rep a))

delayCRep :: (HasRep a, GenBuses (Rep a)) => a -> (a :> a)
delayCRep a0 = abstC . delayC (repr a0) . reprC


#if 0

-- class GenBuses a where
--   genBuses' :: String -> Sources -> Int -> CircuitM (Buses a,Int)

#define AbsTy(abs) \
instance GenBuses (Rep (abs)) => GenBuses (abs) where genBuses' = genBusesRep'

#else

#define AbsTy(abs) \
instance GenBuses (Rep (abs)) => GenBuses (abs) where \
  { genBuses' = genBusesRep' ; delayC = delayCRep ; ty = tyRep }; \
instance BottomCat (:>) (Rep (abs)) => BottomCat (:>) (abs) where \
  { bottomC = bottomRep };\
instance IfCat (:>) (Rep (abs)) => IfCat (:>) (abs) where { ifC = repIf };

#endif

AbsTy((a,b,c))
AbsTy((a,b,c,d))
AbsTy(Maybe a)
AbsTy(Either a b)
AbsTy(Pair a)
AbsTy(Vec Z a)
AbsTy(Vec (S n) a)
AbsTy(RTree.Tree Z a)
AbsTy(RTree.Tree (S n) a)
AbsTy(LTree.Tree Z a)
AbsTy(LTree.Tree (S n) a)
AbsTy(Rag.Tree LU a)
AbsTy(Rag.Tree (BU p q) a)
-- Newtypes. Alternatively, don't use them in external interfaces.
AbsTy(Sum a)
AbsTy(Product a)
