{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification, TypeSynonymInstances, GADTs #-}
{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-} -- see below
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-} -- for LU & BU
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE CPP #-}

-- For Church sum experiment
{-# LANGUAGE LiberalTypeSynonyms, ImpredicativeTypes #-}
{-# LANGUAGE ViewPatterns, TupleSections, EmptyDataDecls #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fcontext-stack=36 #-} -- for add

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

#define OptimizeCircuit

#define NoSums
-- #define StaticSums
-- #define TaggedSums
-- #define ChurchSums

module Circat.Circuit
  ( CircuitM, (:>)
  , PinId, Width, Bus(..), Source(..), GenBuses
  , namedC, constS, constC
--   , litUnit, litBool, litInt
  -- , (|||*), fromBool, toBool
  , Comp', CompNum, DGraph, circuitGraph, outGWith, outG
  , simpleComp, runC, tagged
  , systemSuccess
  ) where

import Prelude hiding (id,(.),not,and,or,curry,uncurry,sequence)
-- import qualified Prelude as P

import Data.Monoid (mempty,(<>),Sum)
import Data.Functor ((<$>))
import Control.Applicative (Applicative(..),Alternative(..),liftA2)
import Control.Arrow (arr,Kleisli(..))
import Data.Foldable (foldMap,toList)
import Data.Typeable                    -- TODO: imports
import Data.Function (on)
import Data.Coerce                      -- TODO: imports
import Unsafe.Coerce -- experiment

import qualified System.Info as SI
import System.Process (system) -- ,readProcess
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode(ExitSuccess))

import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Sequence (Seq,singleton)
import Text.Printf (printf)
import Debug.Trace (trace)

-- mtl
import Control.Monad.State (State,evalState,MonadState)
import qualified Control.Monad.State as Mtl
import Control.Monad.Writer (MonadWriter(..),WriterT,runWriterT)

import TypeUnary.Vec hiding (get)

import Circat.Misc
import Circat.Category
import Circat.Classes
import Circat.Rep
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

-- | Bus width
type Width = Int

-- Data bus: Id, bit width, prim name, arguments, output index
data Bus = Bus PinId Width

data Source = Source Bus PrimName [Source] Int

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
  show (Bus i w) = "B" ++ show i ++ ":" ++ show w

instance Show Source where
  show (Source b prim ins o) = printf "Source %s %s %s %d" (show b) (show prim) (show ins) o

newPinId :: CircuitM PinId
newPinId = do { (p:ps') <- Mtl.get ; Mtl.put ps' ; return p }

newBus :: Width -> CircuitM Bus
newBus w = flip Bus w <$> newPinId

newSource ::  Width -> String -> [Source] -> Int -> CircuitM Source
newSource w prim ins o = (\ b -> Source b prim ins o) <$> newBus w

{--------------------------------------------------------------------
    Buses representing a given type
--------------------------------------------------------------------}

-- | Typed aggregate of buses. @'Buses' a@ carries a value of type @a@.
data Buses :: * -> * where
  UnitB :: Buses Unit
  BoolB :: Source -> Buses Bool
  IntB  :: Source -> Buses Int
  PairB :: Buses a -> Buses b -> Buses (a :* b)
  FunB  :: (a :> b) -> Buses (a -> b)
  -- | Isomorphic form. Note: b must not have one of the standard forms.
  -- If it does, we'll get a run-time error when consuming.
  IsoB  :: Buses (Rep a) -> Buses a

-- -- Alternatively,
-- IsoB  :: Rep a ~ a' => Buses a' -> Buses a

#if 0
-- Equality. Easy hack: derive Eq, but say that circuits are never equal.
-- TODO: reconsider.
deriving instance Eq (Buses a)
instance Eq (a :> b) where _ == _ = False
#else
instance Eq (Buses a) where
  UnitB     == UnitB        = True
  BoolB s   == BoolB s'     = s == s'
  IntB s    == IntB s'      = s == s'
  PairB a b == PairB a' b'  = a == a' && b == b'
  IsoB r    == IsoB r'      = r == r'
  FunB _    == FunB _       = False             -- TODO: reconsider
  _         == _            = False
#endif

deriving instance Typeable Buses
-- deriving instance Show (Buses a)

-- Deriving would need GenBuses a.

instance Show (Buses a) where
  show UnitB       = "()"
  show (BoolB b)   = show b
  show (IntB b)    = show b
  show (PairB a b) = "("++show a++","++show b++")"
  show (FunB _)    = "<function>"
  show (IsoB b)    = "IsoB ("++show b++")"

-- TODO: Improve to Show instance with showsPrec

genBuses :: GenBuses b => Prim a b -> [Source] -> CircuitM (Buses b)
genBuses prim ins = fst <$> genBuses' (primName prim) ins 0

class GenBuses a where
  genBuses' :: String -> [Source] -> Int -> CircuitM (Buses a,Int)

genBus :: (Source -> Buses a) -> Width
       -> String -> [Source] -> Int -> CircuitM (Buses a,Int)
genBus wrap w prim ins o = do src <- newSource w prim ins o
                              return (wrap src,o+1)

instance GenBuses Unit where genBuses' _ _ o = return (UnitB,o)
instance GenBuses Bool where genBuses' = genBus BoolB  1
instance GenBuses Int  where genBuses' = genBus IntB  32
instance (GenBuses a, GenBuses b) => GenBuses (a :* b) where
  genBuses' prim ins o =
    do (a,oa) <- genBuses' prim ins o
       (b,ob) <- genBuses' prim ins oa
       return (PairB a b, ob)

flattenB :: String -> Buses a -> [Source]
flattenB name = flip flat []
 where
   flat :: Buses a -> Unop [Source]
   flat UnitB       = id
   flat (BoolB b)   = (b :)
   flat (IntB b)    = (b :)
   flat (PairB a b) = flat a . flat b
   flat (FunB _)    = error $ "flattenB: FunB unhandled in " ++ name
   flat (IsoB b)    = flat b

isoErr :: String -> x
isoErr nm = error (nm ++ ": IsoB")

unUnitB :: Buses Unit -> Unit
unUnitB UnitB = ()
unUnitB (IsoB _) = isoErr "unUnitB"

pairB :: Buses a :* Buses b -> Buses (a :* b)
pairB (a,b) = PairB a b

unPairB :: Buses (a :* b) -> Buses a :* Buses b
unPairB (PairB a b) = (a,b)
unPairB (IsoB _)    = isoErr "unPairB"

unFunB :: Buses (a -> b) -> (a :> b)
unFunB (FunB circ) = circ
unFunB (IsoB _) = isoErr "unFunB"

exlB :: Buses (a :* b) -> Buses a
exlB = fst . unPairB

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

-- The circuit monad:
type CircuitM = WriterT (Seq Comp) (State PinSupply)

type BCirc a b = Buses a -> CircuitM (Buses b)

-- Instantiate a 'Prim'
genComp :: GenBuses b => Prim a b -> BCirc a b
genComp prim a = do b <- genBuses prim (flattenB "genComp" a)
                    tell (singleton (Comp prim a b))
                    return b

constComp' :: GenBuses b => String -> CircuitM (Buses b)
constComp' str = genComp (Prim str) UnitB

constComp :: GenBuses b => String -> BCirc a b
constComp str = const (constComp' str)

-- TODO: eliminate constComp in favor of a more restrictive version in which a
-- == (), defined as flip genComp UnitB. Add domain flexibility in lambda-ccc
-- instead.

constM' :: (Show b, GenBuses b) => b -> CircuitM (Buses b)
constM' b = constComp' (show b)

constM :: (Show b, GenBuses b) => b -> BCirc a b
constM b = constComp (show b)

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

mkCK :: BCirc a b -> (a :> b)
mkCK = C . Kleisli

unmkCK :: (a :> b) -> BCirc a b
unmkCK = runKleisli . unC

inCK :: (BCirc a a' -> BCirc b b')
     -> ((a :> a') -> (b :> b'))
inCK = mkCK <~ unmkCK

inCK2 :: (BCirc a a' -> BCirc b b' -> BCirc c c')
      -> ((a :> a') -> (b :> b') -> (c :> c'))
inCK2 = inCK <~ unmkCK

primC :: GenBuses b => Prim a b -> a :> b
primC = mkCK . genComp

namedC :: GenBuses b => String -> a :> b
-- namedC = primC . Prim
namedC name = namedOpt name noOpt

type Opt b = [Source] -> CircuitM (Maybe (Buses b))

just :: Applicative f => a -> f (Maybe a)
just = pure . Just

nothing :: Applicative f => f (Maybe a)
nothing = pure Nothing

newComp :: (a :> b) -> Buses a -> CircuitM (Maybe (Buses b))
newComp cir = fmap Just . unmkCK cir

newComp1 :: SourceToBuses a => (a :> b) -> Source -> CircuitM (Maybe (Buses b))
newComp1 cir a = newComp cir (toBuses a)

newComp2 :: (SourceToBuses a, SourceToBuses b) =>
            (a :* b :> c) -> Source -> Source -> CircuitM (Maybe (Buses c))
newComp2 cir a b = newComp cir (PairB (toBuses a) (toBuses b))

newComp3 :: (SourceToBuses a, SourceToBuses b, SourceToBuses c) =>
            ((a :* b) :* c :> d) -> Source -> Source -> Source -> CircuitM (Maybe (Buses d))
newComp3 cir a b c = newComp cir (PairB (PairB (toBuses a) (toBuses b)) (toBuses c))

newVal :: (Show b, GenBuses b) => b -> CircuitM (Maybe (Buses b))
newVal b = Just <$> constM' b

noOpt :: Opt b
noOpt = const nothing

orOpt :: Binop (Opt b)

orOpt f g a = do mb <- f a
                 case mb of
                   Nothing -> g a
                   Just _  -> return mb

namedOpt :: GenBuses b => String -> Opt b -> a :> b
#ifdef OptimizeCircuit
namedOpt name opt =
  mkCK $ \ a -> opt (flattenB "namedOpt" a) >>= maybe (genComp (Prim name) a) return
#else
namedOpt name _ = mkCK (genComp (Prim name))
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

pureC :: Buses b -> a :> b
pureC = mkCK . pure . pure

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

exrB :: Buses (a :* b) -> Buses b
exrB = snd . unPairB

onPairBM :: Functor m =>
            (Buses a :* Buses b -> m (Buses a' :* Buses b'))
         -> (Buses (a :* b) -> m (Buses (a' :* b')))
onPairBM f = fmap pairB . f . unPairB

crossB :: Applicative m =>
          (Buses a -> m (Buses c)) -> (Buses b -> m (Buses d))
       -> (Buses (a :* b) -> m (Buses (c :* d)))
crossB f g = (\ (a,b) -> liftA2 PairB (f a) (g b)) . unPairB

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

#ifdef TypeDerivation

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

-- instance BoolCat (:>) where
--   not = namedC "not"
--   and = namedC "and"
--   or  = namedC "or"
--   xor = namedC "xor"

pattern ConstS name <- Source _ name [] 0
pattern Val x     <- ConstS (reads -> [(x,"")])

pattern TrueS    <- ConstS "True"
pattern FalseS   <- ConstS "False"
pattern NotS a   <- Source _ "not" [a] 0
pattern XorS a b <- Source _ "xor" [a,b] 0

class SourceToBuses a where toBuses :: Source -> Buses a
instance SourceToBuses Bool where toBuses = BoolB
instance SourceToBuses Int  where toBuses = IntB

sourceB :: SourceToBuses a => Source -> CircuitM (Maybe (Buses a))
sourceB = just . toBuses

instance BoolCat (:>) where
  not = namedOpt "not" $ \ case
          [NotS a]     -> sourceB a
          [Val x]      -> newVal (not x)
          _            -> nothing
  and = namedOpt "and" $ \ case
          [TrueS ,y]   -> sourceB y
          [x,TrueS ]   -> sourceB x
          [x@FalseS,_] -> sourceB x
          [_,y@FalseS] -> sourceB y
          _            -> nothing
  or  = namedOpt "or"  $ \ case
          [FalseS,y]   -> sourceB y
          [x,FalseS]   -> sourceB x
          [x@TrueS ,_] -> sourceB x
          [_,y@TrueS ] -> sourceB y
          _            -> nothing
  xor = namedOpt "xor" $ \ case
          [FalseS,y]   -> sourceB y
          [x,FalseS]   -> sourceB x
          [TrueS,y ]   -> newComp1 not y
          [x,TrueS ]   -> newComp1 not x
          _            -> nothing

-- TODO: After I have more experience with these graph optimizations, reconsider
-- the interface.

-- instance NumCat (:>) Int  where { add = namedC "add" ; mul = namedC "mul" }

pattern ZeroS <- ConstS "0"
pattern OneS  <- ConstS "1"

instance NumCat (:>) Int where
 add = namedOpt "add" $ \ case
         [Val x, Val y] -> newVal (x+y)
         [ZeroS,y]      -> sourceB y
         [x,ZeroS]      -> sourceB x
         _              -> nothing
 mul = namedOpt "mul" $ \ case
         [Val x, Val y] -> newVal (x*y)
         [OneS ,y]      -> sourceB y
         [x,OneS ]      -> sourceB x
         [x@ZeroS,_]    -> sourceB x
         [_,y@ZeroS]    -> sourceB y
         _              -> nothing

-- TODO: Some optimizations drop results. Make another pass to remove unused
-- components (recursively).

-- muxC :: IsSourceP c => Bool :* (c :* c) :> c
-- muxC = namedC "mux"

#if 1

-- Simplifications for all types:
-- 
--   mux (False,(a,_))     = a
--   mux (True ,(_,b))     = b
--   mux (_    ,(a,a))     = a
--
-- Simplifications for Bool values:
-- 
--   mux (c,(False,True))  = c
--   mux (c,(True,False))  = c
--   mux (a,(False,b))     = a && b
--   mux (a,(b ,True))     = a || b
--   mux (a,(b,False))     = not a && b
--   mux (a,(True,b ))     = not a || b
--   mux (c,(a,not a))     = c `xor` a
--   mux (c,(not a,a))     = c `xor` not a
--   mux (b,(a,c `xor` a)) = (b && c) `xor` a

muxOpt :: SourceToBuses a => Opt a
muxOpt = \ case
  [FalseS,a,_]       -> sourceB a
  [ TrueS,_,b]       -> sourceB b
  [_,a,a'] | a == a' -> sourceB a
  _                  -> nothing

#define Eql(x) ((==(x)) -> True)

muxOptB :: Opt Bool
muxOptB = \ case
  [c,FalseS,TrueS]            -> sourceB c
  [c,TrueS,FalseS]            -> newComp1 not c
  [a,FalseS,b]                -> newComp2 and a b
  [a,b,TrueS ]                -> newComp2 or  a b
  [a,b,FalseS]                -> newComp2 (and . first not) a b -- not a && b
  [a,TrueS ,b]                -> newComp2 (or  . first not) a b -- not a || b
  [c,a,NotS a']     | a == a' -> newComp2 xor c a
  [c,b@(NotS a),a'] | a == a' -> newComp2 xor c b
  [b,a,c `XorS` a'] | a == a' -> newComp3 andXor b c a
  _                           -> nothing

-- andXor ((b,c),a) = (b && c) `xor` a
andXor :: ((Bool :* Bool) :* Bool) :> Bool
andXor = xor . first and

#if 0

-- Alternative notation:

#define Sat(pred) ((pred) -> True)
#define Eql(x) Sat(==(x))

muxOpt (_ ,(a,Eql(a))) = just $ wrap a

#endif

-- orOpt

instance MuxCat (:>) where
  muxB = namedOpt "mux" (muxOpt `orOpt` muxOptB)
  muxI = namedOpt "mux" muxOpt

#else

-- instance GenBuses t => HasIf (:>) t where
--   ifA = namedC "mux"

-- or

instance IfCat (:>) Bool where ifA = namedC "mux"
instance IfCat (:>) Int  where ifA = namedC "mux32"

instance (IfCat (:>) a, IfCat (:>) b) => IfCat (:>) (a :* b) where
  ifA = prodIf

instance IfCat (:>) b => IfCat (:>) (a -> b) where
  ifA = funIf

#endif

instance GenBuses a => Show (a :> b) where
  show = show . runC

--     Application is no smaller than the instance head
--       in the type family application: RepT :> a
--     (Use -XUndecidableInstances to permit this)

evalWS :: WriterT o (State s) b -> s -> (b,o)
evalWS w s = evalState (runWriterT w) s

-- Turn a circuit into a list of components, including fake In & Out.
runC :: GenBuses a => (a :> b) -> [Comp]
runC = runU . unitize

runU :: (Unit :> Unit) -> [Comp]
runU cir = toList (exr (evalWS (unmkCK cir UnitB) (PinId <$> [0 ..])))

-- Wrap a circuit with fake input and output
unitize :: GenBuses a => (a :> b) -> (Unit :> Unit)
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
       _ -> printf "command \"%s\" failed.\n" cmd

outG :: GenBuses a => String -> (a :> b) -> IO ()
outG = outGWith ("pdf","")

-- Some options:
-- 
-- ("pdf","")
-- ("svg","")
-- ("png","-Gdpi=200")
-- ("jpg","-Gdpi=200")

outGWith :: GenBuses a => (String,String) -> String -> (a :> b) -> IO ()
outGWith (outType,res) name circ = 
  do createDirectoryIfMissing False outDir
     -- writeFile (outFile "graph") (show (simpleComp <$> runC circ))
     -- putStrLn "outGWith: here goes!!"
     -- printf "Circuit: %d components\n" (length (runC circ))
     -- print (simpleComp <$> runC circ)
     writeFile (outFile "dot") (circuitDot name circ)
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

-- TODO: Instead of failing, emit a message about the generated file. Perhaps
-- simply use "echo".

type DGraph = [Comp']

type Dot = String

circuitGraph :: GenBuses a => (a :> b) -> DGraph
circuitGraph = map simpleComp . tagged . runC

graphDot :: String -> DGraph -> Dot
graphDot name comps = printf "digraph %s {\n%s}\n" (tweak <$> name)
                        (concatMap wrap (prelude ++ recordDots comps))
 where
   prelude = [ "rankdir=LR"
             , "node [shape=Mrecord]"
             , "bgcolor=transparent"
             , "ratio=1"
             --, "ranksep=1"
             -- , fixedsize=true
             ]
   wrap  = ("  " ++) . (++ ";\n")
   tweak '-' = '_'
   tweak c   = c

circuitDot :: GenBuses a => String -> (a :> b) -> Dot
circuitDot name circ = graphDot name (circuitGraph circ)

type Statement = String

type Input  = Bus
type Output = Bus

type Comp' = (Int,String,[Input],[Output])

simpleComp :: (Int,Comp) -> Comp'
simpleComp (compNum, Comp prim a b) = (compNum, name, flat a, flat b)
 where
   name = show prim
   flat :: forall t. Buses t -> [Bus]
   flat = map sourceBus . flattenB name

data Dir = In | Out deriving Show
type PortNum = Int
type CompNum = Int

tagged :: [a] -> [(Int,a)]
tagged = zip [0 ..]

recordDots :: [Comp'] -> [Statement]
recordDots comps = nodes ++ edges
 where
   nodes = node <$> comps
    where
      node :: Comp' -> String
      -- -- drop if no ins or outs
      -- node (_,prim,[],[]) = "// removed disconnected " ++ prim
      node (nc,prim,ins,outs) =
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
      compEdges (snkComp,_,ins,_) = edge <$> tagged ins
       where
         edge (ni, Bus i width) =
           printf "%s -> %s %s"
             (port Out (srcMap M.! i)) (port In (width,snkComp,ni)) (label width)
          where
            label 1 = ""
            label w = printf "[label=\"%d\",fontsize=10]" w
--          edge (ni, BoolS x) = litComment ni x
--          edge (ni, IntS  x) = litComment ni x
         litComment :: Show a => CompNum -> a -> String
         litComment ni x = "// "  ++ show x ++ " -> " ++ port In (0,snkComp,ni)
   port :: Dir -> (Width,CompNum,PortNum) -> String
   -- TODO: Use the width, perhaps to label the arrows
   port dir (_w,nc,np) = printf "%s:%s" (compLab nc) (portLab dir np)
   compLab nc = 'c' : show nc

-- showBool :: Bool -> String
-- showBool False = "F"
-- showBool True  = "T"

-- Map each pin to its width, source component and output port numbers
type SourceMap = Map PinId (Width,CompNum,PortNum)

-- TODO: Try removing width.

-- data SourceInfo = BusInfo Width CompNum PortNum
--                 | LitInfo String

sourceMap :: [Comp'] -> SourceMap
sourceMap = foldMap $ \ (nc,_,_,outs) ->
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

type CircuitM = WriterT (Seq Comp) (State PinSupply)

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

type BusSum a b = ()

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
    Type-specific support
--------------------------------------------------------------------}

-- GenBuses needed for data types appearing the external interfaces (and hence
-- not removed during compilation).

#if 1

#define AbsTy(abs) \
instance GenBuses (Rep (abs)) => GenBuses (abs) where \
  genBuses' prim ins o = \
    first abstB <$> (genBuses' prim ins o :: CircuitM (Buses (Rep (abs)),Int))

#else

#define AbsTy(abs) \
instance GenBuses (Rep (abs)) => GenBuses (abs) where \
 { genBuses' prim ins o = \
    first abstB <$> (genBuses' prim ins o :: CircuitM (Buses (Rep (abs)),Int)) }; \
instance IfCat (:>) (Rep (abs)) => IfCat (:>) (abs) where { ifA = repIf }

#endif

AbsTy((a,b,c))
AbsTy((a,b,c,d))
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
AbsTy(Sum Int)
