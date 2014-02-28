{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification, TypeSynonymInstances, GADTs #-}
{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-} -- see below
{-# LANGUAGE CPP #-}

-- For Church sum experiment
{-# LANGUAGE LiberalTypeSynonyms, ImpredicativeTypes #-}
{-# LANGUAGE ViewPatterns, TupleSections, EmptyDataDecls #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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

-- #define StaticSums
-- #define TaggedSums
#define ChurchSums

module Circat.Circuit 
  ( CircuitM, (:>)
  , Pin, Pins, IsSourceP, IsSourceP2, namedC, constS, constC
#if defined TaggedSums
  , inlC, inrC, (|||*)
#elif defined ChurchSums
  , (|||*), fromBool, toBool
#endif
  , muxC -- , pinsAsCirc
  , Comp', CompNum, toG, outGWith, outG
  , simpleComp, runC, tagged
  ) where

import Prelude hiding (id,(.),const,not,and,or,curry,uncurry,sequence)
import qualified Prelude as P

import Data.Monoid (mempty,(<>))
import Data.Functor ((<$>))
-- import Control.Applicative (pure,liftA2)
import Control.Monad (liftM,liftM2)
import Control.Arrow (arr,Kleisli(..))
import Data.Foldable (foldMap,toList)
-- import Data.Traversable (Traversable(..))

import qualified System.Info as SI
import System.Process (system) -- ,readProcess
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode(ExitSuccess))

import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Sequence (Seq,singleton)
#ifdef TaggedSums
import qualified Data.Sequence as Seq
#endif
import Text.Printf (printf)

-- mtl
import Control.Monad.State (State,evalState,MonadState)
import qualified Control.Monad.State as Mtl
import Control.Monad.Writer (MonadWriter(..),WriterT,runWriterT)

import TypeUnary.Vec hiding (get)
-- import FunctorCombo.StrictMemo (HasTrie(..),(:->:),idTrie)

import Circat.Misc
import Circat.Category
-- import Circat.State (StateCat(..),StateCatWith,StateFun,StateExp)
import Circat.Classes
import Circat.Pair
import Circat.RTree

{--------------------------------------------------------------------
    The circuit monad
--------------------------------------------------------------------}

-- Primitive (stub)
newtype Prim a b = Prim String

instance Show (Prim a b) where show (Prim str) = str

-- Component: primitive instance with inputs & outputs
data Comp = forall a b. IsSource2 a b => Comp (Prim a b) a b

deriving instance Show Comp

-- The circuit monad:
type CircuitM = WriterT (Seq Comp) (State PinSupply)

newtype Pin = Pin Int deriving (Eq,Ord,Show,Enum)
type PinSupply = [Pin]

type MonadPins = MonadState PinSupply

newPin :: MonadPins m => m Pin
newPin = do { (p:ps') <- Mtl.get ; Mtl.put ps' ; return p }

-- runCircuitM :: CircuitM a -> PinSupply -> (a,PinSupply)
-- runCircuitM 

{--------------------------------------------------------------------
    Pins
--------------------------------------------------------------------}

sourcePins :: forall a. IsSource a => a -> [Pin]
sourcePins s = toList (toPins s)

-- | Give a representation for a type in terms of structures of pins.
class Show a => IsSource a where
  toPins    :: a -> Seq Pin
  genSource :: MonadPins m => m a
#ifdef TaggedSums
  numPins   :: a -> Int
#endif

-- Instantiate a 'Prim'
genComp :: forall a b. IsSource2 a b =>
           Prim a b -> a -> CircuitM b
genComp prim a = do b <- genSource
                    tell (singleton (Comp prim a b))
                    return b

constComp :: forall a b. IsSource b =>
             String -> a -> CircuitM b
constComp str _ = do b <- genSource
                     tell (singleton (Comp (Prim str) () b))
                     return b

constM :: (Show q, IsSource b) =>
          q -> a -> CircuitM b
constM q = constComp (show q)

type IsSource2 a b = (IsSource a, IsSource b)

instance IsSource () where
  toPins () = mempty
  genSource = return ()
#ifdef TaggedSums
  numPins _ = 0
#endif

instance IsSource Pin where
  toPins p  = singleton p
  genSource = newPin
#ifdef TaggedSums
  numPins _ = 1
#endif

instance IsSource2 a b => IsSource (a :* b) where
  toPins (sa,sb) = toPins sa <> toPins sb
  genSource      = liftM2 (,) genSource genSource
#ifdef TaggedSums
  numPins ~(a,b) = numPins a + numPins b
#endif

-- instance IsSource (a :+ b) where ... ???

instance (IsNat n, IsSource a) => IsSource (Vec n a) where
  toPins    = foldMap toPins
  genSource = genSourceV nat
#ifdef TaggedSums
  numPins _ = natToZ (nat :: Nat n) * numPins (undefined :: a)
#endif

genSourceV :: (MonadPins m, IsSource a) => Nat n -> m (Vec n a)
genSourceV Zero     = return ZVec
genSourceV (Succ n) = liftM2 (:<) genSource (genSourceV n)

instance IsSource a => IsSource (Pair a) where
  toPins    = foldMap toPins
  genSource = liftM toPair genSource
#ifdef TaggedSums
  numPins _ = 2 * numPins (undefined :: a)
#endif

instance (IsNat n, IsSource a) => IsSource (Tree n a) where
  toPins    = foldMap toPins
  genSource = genSourceT nat
#ifdef TaggedSums
  numPins _ = 2 ^ (natToZ (nat :: Nat n) :: Int) * numPins (undefined :: a)
#endif

genSourceT :: (MonadPins m, IsSource a) => Nat n -> m (Tree n a)
genSourceT Zero     = liftM L genSource
genSourceT (Succ _) = liftM B genSource

-- TODO: does the recounting of nat lead to quadratic work?
-- Perhaps rewrite, using the Succ argument.

{--------------------------------------------------------------------
    Pins representing a given type
--------------------------------------------------------------------}

type family Pins a

type instance Pins Bool = Pin

-- Distribute over product-based structures:
type instance Pins ()         = ()
type instance Pins (a :* b)   = Pins a :* Pins b
type instance Pins (Pair a  ) = Pair (Pins a)
type instance Pins (Vec n a ) = Vec  n (Pins a)
type instance Pins (Tree n a) = Tree n (Pins a)

-- See below for function instance

{--------------------------------------------------------------------
    Circuit category
--------------------------------------------------------------------}

infixl 1 :>, :+>

-- | Internal representation for '(:>)'.
type a :+> b = Kleisli CircuitM (Pins a) (Pins b)

-- | Circuit category
newtype a :> b = C { unC :: a :+> b }

type IsSourceP a = IsSource (Pins a)

type IsSourceP2 a b = (IsSourceP a, IsSourceP b)

mkC :: (Pins a -> CircuitM (Pins b)) -> (a :> b)
mkC = C . Kleisli

unmkC :: (a :> b) -> (Pins a -> CircuitM (Pins b))
unmkC = runKleisli . unC

inCK :: ((Pins a -> CircuitM (Pins b)) -> (Pins a' -> CircuitM (Pins b')))
     -> ((a :> b) -> (a' :> b'))
inCK = mkC <~ unmkC

primC :: IsSourceP2 a b => Prim (Pins a) (Pins b) -> a :> b
primC = mkC . genComp

namedC :: IsSourceP2 a b => String -> a :> b
namedC = primC . Prim

-- | Constant circuit from source generator (experimental)
constSM :: CircuitM (Pins b) -> (a :> b)
constSM mkB = mkC (const mkB)

-- | Constant circuit from source
constS :: Pins b -> (a :> b)
constS b = constSM (return b)

-- constS b = C (const b)

-- TODO: Rename "pins", which doesn't fit with exponentials.

-- TODO: Consolidate forms of constant circuits

-- constC :: (IsSource2 a b, Show b) => b -> a :> b
-- constC :: (IsSource2 a (Pins b), Show b) => b -> a :> Pins b
-- constC b = namedC (show b)

constC :: (IsSourceP b, Show b) => b -> a :> b
constC = mkC . constM
-- constC b = mkC (constComp (show b))

-- General mux. Later specialize to simple muxes and make more of them.

-- muxC :: (IsSource2 ((k :->: v) :* k) v, HasTrie k) =>
--         ((k :->: v) :* k) :> v
-- muxC = namedC "mux"

-- muxC :: -- (IsSource2 ((k :->: v) :* k) v, HasTrie k) =>
--         ((k :->: v) :* k) :> v
-- muxC = error "muxC: not implemented"

-- instance ConstCat (:>) where
--   type ConstKon (:>) a b = () -- (IsSource2 a b, Show b)
--   const = constC

-- TODO: Kleisli already defines an ConstCat instance, and it doesn't use
-- constC. Can it work for (:>)?

-- instance Newtype (a :> b) (Pins a -> CircuitM (Pins b)) where
--   pack   = C
--   unpack = unC
-- 
--     Illegal type synonym family application in instance.
--
-- So define manually:

inC :: (a :+> b -> a' :+> b') -> (a :> b -> a' :> b')
inC = C <~ unC

inC2 :: (a :+> b -> a' :+> b' -> a'' :+> b'')
     -> (a :>  b -> a' :>  b' -> a'' :>  b'')
inC2 = inC <~ unC

instance Category (:>) where
  id  = C id
  (.) = inC2 (.)

instance ProductCat (:>) where
  exl   = C exl
  exr   = C exr
  dup   = C dup
  (***) = inC2 (***)
  (&&&) = inC2 (&&&)

-- #define UnwrappedExp

-- pinsAsCirc :: Pins (a -> b) -> a :> b

#ifdef UnwrappedExp

type instance Pins (a -> b) = a :+> b

instance ClosedCat (:>) where
  apply   =   C applyK
  curry   = inC curryK
  uncurry = inC uncurryK

-- pinsAsCirc = C

#else

type instance Pins (a -> b) = a :> b

-- With this version, the methods are trickier, but the result is more easily
-- usable, since we export (:>) and not the underlying (:+>) representation.

instance ClosedCat (:>) where
  apply   = C (applyK . first (arr unC))
  curry   = inC $ \ h -> arr C . curryK h
  uncurry = inC $ \ f -> uncurryK (arr unC . f)

-- pinsAsCirc = id

#endif

{- Types:

Abbreviations:

> type KC = Kleisli CircuitM
> type S = Source

Consider `Source`- specialized versions of `KC`:

> applyK   :: KC (Exp KC (S a) (S b) :* S a) (S b)
>          == KC (KC (S a) (S b) :* S a) (S b)
>          == KC ((a :+> b) :* S a) (S b)
>          =~ KC ((a :> b) :* S a) (S b)
>          == KC (S (a -> b) :* S a) (S b)
>          == KC (S ((a -> b) :* a)) (S b)
>          == ((a -> b) :* a) :+> b
>
> curryK   :: KC (S a :* S b) (S c) -> KC (S a) (Exp KC (S b) (S c))
>          == KC (S a :* S b) (S c) -> KC (S a) (KC (S b) (S c))
>          == KC (S a :* S b) (S c) -> KC (S a) (b :+> c)
>          =~ KC (S a :* S b) (S c) -> KC (S a) (b :> c)
>          == KC (S (a :* b)) (S c) -> KC (S a) (S (b -> c))
>          == ((a :* b) :+> c) -> (a :+> (b -> c))
>
> uncurryK :: KC (S a) (Exp KC (S b) (S c)) -> KC (S a :* S b) (S c)
>          == KC (S a) (KC (S b) (S c)) -> KC (S a :* S b) (S c)
>          == KC (S a) (b :+> c) -> KC (S a :* S b) (S c)
>          =~ KC (S a) (b :> c) -> KC (S a :* S b) (S c)
>          == KC (S a) (S (b -> c)) -> KC (S (a :* b)) (S c)
>          == (a :+> Exp (:>) (b -> c)) -> ((a :* b) :+> c)

-}

muxC :: IsSourceP c => Bool :* (c :* c) :> c
muxC = namedC "mux"

instance TerminalCat (:>) where
  it = C it

instance ConstCat (:>) where
  type ConstKon (:>) a b = (Show b, IsSourceP2 a b)
  const = constC

instance PairCat (:>) where
  toPair = C toPair
  unPair = C unPair

instance BoolCat (:>) where
  not = namedC "not"
  and = namedC "and"
  or  = namedC "or"
  xor = namedC "xor"

instance EqCat (:>) where
  type EqKon (:>) a = IsSource (Pins a)
  eq  = namedC "eq"
  neq = namedC "neq"

instance AddCat (:>) where
  -- TODO: Try with and without these non-defaults
--   fullAdd = namedC "fullAdd"
--   halfAdd = namedC "halfAdd"

instance VecCat (:>) where
  toVecZ = C toVecZ
  unVecZ = C unVecZ
  toVecS = C toVecS
  unVecS = C unVecS

instance TreeCat (:>) where
  toL = C toL
  unL = C unL
  toB = C toB
  unB = C unB

instance IsSourceP2 a b => Show (a :> b) where
  show = show . runC

--     Application is no smaller than the instance head
--       in the type family application: RepT :> a
--     (Use -XUndecidableInstances to permit this)

evalWS :: WriterT o (State s) b -> s -> (b,o)
evalWS w s = evalState (runWriterT w) s

-- Turn a circuit into a list of components, including fake In & Out.
runC :: IsSourceP2 a b => (a :> b) -> [Comp]
runC = runU . unitize

runU :: (Unit :> Unit) -> [Comp]
runU cir = toList (exr (evalWS (unmkC cir ()) (Pin <$> [0 ..])))

-- Wrap a circuit with fake input and output
unitize :: IsSourceP2 a b => (a :> b) -> (Unit :> Unit)
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
       _ -> printf "command \"%s\" failed."

outG :: IsSourceP2 a b => String -> (a :> b) -> IO ()
outG = outGWith ("pdf","")

-- Some options:
-- 
-- ("pdf","")
-- ("svg","")
-- ("png","-Gdpi=200")
-- ("jpg","-Gdpi=200")

outGWith :: IsSourceP2 a b => (String,String) -> String -> (a :> b) -> IO ()
outGWith (outType,res) name circ = 
  do createDirectoryIfMissing False outDir
     writeFile (outFile "dot") (toG circ)
     systemSuccess $
       printf "dot %s -T%s %s -o %s" res outType (outFile "dot") (outFile outType)
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

type DGraph = String

toG :: IsSourceP2 a b => (a :> b) -> DGraph
toG cir = printf "digraph {\n%s}\n"
            (concatMap wrap (prelude ++ recordDots comps))
 where
   prelude = ["rankdir=LR","node [shape=Mrecord]"{-, "ranksep=1"-}, "ratio=1"] -- maybe add fixedsize=true
   comps = simpleComp <$> runC cir
   wrap  = ("  " ++) . (++ ";\n")

type Statement = String

type Inputs  = [Pin]
type Outputs = [Pin]

type Comp' = (String,Inputs,Outputs)

simpleComp :: Comp -> Comp'
simpleComp (Comp prim a b) = (show prim, sourcePins a, sourcePins b)

data Dir = In | Out deriving Show
type PortNum = Int
type CompNum = Int

tagged :: [a] -> [(Int,a)]
tagged = zip [0 ..]

recordDots :: [Comp'] -> [Statement]
recordDots comps = nodes ++ edges
 where
   ncomps :: [(CompNum,Comp')] -- numbered comps
   ncomps = tagged comps
   nodes = node <$> ncomps
    where
      node (nc,(prim,ins,outs)) =
        printf "%s [label=\"{%s%s%s}\"]" (compLab nc) 
          (ports "" (labs In ins) "|") prim (ports "|" (labs Out outs) "")
       where
         ports _ "" _ = ""
         ports l s r = printf "%s{%s}%s" l s r
         labs dir bs = intercalate "|" (portSticker . exl <$> tagged bs)
          where
            -- portSticker = bracket . portLab dir
            portSticker p = bracket (portLab dir p) {- ++ show p -} -- show p for port # debugging
   bracket = ("<"++) . (++">")
   portLab :: Dir -> PortNum -> String
   portLab dir np = printf "%s%d" (show dir) np
   srcMap = sourceMap ncomps
   edges = concatMap compEdges ncomps
    where
      compEdges (snkComp,(_,ins,_)) = edge <$> tagged ins
       where
         edge (ni,i) = printf "%s -> %s" (port Out (srcMap M.! i)) (port In (snkComp,ni))
   port :: Dir -> (CompNum,PortNum) -> String
   port dir (nc,np) = printf "%s:%s" (compLab nc) (portLab dir np)
   compLab nc = 'c' : show nc

-- Map each pin to its source component and output port numbers
type SourceMap = Map Pin (CompNum,PortNum)

sourceMap :: [(CompNum,Comp')] -> SourceMap
sourceMap = foldMap $ \ (nc,(_,_,outs)) ->
              M.fromList [(b,(nc,np)) | (np,b) <- tagged outs ]

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

--     Could not deduce (IsSource (Pins b),
--                       IsSource (Pins a),
--                       IsSource (Pins (Trie a b)))
--       arising from a use of `muxC'

{-
newtype a :> b = Circ (Kleisli CircuitM (Pins a) (Pins b))

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

type instance Unpins Pin = Bool

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

#if defined StaticSums

type instance Pins (a :+ b) = Pins a :+ Pins b

instance CoproductCat (:>) where
  inl   = C inl
  inr   = C inr
  (|||) = inC2 (|||)
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

data a :++ b = UP { sumPins :: Seq Pin, sumFlag :: Pin } deriving Show

type instance Pins (a :+ b) = Pins a :++ Pins b

instance IsSource2 a b => IsSource (a :++ b) where
  toPins (UP ps f) = ps <> singleton f
  genSource =
    liftM2 UP (Seq.replicateM (numPins (undefined :: (a :++ b)) - 1) newPin)
              newPin
  numPins _ =
    (numPins (undefined :: a) `max` numPins (undefined :: b)) + 1

unsafeInject :: forall q a b. (IsSourceP q, IsSourceP2 a b) =>
                Bool -> q :> a :+ b
unsafeInject flag = mkC $ \ q ->
  do x <- constM flag q
     let nq  = numPins (undefined :: Pins q)
         na  = numPins (undefined :: Pins a)
         nb  = numPins (undefined :: Pins b)
         pad = Seq.replicate (max na nb - nq) x
     return (UP (toPins q <> pad) x)

inlC :: IsSourceP2 a b => a :> a :+ b
inlC = unsafeInject False

inrC :: IsSourceP2 a b => b :> a :+ b
inrC = unsafeInject True

infixr 2 |||*

{-
(|||*) :: (IsSourceP2 a b, IsSourceP c) =>
          (a :> c) -> (b :> c) -> (a :+ b :> c)
f |||* g = muxC . ((f *** g) . extractBoth &&& pureC sumFlag)

cond :: IsSource (Pins c) => ((c :* c) :* Bool) :> c
cond = muxCT . first toPair

muxCT :: (IsSourceP2 ((u :->: v) :* u) v, HasTrie u) =>
         ((u :->: v) :* u) :> v
muxCT = namedC "mux"
-}

(|||*) :: (IsSourceP2 a b, IsSourceP c) =>
          (a :> c) -> (b :> c) -> (a :+ b :> c)
f |||* g = muxC . (pureC sumFlag &&& (f *** g) . extractBoth)

-- TODO: Reduce muxC to several one-bit muxes.

-- unsafeExtract :: IsSource (Pins c) => a :+ b :> c
-- unsafeExtract = pureC (pinsSource . sumPins)

extractBoth :: IsSourceP2 a b => a :+ b :> a :* b
extractBoth = pureC ((pinsSource &&& pinsSource) . sumPins)

pinsSource :: IsSource a => Seq Pin -> a
pinsSource pins = Mtl.evalState genSource (toList pins)

pureC :: (Pins a -> Pins b) -> (a :> b)
pureC = C . arr

-- TODO: Generalize CoproductCat to accept constraints like IsSourceP, and then
-- move inlC, inrC, (|||*) into a CoproductCat instance. Tricky.

#elif defined ChurchSums

{--------------------------------------------------------------------
    Yet another sum experiment: Church encoding
--------------------------------------------------------------------}

type instance Pins (a :+ b) = PSum a b

newtype PSum a b =
  PSum { unPSum :: forall c. CondCat (:>) c => (a :=> c) :* (b :=> c) :> c }

psc :: (forall c. CondCat (:>) c => (a :> c) :* (b :> c) -> CircuitM (Pins c)) -> PSum a b
psc q = PSum (mkC q)

unPsc :: PSum a b -> (forall c. CondCat (:>) c => (a :> c) :* (b :> c) -> CircuitM (Pins c))
unPsc ps = unmkC (unPSum ps)

inlC :: a :> a :+ b
inlC = mkC (\ a -> return (psc (\ (f,_) -> unmkC f a)))

inrC :: b :> a :+ b
inrC = mkC (\ b -> return (psc (\ (_,g) -> unmkC g b)))

infixr 2 |||*

(|||*) :: forall a b c. CondCat (:>) c =>
          (a :> c) -> (b :> c) -> (a :+ b :> c)
f |||* g = mkC (\ q -> unPsc q (f,g))

distlC :: forall u a b. (u :* (a :+ b)) :> (u :* a :+ u :* b)
distlC = mkC (\ (u,q) -> return (psc (\ (f,g) -> unPsc q (injl u f, injl u g))))

{-
u :: Pins u
q :: Pins (a :+ b)
  == PSum a b
unPSum q :: forall c. CondCat (:>) c => (a :> c) :* (b :> c) -> CircuitM (Pins c)

f :: u :* a :> c
g :: u :* b :> c

injl u f :: a :> c
injl u g :: b :> c

unPSum q (injl u f) (injl v f) :: CircuitM (Pins c)

-}

distrC :: forall v a b. ((a :+ b) :* v) :> (a :* v :+ b :* v)
distrC = mkC (\ (q,v) -> return (psc (\ (f,g) -> unPsc q (injr v f, injr v g))))

injl :: Pins u -> (u :* a :> c) -> (a :> c)
injl u = inCK (. (u,))

injr :: Pins v -> (a :* v :> c) -> (a :> c)
injr v = inCK (. (,v))

-- (. (u,)) :: (Pins (u :* a) -> CircuitM (Pins c)) -> (Pins a -> CircuitM (Pins c))
-- inCK (. (u,)) :: (u :* a : c) -> (a :> c)

instance                        CondCat (:>) Unit      where cond = it
instance                        CondCat (:>) Bool      where cond = muxC
instance (CondCat2 (:>) a b) => CondCat (:>) (a :*  b) where cond = prodCond
instance (CondCat (:>) b)    => CondCat (:>) (a :=> b) where cond = funCond
instance CondCat (:>) (a :+ b)                         where cond = sumCond

sumToFun' :: (t :> a :+ b)
          -> forall c. CondCat (:>) c => t :> ((a :=> c) :* (b :=> c) :=> c)
sumToFun' = (inCK.fmap.fmap) unPSum

sumToFun :: forall a b c. CondCat (:>) c => (a :+ b :> ((a :=> c) :* (b :=> c) :=> c))
sumToFun = sumToFun' id

-- sumToFun = (inCK.fmap.fmap) unPSum (id :: a :+ b :> a :+ b)

funToSum' :: forall t a b.
             (forall c. CondCat (:>) c => t :> ((a :=> c) :* (b :=> c) :=> c))
          -> (t :> a :+ b)
funToSum' q = mkC (return . foo)
 where
   foo :: Pins t -> Pins (a :+ b)
   foo t = PSum (mkC r)
    where
      r :: forall c. CondCat (:>) c => (a :> c) :* (b :> c) -> CircuitM (Pins c)
      r fg = do h <- unmkC q t
                unmkC h fg

#if 0

q :: forall c. CondCat (:>) c => t :> ((a :=> c) :* (b :=> c) :=> c)

unmkC q :: forall c. CondCat (:>) c => Pins t -> CircuitM (Pins ((a :=> c) :* (b :=> c) :=> c))
        :: forall c. CondCat (:>) c => Pins t -> CircuitM ((a :=> c) :* (b :=> c) :> c)

fg :: (a :> c) :* (b :> c)

unmkC q t :: forall c. CondCat (:>) c => CircuitM ((a :=> c) :* (b :=> c) :> c)
h :: (a :=> c) :* (b :=> c) :> c
unmkC h :: (a :> b) :* (b :> c) -> CircuitM (Pins c)
unmkC h fg :: CircuitM (Pins c)

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
