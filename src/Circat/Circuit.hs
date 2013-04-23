{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification, TypeSynonymInstances, GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances #-} -- see below

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Circuit
-- Copyright   :  (c) 2013 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Circuit representation
----------------------------------------------------------------------

module Circat.Circuit
  -- ((:>), toG, outG, bc, outAll)
    where

import Prelude hiding (id,(.),const,fst,snd,not,and,or,curry,uncurry,sequence)
import qualified Prelude as P

import Data.Monoid (mempty,(<>))
import Data.Functor ((<$>))
import Control.Applicative (pure,liftA2)
import Control.Monad (liftM)
import Control.Arrow (arr,Kleisli(..))
import Data.Foldable (foldMap,toList)
import Data.Traversable (Traversable(..))

import qualified System.Info as SI
import System.Process (system) -- ,readProcess
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode(ExitSuccess))

import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Sequence (Seq,singleton)

-- mtl
import Control.Monad.State (State,evalState)
import qualified Control.Monad.State as M
import Control.Monad.Writer (MonadWriter(..),WriterT,runWriterT)
import Text.Printf (printf)

import TypeUnary.Vec hiding (get)
import FunctorCombo.StrictMemo (HasTrie(..),(:->:),idTrie)

import Circat.Misc ((:*),(<~),Unop,inNew)
import Circat.Category
import Circat.State (StateCat(..),StateCatWith,StateFun,StateExp)
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
type PinSupply = Pin  -- Next free pin

newPin :: CircuitM Pin
newPin = do { p <- M.get ; M.put (succ p) ; return p }

{--------------------------------------------------------------------
    Pins
--------------------------------------------------------------------}

sourcePins :: forall a. IsSource a => a -> [Pin]
sourcePins s = toList (toPins s)

-- | Give a representation for a type in terms of structures of pins.
class Show a => IsSource a where
  toPins    :: a -> Seq Pin
  genSource :: CircuitM a

genComp :: forall a b. IsSource2 a b =>
           Prim a b -> a -> CircuitM b
genComp prim a = do b <- genSource
                    tell (singleton (Comp prim a b))
                    return b

type IsSource2 a b = (IsSource a, IsSource b)

instance IsSource () where
  toPins () = mempty
  genSource = pure ()

instance IsSource Pin where
  toPins p  = singleton p
  genSource = newPin

instance IsSource2 a b => IsSource (a :* b) where
  toPins (sa,sb) = toPins sa <> toPins sb
  genSource      = liftA2 (,) genSource genSource

-- instance IsSource (a :+ b) where ... ???

instance (IsNat n, IsSource a) => IsSource (Vec n a) where
  toPins    = foldMap toPins
  genSource = genSourceV nat

genSourceV :: IsSource a => Nat n -> CircuitM (Vec n a)
genSourceV Zero     = pure ZVec
genSourceV (Succ n) = liftA2 (:<) genSource (genSourceV n)

instance IsSource a => IsSource (Pair a) where
  toPins    = foldMap toPins
  genSource = toPair <$> genSource

instance (IsNat n, IsSource a) => IsSource (Tree n a) where
  toPins    = foldMap toPins
  genSource = genSourceT nat

genSourceT :: IsSource a => Nat n -> CircuitM (Tree n a)
genSourceT Zero     = L <$> genSource
genSourceT (Succ _) = B <$> genSource

-- TODO: does the recounting of nat lead to quadratic work?
-- Perhaps rewrite, using the Succ argument.

{--------------------------------------------------------------------
    Pins representing a given type
--------------------------------------------------------------------}

type family Pins a

type instance Pins Bool = Pin

-- Everything else distributes:
type instance Pins ()         = ()
type instance Pins ( a :* b ) = Pins a :* Pins b
type instance Pins (Pair a  ) = Pair (Pins a)
type instance Pins (Vec n a ) = Vec  n (Pins a)
type instance Pins (Tree n a) = Tree n (Pins a)

{--------------------------------------------------------------------
    Circuit category
--------------------------------------------------------------------}

infixl 1 :>

-- | Circuit category
type (:>) = Kleisli CircuitM

mkC :: (a -> CircuitM b) -> (a :> b)
mkC = Kleisli

primC :: IsSource2 a b => Prim a b -> a :> b
primC = mkC . genComp

namedC :: IsSource2 a b => String -> a :> b
namedC = primC . Prim

-- constC :: (IsSource2 a b, Show b) => b -> a :> b
constC :: (IsSource2 a (Pins b), Show b) => b -> a :> Pins b
constC b = namedC (show b)

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

instance BoolCat (:>) where
  type BoolT (:>) = Pin
  not = namedC "not"
  and = namedC "and"
  or  = namedC "or"
  xor = namedC "xor"

instance EqCat (:>) where
  type EqKon (:>) a = IsSource a
  eq  = namedC "eq"
  neq = namedC "neq"

instance AddCat (:>) where
  -- TODO: Try with and without these non-defaults
--   fullAdd = namedC "fullAdd"
--   halfAdd = namedC "halfAdd"

instance IsSource2 a b => Show (a :> b) where
  show = show . runC

--     Application is no smaller than the instance head
--       in the type family application: RepT :> a
--     (Use -XUndecidableInstances to permit this)

evalWS :: WriterT o (State s) b -> s -> (b,o)
evalWS w s = evalState (runWriterT w) s

-- Turn a circuit into a list of components, including fake In & Out.
runC :: IsSource2 a b => (a :> b) -> [Comp]
runC = runU . unitize

runU :: (() :> ()) -> [Comp]
runU (Kleisli f) = toList (snd (evalWS (f ()) (Pin 0)))

-- Wrap a circuit with fake input and output
unitize :: IsSource2 a b => (a :> b) -> (() :> ())
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

outG :: IsSource2 a b => String -> (a :> b) -> IO ()
outG name circ = 
  do createDirectoryIfMissing False outDir
     writeFile (outFile "dot") (toG circ)
     systemSuccess $
       printf "dot %s -T%s %s -o %s" res outType (outFile "dot") (outFile outType)
     systemSuccess $
       printf "%s %s" open (outFile outType)
 where
   outDir = "out"
   outFile suff = outDir++"/"++name++"."++suff
   (outType,res) = ("pdf","")
                   -- ("svg","")
                   -- ("png","-Gdpi=200")
   open | SI.os == "darwin" = "open"
        | otherwise         = error "unknown open for OS"

type DGraph = String

toG :: IsSource2 a b => (a :> b) -> DGraph
toG cir = printf "digraph {\n%s}\n"
            (concatMap wrap (prelude ++ recordDots comps))
 where
   prelude = ["rankdir=LR","node [shape=Mrecord]"] -- maybe add fixedsize=true
   comps = simpleComp <$> runC cir
   wrap  = ("  " ++) . (++ ";\n")

type Statement = String

type Comp' = (String,[Pin],[Pin])

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
         labs dir bs = intercalate "|" (portSticker . fst <$> tagged bs)
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

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

bc :: Unop (a :> b)
bc = id

-- Write in most general form and then display by applying 'bc' (to
-- type-narrow).

c0 :: BoolWith (~>) b => b ~> b
c0 = id

c1 :: BoolWith (~>) b => b ~> b
c1 = not . not

c2 :: BoolWith (~>) b => (b :* b) ~> b
c2 = not . and

c3 :: BoolWith (~>) b => (b :* b) ~> b
c3 = not . and . (not *** not)

c4 :: BoolWith (~>) b => (b :* b) ~> (b :* b)
c4 = swapP  -- no components

c5 :: BoolWith (~>) b => (b :* b) ~> (b :* b)
c5 = xor &&& and   -- half-adder

c6 :: b ~ BoolT (:>) => () :> b
c6 = constC False

c7 :: b ~ BoolT (:>) => b :> b
c7 = constC False

outSimples :: IO ()
outSimples = do
  outG "c0" c0
  outG "c1" c1
  outG "c2" c2
  outG "c3" c3
  outG "c4" c4
  outG "c5" c5
  outG "c6" c6

{- For instance,

> c3 (True,False)
True

> bc c3
[Comp In () (Pin 0,Pin 1),Comp not (Pin 0) (Pin 2),Comp not (Pin 1) (Pin 3),Comp and (Pin 2,Pin 3) (Pin 4),Comp not (Pin 4) (Pin 5),Comp Out (Pin 5) ()]

-- Same, pretty-printed:

[ Comp In () (Pin 0,Pin 1)
, Comp not (Pin 0) (Pin 2)
, Comp not (Pin 1) (Pin 3)
, Comp and (Pin 2,Pin 3) (Pin 4)
, Comp not (Pin 4) (Pin 5)
, Comp Out (Pin 5) ()
]

> putStr $ toG c3
digraph {
  rankdir=LR ; node [shape=Mrecord];
  c0 [label="{In|{<Out0>|<Out1>}}"];
  c1 [label="{{<In0>}|not|{<Out0>}}"];
  c2 [label="{{<In0>}|not|{<Out0>}}"];
  c3 [label="{{<In0>|<In1>}|and|{<Out0>}}"];
  c4 [label="{{<In0>}|not|{<Out0>}}"];
  c5 [label="{{<In0>}|Out}"];
  c0:Out1 -> c1:In0;
  c0:Out0 -> c2:In0;
  c2:Out0 -> c3:In0;
  c1:Out0 -> c3:In1;
  c3:Out0 -> c4:In0;
  c4:Out0 -> c5:In0;
}

> outG "c3" c3

-}

-- Vectors

addV1 :: AddVP N1
addV1 = adds

addV2 :: AddVP N2
addV2 = adds

addV4 :: AddVP N4
addV4 = adds

addV8 :: AddVP N8
addV8 = adds

addV16 :: AddVP N16
addV16 = adds

outVecs :: IO ()
outVecs = do
  outG "addV1"  addV1
  outG "addV2"  addV2
  outG "addV4"  addV4
  outG "addV8"  addV8
  outG "addV16" addV16

-- Trees (identical results)

addT1 :: AddTP N0
addT1 = adds

addT2 :: AddTP N1
addT2 = adds

addT4 :: AddTP N2
addT4 = adds

addT8 :: AddTP N3
addT8 = adds

addT16 :: AddTP N4
addT16 = adds

outTrees :: IO ()
outTrees = do
  outG "addT1"  addT1
  outG "addT2"  addT2
  outG "addT4"  addT4
  outG "addT8"  addT8
  outG "addT16" addT16

outAll :: IO ()
outAll = do outSimples ; outVecs ; outTrees

-- Stateful addition via StateFun

outSG :: (IsSource s, IsSource2 a b, StateCatWith (~~>) (:>) s) =>
         String -> (a ~~> b) -> IO ()
outSG name = outG name . runState

type (:->) = StateFun (:>) (BoolT (:>))

type AddS f = f (Pair (BoolT (:>))) :-> f (BoolT (:>))

type AddVS n = AddS (Vec  n)
type AddTS n = AddS (Tree n)

addVS1 :: AddVS N1
addVS1 = addS

addVS2 :: AddVS N2
addVS2 = addS

addVS4 :: AddVS N4
addVS4 = addS

addVS8 :: AddVS N8
addVS8 = addS

addVS16 :: AddVS N16
addVS16 = addS

-- outSG "addVS4" addVS4
--   or
-- outG "addVS4" (runState addVS4)

{-

addTS16 :: AddTS N4
addTS16 = addS

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

--   apply   :: ClosedKon (~>) a => (Exp (~>) a b :* a) ~> b
--   curry   :: ClosedKon (~>) b => ((a :* b) ~> c) -> (a ~> Exp (~>) b c)
--   uncurry :: ClosedKon (~>) b => (a ~> Exp (~>) b c) -> (a :* b) ~> c

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

-- instance ClosedCatU (~>) s => StateCat (StateExp (~>) s) where
--   type StateKon  (StateExp (~>) s) = ClosedKon (~>) s
--   type StateBase (StateExp (~>) s) = (~>)
--   type StateT    (StateExp (~>) s) = s
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
--   type ClosedKon (:>) u = (HasTrie u, Traversable (Trie (Unpins u)))
--   type Exp (:>) u v = Unpins u :->: v
--   apply = muxC

--   curry   = inNew $ \ f -> sequence . trie . curry f
--   uncurry = inNew $ \ h -> uncurry (distribMF . liftM untrie . h)

--   apply   :: ClosedKon (~>) a => (Exp (~>) a b :* a) ~> b
--   curry   :: ClosedKon (~>) b => ((a :* b) ~> c) -> (a ~> Exp (~>) b c)
--   uncurry :: ClosedKon (~>) b => (a ~> Exp (~>) b c) -> (a :* b) ~> c

{-
  apply   :: ClosedKon (:>) a => ((Unpins a :->: b) :* a) :> b
  curry   :: ClosedKon (:>) b => ((a :* b) :> c) -> (a :> (Unpins b :->: c))
  uncurry :: ClosedKon (:>) b => (a :> (Unpins b :->: c)) -> ((a :* b) :> c)

uncurry untrie :: ((k :->: v) :* k) -> v
uncurry untrie :: ((Unpins a :->: b) :* Unpins a) -> b

-}

muxC :: (IsSource2 ((Unpins k :->: v) :* k) v, HasTrie k) =>
        ((Unpins k :->: v) :* k) :> v
muxC = namedC "mux"
