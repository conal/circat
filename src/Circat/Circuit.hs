{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification, GADTs #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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

module Circat.Circuit ((:>), toG, outG, bc) where

import Prelude hiding (id,(.),fst,snd)
import qualified Prelude as P

import Data.Monoid (mempty,(<>))
import Data.Functor ((<$>))
import Control.Applicative (pure,liftA2)
import Control.Arrow (Kleisli(..))
import Data.Foldable (foldMap,toList)

import qualified System.Info as SI
import System.Process (system) -- ,readProcess
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode(ExitSuccess))

import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

-- mtl
import Control.Monad.State (MonadState(..),State,evalState)
import Control.Monad.Writer (MonadWriter(..),WriterT,runWriterT)
import Text.Printf (printf)

import TypeUnary.Vec (Vec(..),Nat(..),IsNat(..))

import Circat.Misc ((:*),(<~),Unop)
import Circat.Category
import Circat.Classes

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
type CircuitM = WriterT [Comp] (State BitSupply)

-- TODO: Is WriterT [a] efficient, or do we get frequent (++)? I could use a
-- difference list instead, i.e., Unop [Comp] instead of [Comp].

newtype Bit = Bit Int deriving (Eq,Ord,Show,Enum)
type BitSupply = Bit  -- Next free pin

newBit :: CircuitM Bit
newBit = do { p <- get ; put (succ p) ; return p }

{--------------------------------------------------------------------
    Bits
--------------------------------------------------------------------}

sourceBits :: forall a. IsSource a => a -> [Bit]
sourceBits s = toList (toBits s)

-- The Source type family gives a representation for a type in terms of
-- structures of pins. Maybe drop the Show constraint later (after testing).
class Show a => IsSource a where
  toBits    :: a -> Seq Bit
  genSource :: CircuitM a

genComp :: forall a b. IsSource2 a b =>
           Prim a b -> a -> CircuitM b
genComp prim a = do b <- genSource
                    tell [Comp prim a b]
                    return b

type IsSource2 a b = (IsSource a, IsSource b)

instance IsSource () where
  toBits () = mempty
  genSource = pure ()

instance IsSource Bit where
  toBits p  = Seq.singleton p
  genSource = newBit

instance IsSource2 a b => IsSource (a :* b) where
  toBits (sa,sb) = toBits sb <> toBits sa
  genSource      = liftA2 (,) genSource genSource

-- instance IsSource (a :+ b) where ... ???

instance (IsNat n, IsSource a) => IsSource (Vec n a) where
  toBits    = foldMap toBits
  genSource = genSourceV nat

genSourceV :: IsSource a => Nat n -> CircuitM (Vec n a)
genSourceV Zero     = pure ZVec
genSourceV (Succ n) = liftA2 (:<) genSource (genSourceV n)


{--------------------------------------------------------------------
    Circuit category
--------------------------------------------------------------------}

infixl 1 :>

-- | Circuit category
type (:>) = Kleisli CircuitM

-- TODO: Will the product & coproduct instances really work here, or do I need a
-- wrapper around Kleisli? Maybe they just work. Hm. If so, what benefits arise
-- from using the categorical instead of monadic form? Perhaps amenability to
-- other interpretations, such as timing and demand analysis.

primC :: IsSource2 a b => Prim a b -> a :> b
primC = Kleisli . genComp

namedC :: IsSource2 a b => String -> a :> b
namedC = primC . Prim

instance CategoryBool (:>) where
  type BoolT (:>) = Bit
  notC = namedC "not"
  orC  = namedC "or"
  andC = namedC "and"

instance EqCat (:>) where
  type EqConstraint (:>) a = IsSource a
  eq  = namedC "eq"
  neq = namedC "neq"

instance IsSource2 a b => Show (a :> b) where
  show = show . runC

evalWS :: WriterT o (State s) b -> s -> (b,o)
evalWS w s = evalState (runWriterT w) s

-- Turn a circuit into a list of components, including fake In & Out.
runC :: IsSource2 a b => (a :> b) -> [Comp]
runC = runU . unitize

runU :: (() :> ()) -> [Comp]
runU (Kleisli f) = snd (evalWS (f ()) (Bit 0))

-- Wrap a circuit with fake input and output
unitize :: IsSource2 a b => (a :> b) -> (() :> ())
unitize = namedC "Out" <~ namedC "In"

{--------------------------------------------------------------------
    Visualize circuit as dot graph
--------------------------------------------------------------------}

-- I could use the language-dot API, but it's easier not to.

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
       printf "dot -Gdpi=200 -T%s %s -o %s" outType (outFile "dot") (outFile outType)
     systemSuccess $
       printf "%s %s" open (outFile outType)
 where
   outDir = "out"
   outFile suff = outDir++"/"++name++"."++suff
   outType = "png"
   open | SI.os == "darwin" = "open"
        | otherwise         = error "unknown open for OS"

type DGraph = String

toG :: IsSource2 a b => (a :> b) -> DGraph
toG cir = "digraph {\n" ++ concatMap wrap (recordDots comps) ++ "}\n"
 where
   comps = simpleComp <$> runC cir
   wrap  = ("  " ++) . (++ ";\n")

type Statement = String

type Comp' = (String,[Bit],[Bit])

simpleComp :: Comp -> Comp'
simpleComp (Comp prim a b) = (show prim, sourceBits a, sourceBits b)

data Dir = In | Out deriving Show
type PortNum = Int
type CompNum = Int

tagged :: [a] -> [(Int,a)]
tagged = zip [0 ..]

recordDots :: [Comp'] -> [Statement]
recordDots comps = prelude ++ nodes ++ edges
 where
   ncomps :: [(CompNum,Comp')] -- numbered comps
   ncomps = tagged comps
   prelude = ["rankdir=LR ; node [shape=Mrecord]"] -- maybe add fixedsize=true
   nodes = node <$> ncomps
    where
      node (nc,(prim,ins,outs)) =
        printf "%s [label=\"{%s%s%s}\"]" (compLab nc) 
          (ports "" (labs In ins) "|") prim (ports "|" (labs Out outs) "")
       where
         ports _ "" _ = ""
         ports l s r = printf "%s{%s}%s" l s r
         labs dir bs = intercalate "|" (bracket . portLab dir . fst <$> tagged bs)
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

-- Note: the rankdir=LR and the outer braces in node lead to a left-to-right
-- rendering by dot. I expected a top-to-bottom rendering to work as well, but
-- it looks terrible.

-- Map each bit to its source component and output port numbers
type SourceMap = Map Bit (CompNum,PortNum)

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

_c0 :: BCat (~>) b => b ~> b
_c0 = id

_c1 :: BCat (~>) b => b ~> b
_c1 = notC . notC

_c2 :: BCat (~>) b => (b :* b) ~> b
_c2 = notC . andC

_c3 :: BCat (~>) b => (b :* b) ~> b
_c3 = notC . andC . (notC *** notC)

_c4 :: BCat (~>) b => (b :* b) ~> (b :* b)
_c4 = swapP  -- no components

_c5 :: BCat (~>) b => (b :* b) ~> (b :* b)
_c5 = andC &&& orC

{- For instance,

> _c3 (True,False)
True

> bc _c3
[Comp In () (Bit 0,Bit 1),Comp not (Bit 0) (Bit 2),Comp not (Bit 1) (Bit 3),Comp and (Bit 2,Bit 3) (Bit 4),Comp not (Bit 4) (Bit 5),Comp Out (Bit 5) ()]

-- Same, pretty-printed:

[ Comp In () (Bit 0,Bit 1)
, Comp not (Bit 0) (Bit 2)
, Comp not (Bit 1) (Bit 3)
, Comp and (Bit 2,Bit 3) (Bit 4)
, Comp not (Bit 4) (Bit 5)
, Comp Out (Bit 5) ()
]

> putStr $ toG _c3
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

> outG "c3" _c3

-- Then view src/dot/c3.svg (and see outType above).

-}

-- Simple adders

