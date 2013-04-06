{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE TupleSections, ScopedTypeVariables, ExistentialQuantification #-}
{-# LANGUAGE ParallelListComp #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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

module Circat.Circuit where

-- TODO: explicit exports

import Prelude hiding (id,(.),fst,snd)
import qualified Prelude as P

import Control.Applicative
import Control.Monad (void,join,(>=>),(<=<))
import qualified Control.Arrow as A
import Control.Arrow (Kleisli(..))
import Data.Foldable (foldMap)

import System.Process (system)

import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as M

-- mtl
import Control.Monad.State (MonadState(..),State,runState,evalState)
import Control.Monad.Writer (MonadWriter(..),WriterT,runWriterT)
import Text.Printf

-- import qualified Language.Dot as D

import Circat.Misc ((:*),(:+),(<~),Unop)
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
sourceBits s = toBits s []

-- The Source type family gives a representation for a type in terms of
-- structures of pins. Maybe drop the Show constraint later (after testing).
class Show a => IsSource a where
  toBits    :: a -> Unop [Bit]  -- difference list
  genSource :: CircuitM a

genComp :: forall a b. IsSource2 a b =>
           Prim a b -> a -> CircuitM b
genComp prim a = do b <- genSource
                    tell [Comp prim a b]
                    return b

type IsSource2 a b = (IsSource a, IsSource b)

instance IsSource () where
  toBits () = id
  genSource = pure ()

instance IsSource Bit where
  toBits p  = (p :)
  genSource = newBit

instance IsSource2 a b => IsSource (a :* b) where
  toBits (sa,sb) = toBits sb . toBits sa
  genSource      = liftA2 (,) genSource genSource

-- instance IsSource (a :+ b) where ... ???

{--------------------------------------------------------------------
    Circuit category
--------------------------------------------------------------------}

infixl 1 :>

-- | Circuit category
type (:>) = Kleisli CircuitM

-- TODO: Will the product & coproduct instances really work here, or do I need a
-- wrapper around Kleisli? Maybe they just work. Hm. If so, what benefit accrues
-- from using the categorical instead of monadic form?

newComp :: IsSource2 a b => Prim a b -> a :> b
newComp prim = Kleisli (genComp prim)

pcomp :: IsSource2 a b => String -> a :> b
pcomp = newComp . Prim

instance BoolCat (:>) where
  type BoolT (:>) = Bit
  notC = pcomp "not"
  orC  = pcomp "or"
  andC = pcomp "and"

instance EqCat (:>) where
  type EqConstraint (:>) a = IsSource a
  eq  = pcomp "eq"
  neq = pcomp "neq"

instance IsSource2 a b => Show (a :> b) where
  show = show . cComps

evalWS :: WriterT o (State s) b -> s -> (b,o)
evalWS w s = evalState (runWriterT w) s

-- Turn a circuit into a list of components, including fake In & Out.
cComps :: IsSource2 a b => (a :> b) -> [Comp]
cComps (Kleisli f) =
  snd . flip evalWS (Bit 0) $
    do i  <- genComp (Prim "In") ()
       o  <- f i
       () <- genComp (Prim "Out") o
       return ()

{--------------------------------------------------------------------
    Visualize circuit as dot graph
--------------------------------------------------------------------}

outG :: IsSource2 a b => String -> (a :> b) -> IO ()
outG name circ = 
  do writeFile (outFile "dot") (toG circ)
     void $ system $ 
       printf "neato -Tsvg %s -o %s" (outFile "dot") (outFile "svg")
 where
   outFile suff = "dot/"++name++"."++suff

type DGraph = String

toG :: IsSource2 a b => (a :> b) -> DGraph
toG cir = "digraph {\n" ++ concatMap wrap (recordDots comps) ++ "}\n"
 where
   comps = simpleComp <$> cComps cir
   wrap = ("  " ++) . (++ ";\n")

-- I use neato mainly because it supports the edge length attribute ("len"),
-- which I use for input & output ports. Alternatively, use records with one
-- side for inputs, one for outputs, and the primitive name in-between.

type Statement = String

type Comp' = (String,[Bit],[Bit])

simpleComp :: Comp -> Comp'
simpleComp (Comp prim a b) = (show prim, sourceBits a, sourceBits b)

data Dir = In | Out deriving Show
type PortNum = Int
type CompNum = Int

recordDots :: [Comp'] -> [Statement]
recordDots comps = prelude ++ nodes ++ edges
 where
   tagged :: [a] -> [(Int,a)]
   tagged = zip [0 ..]
   ncomps :: [(CompNum,Comp')] -- numbered comps
   ncomps = tagged comps
   prelude = ["ordering=out","splines=true"]
   nodes = "node [fixedsize=true,shape=Mrecord]" : (node <$> ncomps)
    where
      node (nc,(prim,ins,outs)) =
        printf "%s [label=\"{%s}|%s|{%s}\"]" 
          (compLab nc) (labs In ins) prim (labs Out outs)
       where
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

-- Map each bit to its source component and output port numbers
type SourceMap = Map Bit (CompNum,PortNum)

sourceMap :: [(CompNum,Comp')] -> SourceMap
sourceMap = foldMap sources
 where
   sources :: (Int,Comp') -> SourceMap
   sources (nc,(_,_,outs)) = M.fromList [(b,(nc,np)) | np <- [0 ..] | b <- outs]

--    portLab dir (portNum,bit) = printf "<%s%d>%d" (show dir) portNum bit


-- use <$> instead of map

compsDots :: [Comp'] -> [Statement]
compsDots comps = prelude ++ compNodes ++ portEdges ++ flowEdges
 where
   tagged :: [a] -> [(Int,a)]
   tagged = zip [0 ..]
   ncomps :: [(Int,Comp')] -- numbered comps
   ncomps = tagged comps
   prelude = ["ordering=out","splines=true"]
   compNodes = "node [fixedsize=true,shape=circle]" : map node ncomps
    where
      node (n,(prim,_,_)) =
        printf "%s [label=%s]" (compLab n) (show prim)
   portEdges = "node [shape=point]" 
             : "edge [arrowsize=0,len=0.35,fontsize=8]"
             : concatMap edges ncomps
    where
      edges (nc,(_,ins,outs)) = map inEdge  (tagged ins)
                             ++ map outEdge (tagged outs)
       where
         inEdge  (ni,_) = edge (inLab nc ni) (compLab nc) "head" ni
         outEdge (no,o) = edge (compLab nc)  (outLab o)   "tail" no
         edge = printf "%s -> %s [%slabel=%d]"
   flowEdges = "edge [arrowsize=0.75,len=1]" : concatMap edge ncomps
    where
      edge (nc,(_,srcs,_)) = map srcEdge (tagged srcs)
       where
         srcEdge (ni,src) =
           printf "%s -> %s" (outLab src) (inLab nc ni)
   compLab :: Int -> String
   compLab = ('c':) . show
   outLab :: Bit -> String
   outLab (Bit n) = 'b' : show n
   inLab :: Int -> Int -> String
   inLab nc ni = compLab nc ++ "_i" ++ show ni

-- ((Bit 0,Bit 2),[Comp not (Bit 0) (Bit 1),Comp not (Bit 1) (Bit 2)])

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

bc :: Unop (a :> b)
bc = id

-- Write in most general form and then display by applying 'bc' (to
-- type-narrow).

c0 :: BCat (~>) b => b ~> b
c0 = id

c1 :: BCat (~>) b => b ~> b
c1 = notC . notC

c2 :: BCat (~>) b => (b :* b) ~> b
c2 = notC . andC

c3 :: BCat (~>) b => (b :* b) ~> b
c3 = notC . andC . (notC *** notC)

c4 :: BCat (~>) b => (b :* b) ~> (b :* b)
c4 = swapP  -- no components

c5 :: BCat (~>) b => (b :* b) ~> (b :* b)
c5 = andC &&& orC

{- For instance,

> c3 (True,False)
True

> bc c3
(((Bit 0,Bit 1),Bit 5),[Comp (Prim "not") (Bit 0) (Bit 2),Comp (Prim "not") (Bit 1) (Bit 3),Comp (Prim "and") (Bit 2,Bit 3) (Bit 4),Comp (Prim "not") (Bit 4) (Bit 5)])

-}
