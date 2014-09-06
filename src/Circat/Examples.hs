{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds, FlexibleContexts #-}

{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  Circat.Examples
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Circuit examples
----------------------------------------------------------------------

module Circat.Examples (outSimples,outAll,bc,outV) where

import Prelude hiding (id,(.),const,not,and,or,curry,uncurry,sequence)
#if 0
import TypeUnary.Vec hiding (get)
#endif

import Circat.Circuit
import Circat.Misc ((:*),Unop)
import Circat.Category
import Circat.Classes
-- import Circat.RTree

import Circat.Netlist (outV)


{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

outGV :: GenBuses a => String -> Attrs -> (a :> b) -> IO ()
outGV name attrs cir =
  do outG name attrs cir
     outV name       cir

-- outG = outGWith ("pdf","")  -- change as desired.

-- Handy for showing the graph representation in ghci.
bc :: Unop (a :> b)
bc = id

-- Write in most general form and then display by applying 'bc' (to
-- type-narrow).

c0 :: BoolCat k => Bool `k` Bool
c0 = id

c1 :: BoolCat k => Bool `k` Bool
c1 = not . not

c2 :: BoolCat k => (Bool :* Bool) `k` Bool
c2 = not . and

c3 :: BoolCat k => (Bool :* Bool) `k` Bool
c3 = not . and . (not *** not)

c4 :: BoolCat k => (Bool :* Bool) `k` (Bool :* Bool)
c4 = swapP  -- no components

c5 :: BoolCat k => (Bool :* Bool) `k` (Bool :* Bool)
c5 = xor &&& and   -- half-adder

c6 :: () :> Bool
c6 = constC False

c7 :: Bool :> Bool
c7 = constC False

outSimples :: IO ()
outSimples = 
  do out "c0" c0
     out "c1" c1
     out "c2" c2
     out "c3" c3
     out "c4" c4
     out "c5" c5
     out "c6" c6
     out "c7" c7
 where
   out :: GenBuses a => String -> (a :> b) -> IO ()
   out = flip outGV []

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

#if 0

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
  outGV "addV1"  addV1
  outGV "addV2"  addV2
  outGV "addV4"  addV4
  outGV "addV8"  addV8
  outGV "addV16" addV16

#endif

-- Trees (identical results)

#if 0

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
  outGV "addT1"  addT1
  outGV "addT2"  addT2
  outGV "addT4"  addT4
  outGV "addT8"  addT8
  outGV "addT16" addT16

#endif

----

{-

-- Stateful addition via StateFun

outSG :: (IsSourceP s, GenBuses a, StateCatWith sk (:>) s) =>
         String -> (a `sk` b) -> IO ()
outSG name = outG name . runState

type (:->) = StateFun (:>) Bool

type AddS f = f (Pair Bool) :-> f Bool

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

type AddS f = f (Pair Bool) :-> f Bool

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

-}

-- addTS16 :: AddTS N4
-- addTS16 = addS

----

outAll :: IO ()
outAll = do outSimples -- ; outVecs -- ; outTrees
