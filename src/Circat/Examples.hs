{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}

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

import Prelude hiding (id,(.),const,fst,snd,not,and,or,curry,uncurry,sequence)
import TypeUnary.Vec hiding (get)

import Circat.Circuit
import Circat.Misc ((:*),Unop)
import Circat.Category
import Circat.Classes
import Circat.RTree

import Circat.Netlist (outV)


{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

bc :: Unop (a :> b)
bc = id

-- Write in most general form and then display by applying 'bc' (to
-- type-narrow).

c0 :: BoolWith k b => b `k` b
c0 = id

c1 :: BoolWith k b => b `k` b
c1 = not . not

c2 :: BoolWith k b => (b :* b) `k` b
c2 = not . and

c3 :: BoolWith k b => (b :* b) `k` b
c3 = not . and . (not *** not)

c4 :: BoolWith k b => (b :* b) `k` (b :* b)
c4 = swapP  -- no components

c5 :: BoolWith k b => (b :* b) `k` (b :* b)
c5 = xor &&& and   -- half-adder

c6 :: b ~ BoolT (:>) => () :> b
c6 = constC False

c7 :: b ~ BoolT (:>) => b :> b
c7 = constC False

outSimples :: IO ()
outSimples = 
  do outG "c0" c0
     outG "c1" c1
     outG "c2" c2
     outG "c3" c3
     outG "c4" c4
     outG "c5" c5
     outG "c6" c6
     outG "c7" c7
     outV "c0" c0
     outV "c1" c1
     outV "c2" c2
     outV "c3" c3
     outV "c4" c4
     outV "c5" c5
     outV "c6" c6
     outV "c7" c7
  

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
  outV "addV1"  addV1
  outV "addV2"  addV2
  outV "addV4"  addV4
  outV "addV8"  addV8
  outV "addV16" addV16

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
  outV "addT1"  addT1
  outV "addT2"  addT2
  outV "addT4"  addT4
  outV "addT8"  addT8
  outV "addT16" addT16

outAll :: IO ()
outAll = do outSimples ; outVecs ; outTrees
