{-# LANGUAGE TypeOperators, ConstraintKinds, FlexibleContexts, CPP #-}
{-# LANGUAGE ViewPatterns, PatternGuards, ParallelListComp, ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  Circat.Circuit
-- Copyright   :  (c) 2013 Tabula, Inc.
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Circuit to Netlist conversion
----------------------------------------------------------------------

#define StateMachine

-- TODO: Use Text.Printf to replace the awkward string formations in this
-- module.

module Circat.Netlist
  ( toNetlist, mk_module
  , genVHDL, V.ppModule
  , outV  -- phasing out
  , saveAsVerilog
  ) where

import Data.Monoid (mempty,(<>),mconcat)
import Control.Arrow (first)
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as M
import Text.Printf (printf)

import System.Directory (createDirectoryIfMissing)

import Circat.Circuit
  ( CompS(..), compOuts, compName, compOuts, tagged
  , Width, PinId, Bus(..),Name,DGraph,Report
  , (:>), GenBuses,unitize,mkGraph
  )

import Language.Netlist.AST
  ( Module(..), Decl(..), Expr(..), ExprLit (..), Bit(..), Range(..)
  , BinaryOp(..), UnaryOp(..), Ident, Range, Event(..), Edge(..), Stmt(..) )

import Language.Netlist.GenVHDL(genVHDL)
import Language.Netlist.GenVerilog(mk_module)
import qualified Language.Verilog as V

-- PinId description: width & name
type PinDesc = (Width,String)

-- type PinToWireDesc = (PinId,PinDesc) 

type PinMap = Map PinId PinDesc

-- Phasing out
outV :: GenBuses a => Name -> (a :> b) -> IO ()
outV name circ = saveVerilog name' (toVerilog ndr)
 where
   ndr@(name',_,_) = mkGraph name (unitize circ)

-- | Converts a Circuit to a Module
toNetlist :: Name -> DGraph -> Module

#ifdef StateMachine
toNetlist name comps
--   | Left _ <- portCompMb "NewState" comps
--   = Module name' ins outs [] (nets++assigns)
--   | otherwise
  = Module name' (clockIns++ins) outs [] (nets++assigns++clockDecls)
 where
   (p2wIn,ins)    = modPorts "In"
   (_,outs)       = modPorts "Out"
   (p2wNets,nets) = moduleNets comps
   p2w            = p2wIn <> p2wNets
   assigns        = moduleAssigns p2w comps
   modPorts str   = modulePorts (portComp str comps)
   (clockIns,clockDecls) = clocked p2w comps
   name' = map tweak name
    where
      tweak '-' = '_'
      tweak c   = c

-- TODO: rename "portComp", since it's no longer just about module ports.

clocked :: PinMap -> DGraph -> ([(Ident,Maybe Range)],[Decl])
clocked p2w comps
  | null states = mempty
  | otherwise =
      ( [("clock",Nothing),("reset",Nothing)]
      , [ProcessDecl
           (Event (ExprVar "clock") PosEdge) Nothing
           (If (ExprBinary Equals
                 (ExprVar "reset") (ExprLit Nothing (ExprBit T)))
               (updates starts)
               (Just (updates news)))] )
 where
  starts,news,states :: [Expr]
  (starts,news,states) =
    unzip3 [(v start,v new,v state) | CompS _ "delay" [start,new] [state] _ <- comps]
  v :: Bus -> Expr
  v = sourceExp p2w  -- Move to view pattern
  updates :: [Expr] -> Stmt
  updates sources = sseq (zipWith Assign states sources)

--   always @ (posedge clock)
--     if (reset == 1'b1) begin s0 <= inits0; ... end
--     else begin s0 <= t0; ... end
--   end

-- Statment Seq tidied for singletons sequences.
sseq :: [Stmt] -> Stmt
sseq [s] = s
sseq ss = Seq ss

#else
toNetlist name comps = Module name ins outs [] (nets++assigns)
  where (p2wM,ins)  = modulePorts (portComp "In"  comps)
        (_,outs)    = modulePorts (portComp "Out" comps)
        (p2wI,nets) = moduleNets comps
        p2w         = p2wM <> p2wI
        assigns     = moduleAssigns p2w comps
#endif

-- TODO: Rework toNetlist with a Writer monad, aggregating a PinMap.
-- Ditto for modulePorts and moduleNets.
-- Maybe gather the ins & outs similarly in the monoid.
-- Maybe then a Reader with the same info for moduleAssigns.

toVerilog :: (Name,DGraph,Report) -> String
toVerilog (name,graph,_report) =
  printf "%s"
   (show (V.ppModule (mk_module (toNetlist name graph))))

saveAsVerilog :: (Name,DGraph,Report) -> IO ()
saveAsVerilog gg@(name,_,_) = saveVerilog name (toVerilog gg)

saveVerilog :: Name -> String -> IO ()
saveVerilog name verilog =
  do createDirectoryIfMissing False outDir
     writeFile filePath verilog
     putStrLn ("Wrote " ++ filePath)
  where
    outDir   = "out"
    filePath = outDir ++ "/" ++ name ++ ".v"

-- | Produces the assign statements for every Comp except inputs ("In" and
-- "State"). Assign statements bind the result of a function (and,or,add
-- etc.) to a variable name which is a wire in verilog parlance eg. w_xor_I1 =
-- In_0 ^ In_1 // (`^` is xor)
moduleAssigns :: PinMap -> [CompS] -> [Decl]
moduleAssigns p2w = concatMap (moduleAssign p2w)

isInput, isOutput, isNewState, isTerminal :: String -> Bool
-- isInput  = (`elem` ["In" , "State"])
-- isOutput = (`elem` ["Out", "NewState", "InitialState"])
isInput    = (== "In" )
isOutput   = (== "Out")
isNewState = (== "NewState")
isTerminal s = isInput s || isOutput s

moduleAssign :: PinMap -> CompS -> [Decl]
-- Input comps are never assigned
moduleAssign _ (CompS _ "In" _ _ _) = [] 
-- moduleAssign _ (CompS _ "State" _ _ _) = [] 
-- moduleAssign _ (CompS _ "InitialState" _ _ _) = [] 
-- moduleAssign _ (CompS _ "NewState" _ _ _) = [] 
moduleAssign _ (CompS _ "delay" _ _ _) = []   -- treated specially
-- binary operations
moduleAssign p2w (CompS _ name [i0,i1] [o] _) = 
  [NetAssign (busName p2w o) (ExprBinary binOp i0E i1E)]
  where
    i0E = sourceExp p2w i0
    i1E = sourceExp p2w i1
    binOp = 
      case name of
        "and"  -> And
        "or"   -> Or
        "nor"  -> Nor
        "xor"  -> Xor
        "xnor" -> Xnor
        "eq"   -> Equals
        "neq"  -> NotEquals
        "add"  -> Plus
        "mul"  -> Times
        _      -> err 
    err = error $ "Circat.Netlist.moduleAssign: BinaryOp " 
                  ++ show name ++ " not supported."
moduleAssign p2w (CompS _ "if" [a,b,c] [o] _) =
  [NetAssign (busName p2w o)
    (ExprCond (sourceExp p2w a) (sourceExp p2w b) (sourceExp p2w c))]

-- unary operations                                                  
moduleAssign p2w c@(CompS _ name [i] [o] _) = 
  [NetAssign (busName p2w o) (ExprUnary unaryOp iE)]
  where
    iE = sourceExp p2w i
    unaryOp = case name of
                "not"   -> Neg
                "False" -> Neg          -- TODO: remove?
                _       -> err
    err = error $ "Circat.Netlist.moduleAssign: UnaryOp " 
                  ++ show name ++ " not supported." ++ show c

moduleAssign p2w (CompS _ name [] [o] _) = 
  [NetAssign (busName p2w o) (ExprLit Nothing val)]
  where 
    val = case name of 
            "True"      -> ExprBit T
            "False"     -> ExprBit F
            "undefined" -> ExprNum 0  -- default
            _           ->
              case reads name of
                [(n :: Int,"")] -> ExprNum (fromIntegral n)
                _ -> err $ "Literal " ++ name ++ " not recognized."
    err = error . ("Circat.Netlist.moduleAssign: " ++)

-- output assignments
moduleAssign p2w (CompS _ name ps [] _) | isOutput name || isNewState name =
  map (\ (n,p) -> NetAssign (outPortName n) (sourceExp p2w p)) (tagged ps)
 where
   outPortName = portName name ps

-- Upstream, we now remove components with unused outputs, including ()
-- moduleAssign _ (CompS _ "()" [] [] _) = []

-- HACK: Catch-all
moduleAssign p2w (CompS _ name is os _) = 
  [InstDecl name "inst" [] (port "i" is) (port "o" os)]
  where
    port s pins = [(s ++ show i, sourceExp p2w p) | p <- pins | i <- [0::Int ..]]

-- moduleAssign _ c = error $ "Circat.Netlist.moduleAssign: Comp " ++ show c 
--                            ++ " not supported."

-- TODO: Swap arguments in sourceExp, lw, lookupWireDesc

sourceExp :: PinMap -> Bus -> Expr
sourceExp p2w b = ExprVar (busName p2w b)

lw :: PinMap -> PinId -> PinDesc
lw = lookupWireDesc

lookupWireDesc :: PinMap -> PinId -> PinDesc
lookupWireDesc p2w pin = fromMaybe err (M.lookup pin p2w)
  where
    err = error $ "Circat.Netlist.lookupWireDesc: PinId " ++ show pin
                  ++ " does not have an entry."

busName :: PinMap -> Bus -> String
busName p2w (Bus i _) = snd (lw p2w i)

-- | Generates a wire declaration for all Comp outputs along with 
-- a map from PinId to wire name
moduleNets :: [CompS] -> (PinMap,[Decl])
moduleNets = mconcat . map moduleNet

moduleNet :: CompS -> (PinMap,[Decl])
moduleNet c | isTerminal (compName c) = mempty
moduleNet c =
  first M.fromList . unzip $
    [ ((o,(wid, wireName i)), valDecl (compName c) (wireName i) (Just (busRange wid)))
    | (i,Bus o wid) <- tagged outs ]
  where
    outs = compOuts c
    wireName i = "w_"++instName c++if length outs==1 then "" else "_"++show i

valDecl :: Name -> Ident -> Maybe Range -> Decl
valDecl "delay" s r = MemDecl s Nothing r Nothing
valDecl _       s r = NetDecl s r Nothing

busRange :: Width -> Range
busRange wid = Range (lit 0) (lit (wid - 1))
 where
   lit = ExprLit Nothing . ExprNum . fromIntegral

instName :: CompS -> String
instName (CompS num name _ _ _) = name ++"_I"++show num

type CompStuff = (PinMap,[(Ident, Maybe Range)]) -- TODO: Better name

-- | Bit-blasted list of inputs and outputs
modulePorts :: CompS -> CompStuff
modulePorts (CompS _  name ins outs _) = ports name ins <> ports name outs

ports :: Name -> [Bus] -> CompStuff
ports compNm ps =
  (first M.fromList . unzip)
    [ let name = portName compNm ps i in
        ((p,(wid,name)),(name,Just (busRange wid))) -- TODO: redesign
    | (i,Bus p wid) <- tagged ps ]

portName :: Show b => String -> [a] -> b  -> Ident
portName compNm ps i = 
  compNm ++ if length ps == 1 then "" else "_" ++ show i


-- | Given a list of simple Comps (CompS), retrieve 
-- the one comp with given name.
portComp :: String -> [CompS] -> CompS
portComp name comps =
 either error id (portCompMb name comps)

-- | Like 'portComp' but fails gracefully
portCompMb :: String -> [CompS] -> Either String CompS
portCompMb name comps =
  case fC of
    [c] -> Right c
    _   -> Left eIncorrectComps
  where 
    fC = filter ((== name) . compName) comps
    floc = "Circat.Netlist.portComp"
    eIncorrectComps = 
      floc ++ ": Incorrect number of comps named " ++ show name
           ++ " found in the list of comps. "
           ++ if length fC > 1 then " Multiple comps found " ++ show fC 
              else " No comps found."

-- TODO: Build a Name-to-CompS map and use repeatedly in portComp calls
