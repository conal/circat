{-# LANGUAGE TypeOperators, ConstraintKinds, FlexibleContexts, CPP #-}
{-# LANGUAGE ViewPatterns, ParallelListComp, ScopedTypeVariables #-}

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

-- TODO: Use Text.Printf to replace the awkward string formations in this
-- module.

module Circat.Netlist
  ( toNetlist, mk_module
  , genVHDL, V.ppModule
  , outV  -- phasing out
  , saveAsVerilog
  ) where

import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as M
import Text.Printf (printf)

import System.Directory (createDirectoryIfMissing)

import Circat.Circuit
  ( (:>), GenBuses, CompS(..), compName, compOuts, tagged
  , Width, PinId, Bus(..)
  , Name,unitize,DGraph,mkGraph,Report)

import Language.Netlist.AST
  ( Module(..), Decl(..), Expr(..), ExprLit (..), Bit(..), Range(..)
  , BinaryOp(..), UnaryOp(..), Ident, Range )

import Language.Netlist.GenVHDL(genVHDL)
import Language.Netlist.GenVerilog(mk_module)
import qualified Language.Verilog as V

-- PinId description: width & name
type PinDesc = (Width,String)

type PinToWireDesc = (PinId,PinDesc) 

#if 1
-- TODO: Phase out
outV :: GenBuses a => Name -> (a :> b) -> IO ()
outV name circ = saveVerilog name' (toVerilog ndr)
 where
   ndr@(name',_,_) = mkGraph name (unitize circ)

-- | Converts a Circuit to a Module
toNetlist :: Name -> DGraph -> Module
toNetlist name comps = Module name ins outs [] (nets++assigns)
  where (p2wM,ins)  = modulePorts (portComp "In"  comps)
        (_,outs)    = modulePorts (portComp "Out" comps)
        (p2wI,nets) = moduleNets comps
        p2w         = M.fromList (p2wM ++ p2wI)
        assigns     = moduleAssigns p2w comps

toVerilog :: (Name,DGraph,Report) -> String
toVerilog (name,graph,report) =
  printf "%s\n\n// %s\n"
   (show (V.ppModule (mk_module (toNetlist name graph))))
   report

saveAsVerilog :: (Name,DGraph,Report) -> IO ()
saveAsVerilog gg@(name,_,_) = saveVerilog name (toVerilog gg)

saveVerilog :: Name -> String -> IO ()
saveVerilog name verilog =
  do createDirectoryIfMissing False outDir
     writeFile filePath verilog
     putStrLn ("Wrote " ++ filePath)
  where
    outDir   = "out"
    filePath = outDir ++ "/" ++ name ++ ".v.txt"

#else
outV :: GenBuses a => String -> (a :> b) -> IO ()
outV cirName cir = 
  do createDirectoryIfMissing False outDir
     writeFile filePath (toV cirName cir)
     putStrLn ("Wrote " ++ filePath)
  where
    outDir   = "out"
    filePath = outDir ++ "/" ++ cirName ++ ".v.txt"

toV :: GenBuses a => String -> (a :> b) -> String
toV cirName cir = show . V.ppModule . mk_module $ toNetlist cirName cir

-- | Converts a Circuit to a Module
toNetlist :: GenBuses a => String -> (a :> b) -> Module
toNetlist circuitName cir = Module circuitName ins outs [] (nets++assigns)
  where (comps,_)   = circuitGraph cir
        (p2wM,ins)  = modulePorts (portComp "In"  comps)
        (_,outs)    = modulePorts (portComp "Out" comps)
        (p2wI,nets) = moduleNets comps
        p2w         = M.fromList (p2wM ++ p2wI)
        assigns     = moduleAssigns p2w comps

#endif

type PinMap = Map PinId PinDesc

-- | Produces the assign statements for every Comp except "In"
-- Assign statements bind the result of a function (and,or,add etc.)
-- to a variable name which is a wire in verilog parlance
-- eg. w_xor_I1 = In_0 ^ In_1 // (`^` is xor)
moduleAssigns :: PinMap -> [CompS] -> [Decl]
moduleAssigns p2w = concatMap (moduleAssign p2w)

moduleAssign :: PinMap -> CompS -> [Decl]
-- "In" comps are never assigned
moduleAssign _ (CompS _ "In" _ _ _) = [] 
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
                "False" -> Neg
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
moduleAssign p2w (CompS _ "Out" ps [] _) =
  map (\ (n,p) -> NetAssign (outPortName n) (sourceExp p2w p)) (tagged ps)
  where
     outPortName = portName "Out" ps

-- We now remove components with unused outputs, including ()
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
moduleNets :: [CompS] -> ([PinToWireDesc],[Decl])
moduleNets = unzip . concatMap moduleNet

moduleNet :: CompS -> [(PinToWireDesc,Decl)]
moduleNet c | compName c `elem` ["In","Out"] = []
moduleNet c = 
  [ ((o,(wid, wireName i)), NetDecl (wireName i) (Just (busRange wid)) Nothing)
  | (i,Bus o wid) <- tagged outs ]
  where
    outs = compOuts c
    wireName i = "w_"++instName c++if length outs==1 then "" else "_"++show i

busRange :: Width -> Range
busRange wid = Range (lit 0) (lit (wid - 1))
 where
   lit = ExprLit Nothing . ExprNum . fromIntegral

instName :: CompS -> String
instName (CompS num name _ _ _) = name ++"_I"++show num

-- | Generates a bit-blasted list of primary inputs of
-- the module.
modulePorts :: CompS -> ([PinToWireDesc],[(Ident, Maybe Range)])
modulePorts comp' = 
  case comp' of 
    (CompS _  "In"  []  outs _) -> unzip (ports "In" outs)
    (CompS _  "Out" ins [] _)   -> ([],map snd $ ports "Out" ins) 
    _                   -> 
      error $ "Circat.Netlist.modulePorts: Comp " ++ show comp' 
               ++ " not recognized." 
  where
    ports :: String -> [Bus] -> [(PinToWireDesc,(Ident, Maybe Range))]
    ports dir ps =
      [ let name = portName dir ps i in
          ((p,(wid,name)),(name,Just (busRange wid))) -- TODO: redesign
      | (i,Bus p wid) <- tagged ps
      ]

portName :: Show b => String -> [a] -> b  -> String
portName dir ps i = 
  dir++if length ps == 1 then "" else "_" ++ show i

-- | Given a list of simple Comps (CompS), retrieve 
-- the comp named dir. `dir` can have the values of 
-- "In" or "Out"
portComp :: String -> [CompS] -> CompS
portComp dir comps
  | dir /= "In" && dir /= "Out" = error eIllegalDir 
  | length fC == 1              = head fC
  | otherwise                   = error eIncorrectComps
  where 
    fC = filter ((== dir) . compName) comps
    floc = "Circat.Netlist.portComp"
    eIllegalDir = 
      floc ++ ": Illegal value for dir " ++ dir
           ++ ". Valid values are In or Out"            
    eIncorrectComps = 
      floc ++ ": Incorrect number of comps named " ++ show dir
           ++ " found in the list of comps. "
           ++ if length fC > 1 then " Multiple comps found " ++ show fC 
              else " No comps found."
