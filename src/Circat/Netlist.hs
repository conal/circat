{-# LANGUAGE TypeOperators, ConstraintKinds #-}

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
module Circat.Netlist 
  ( toNetlist, mk_module
  , genVHDL, V.ppModule
  , toV, outV) where

import Data.Functor ((<$>))
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as M

import System.Directory (createDirectoryIfMissing)

import Circat.Circuit
  ((:>), IsSource2, Comp', simpleComp, runC , tagged, CompNum, Pin)

import Language.Netlist.AST
  ( Module(..), Decl(..), Expr(..), ExprLit (..)
  , Bit (..), BinaryOp(..), UnaryOp(..), Ident, Range )

import Language.Netlist.GenVHDL(genVHDL)
import Language.Netlist.GenVerilog(mk_module)
import qualified Language.Verilog as V

type PinToWireName   = (Pin,String) 

outV :: IsSource2 a b => String -> (a :> b) -> IO ()
outV cirName cir = 
  do createDirectoryIfMissing False outDir
     writeFile filePath (toV cirName cir)
  where
    outDir   = "out"
    filePath = outDir ++ "/" ++ cirName ++ ".v"

toV :: IsSource2 a b => String -> (a :> b) -> String
toV cirName cir = show . V.ppModule . mk_module $ toNetlist cirName cir

-- | Converts a Circuit to a Module
toNetlist :: IsSource2 a b => String -> (a :> b) -> Module
toNetlist circuitName cir = Module circuitName ins outs [] (nets++assigns)
  where comps  = simpleComp <$> runC cir
        ncomps      = tagged comps
        (p2wM,ins)  = modulePorts (portComp "In" comps)
        (_,outs)    = modulePorts (portComp "Out" comps)
        (p2wI,nets) = moduleNets ncomps
        p2w         = M.fromList (p2wM ++ p2wI)
        assigns     = moduleAssigns p2w ncomps 

-- | Produces the assign statements for every Comp except "In"
-- Assign statements bind the result of a function (and,or,add etc.)
-- to a variable name which is a wire in verilog parlance
-- eg. w_xor_I1 = In_0 ^ In_1 // (`^` is xor)
moduleAssigns :: Map Pin String -> [(CompNum,Comp')] -> [Decl]
moduleAssigns p2w = concatMap (moduleAssign p2w)

moduleAssign :: Map Pin String -> (CompNum,Comp') -> [Decl]
-- "In" comps are never assigned
moduleAssign _ (_,("In",_,_)) = [] 
-- binary operations
moduleAssign p2w (_,(name,[i0,i1],[o])) = 
  [NetAssign (lw o p2w) (ExprBinary binOp i0E i1E)]
  where
    i0E = expVar i0 p2w
    i1E = expVar i1 p2w
    binOp = 
      case name of
        "and"  -> And
        "or"   -> Or
        "nor"  -> Nor
        "xor"  -> Xor
        "xnor" -> Xnor
        "eq"   -> Equals
        "neq"  -> NotEquals
        _      -> err 
    err = error $ "Circat.Netlist.moduleAssign: BinaryOp " 
                  ++ show name ++ " not supported."

-- unary operations                                                  
moduleAssign p2w c@(_,(name,[i],[o])) = 
  [NetAssign (lw o p2w) (ExprUnary unaryOp iE)]
  where
    iE = expVar i p2w
    unaryOp = case name of
                "not"   -> Neg
                "False" -> Neg
                _       -> err
    err = error $ "Circat.Netlist.moduleAssign: UnaryOp " 
                  ++ show name ++ " not supported." ++ show c

-- constant sources
moduleAssign p2w (_,(name,[],[o])) = 
  [NetAssign (lw o p2w) (ExprLit Nothing (ExprBit bit))] 
  where 
    bit = case name of 
            "True"  -> T
            "False" -> F
            _       -> error $ "Circat.Netlist.moduleAssign: Literal "
                                ++ name ++ " not recognized."

-- output assignments
moduleAssign p2w (_,("Out",ps,[])) =
  map (\(n,p) -> NetAssign (outPortName n) (expVar p p2w)) (tagged ps)
  where
     outPortName = portName "Out" ps
     
moduleAssign _ c = error $ "Circat.Netlist.moduleAssign: Comp " ++ show c 
                           ++ " not supported."

expVar :: Pin -> Map Pin String -> Expr
expVar p p2w = ExprVar (lw p p2w)

lw :: Pin -> Map Pin String -> String
lw = lookupWireName

lookupWireName :: Pin -> Map Pin String -> String
lookupWireName pin p2w = fromMaybe err (M.lookup pin p2w)
  where
    err = error $ "Circat.Netlist.lookupWireName: Pin " ++ show pin
                  ++ " does not have a wire name."
    
-- | Generates a wire declaration for all Comp outputs along with 
-- a map from Pin to wire name
moduleNets :: [(CompNum,Comp')] -> ([PinToWireName],[Decl])
moduleNets = unzip . concatMap moduleNet

moduleNet :: (CompNum,Comp') -> [(PinToWireName,Decl)]
moduleNet (_,("In",_,_))      = []
moduleNet (_,("Out",_,_))     = []
moduleNet c@(_,(_,_,outs)) = 
  [((outs!!i,wireName i), NetDecl (wireName i) Nothing Nothing) | i <- [0..length outs-1]]
  where
    wireName i = "w_"++instName c++if length outs==1 then "" else "_"++show i

-- TODO: Wherever we see !!, we're doing a linear-time operation that could be
-- done in log time instead. Consider changing the representation to from [] to
-- IntMap.

instName :: (CompNum,Comp') -> String
instName (num,(name,_,_)) = name ++"_I"++show num

-- | Generates a bit-blasted list of primary inputs of
-- the module.
modulePorts :: Comp' -> ([PinToWireName],[(Ident, Maybe Range)])
modulePorts comp' = 
  case comp' of 
    ("In", [], outs) -> unzip (ports "In" outs)
    ("Out",ins,[])   -> ([],map snd $ ports "Out" ins) 
    _                -> 
      error $ "Circat.Netlist.modulePorts: Comp " ++ show comp' 
               ++ " not recognized." 
  where
    ports dir ps =  
      [ let name = portName dir ps i in ((ps!!i,name),(name,Nothing)) 
      | i <- [0..length ps-1]
      ]

portName :: (Show b) => String -> [a] -> b  -> String
portName dir ps i = 
  dir++if length ps == 1 then "" else "_" ++ show i

-- | Given a list of simple Comps (Comp'), retrieve 
-- the comp named dir. `dir` can have the values of 
-- "In" or "Out"
portComp :: String -> [Comp'] -> Comp'
portComp dir comps
  | dir /= "In" && dir /= "Out" = error eIllegalDir 
  | length fC == 1              = head fC
  | otherwise                   = error eIncorrectComps
  where 
    fC = filter (\(n,_,_) -> n == dir) comps
    floc = "Circat.Netlist.gPortComp"
    eIllegalDir = 
      floc ++ ": Illegal value for dir " ++ dir
           ++ ". Valid values are In or Out"            
    eIncorrectComps = 
      floc ++ ": Incorrect number of comps named " ++ dir 
           ++ " found in the list of comps. "
           ++ if length fC > 1 then " Multiple comps found " ++ show fC 
              else " No comps found."

