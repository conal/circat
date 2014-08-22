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
  , toV, outV) where

import Data.Functor ((<$>))
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as M

import System.Directory (createDirectoryIfMissing)

import Circat.Circuit
  ( (:>), GenBuses, Source(..), Comp', simpleComp, runC, tagged
  , Width, CompNum, PinId, Bus(..) )

import Language.Netlist.AST
  ( Module(..), Decl(..), Expr(..), ExprLit (..), Range(..)
  , Bit (..), BinaryOp(..), UnaryOp(..), Ident, Range )

import Language.Netlist.GenVHDL(genVHDL)
import Language.Netlist.GenVerilog(mk_module)
import qualified Language.Verilog as V

-- PinId description: width & name
type PinDesc = (Width,String)

type PinToWireDesc = (PinId,PinDesc) 

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
  where comps  = simpleComp <$> runC cir
        ncomps      = tagged comps
        (p2wM,ins)  = modulePorts (portComp "In"  comps)
        (_,outs)    = modulePorts (portComp "Out" comps)
        (p2wI,nets) = moduleNets ncomps
        p2w         = M.fromList (p2wM ++ p2wI)
        assigns     = moduleAssigns p2w ncomps 

type PinMap = Map PinId PinDesc

-- | Produces the assign statements for every Comp except "In"
-- Assign statements bind the result of a function (and,or,add etc.)
-- to a variable name which is a wire in verilog parlance
-- eg. w_xor_I1 = In_0 ^ In_1 // (`^` is xor)
moduleAssigns :: PinMap -> [(CompNum,Comp')] -> [Decl]
moduleAssigns p2w = concatMap (moduleAssign p2w)

moduleAssign :: PinMap -> (CompNum,Comp') -> [Decl]
-- "In" comps are never assigned
moduleAssign _ (_,("In",_,_)) = [] 
-- binary operations
moduleAssign p2w (_,(name,[i0,i1],[o])) = 
  [NetAssign (sourceName p2w o) (ExprBinary binOp i0E i1E)]
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
moduleAssign p2w (_,("mux",[a,b,c],[o])) =
  [NetAssign (sourceName p2w o)
    (ExprCond (sourceExp p2w a) (sourceExp p2w b) (sourceExp p2w c))]

-- unary operations                                                  
moduleAssign p2w c@(_,(name,[i],[o])) = 
  [NetAssign (sourceName p2w o) (ExprUnary unaryOp iE)]
  where
    iE = sourceExp p2w i
    unaryOp = case name of
                "not"   -> Neg
                "False" -> Neg
                _       -> err
    err = error $ "Circat.Netlist.moduleAssign: UnaryOp " 
                  ++ show name ++ " not supported." ++ show c

#if 0
-- Now handled in sourceExp
-- constant sources
moduleAssign p2w (_,(name,[],[o])) = 
  [NetAssign (sourceName p2w o) (ExprLit Nothing val)]
  where 
    val = case name of 
            "True"  -> ExprBit T
            "False" -> ExprBit F
            _       ->
              case reads name of
                [(n :: Int,"")] -> ExprNum (fromIntegral n)
                _ -> error $ "Circat.Netlist.moduleAssign: Literal "
                              ++ name ++ " not recognized."
#endif

-- output assignments
moduleAssign p2w (_,("Out",ps,[])) =
  map (\ (n,p) -> NetAssign (outPortName n) (sourceExp p2w p)) (tagged ps)
  where
     outPortName = portName "Out" ps

-- HACK: Catch-all
moduleAssign _ (_,("()",[],[])) = []
moduleAssign p2w (_,(name,is,os)) = 
  [InstDecl name "inst" [] (port "i" is) (port "o" os)]
  where
    port s pins = [(s ++ show i, sourceExp p2w p) | p <- pins | i <- [0::Int ..]]

-- moduleAssign _ c = error $ "Circat.Netlist.moduleAssign: Comp " ++ show c 
--                            ++ " not supported."

-- TODO: Swap arguments in sourceExp, lw, lookupWireDesc

sourceExp :: PinMap -> Source -> Expr
sourceExp p2w (BusS  b) = ExprVar (busName p2w b)
sourceExp _   (BoolS x) = ExprLit Nothing (ExprBit (if x then T else F))
sourceExp _   (IntS  x) = ExprLit Nothing (ExprNum (fromIntegral x))

lw :: PinMap -> PinId -> PinDesc
lw = lookupWireDesc

lookupWireDesc :: PinMap -> PinId -> PinDesc
lookupWireDesc p2w pin = fromMaybe err (M.lookup pin p2w)
  where
    err = error $ "Circat.Netlist.lookupWireDesc: PinId " ++ show pin
                  ++ " does not have an entry."

busName :: PinMap -> Bus -> String
busName p2w (Bus i _) = snd (lw p2w i)

sourceName :: PinMap -> Source -> String
sourceName p2w (BusS b) = busName p2w b

-- | Generates a wire declaration for all Comp outputs along with 
-- a map from PinId to wire name
moduleNets :: [(CompNum,Comp')] -> ([PinToWireDesc],[Decl])
moduleNets = unzip . concatMap moduleNet

moduleNet :: (CompNum,Comp') -> [(PinToWireDesc,Decl)]
moduleNet (_,("In",_,_))      = []
moduleNet (_,("Out",_,_))     = []
moduleNet c@(_,(_,_,outs)) = 
  [ ((o,(wid, wireName i)), NetDecl (wireName i) (Just (busRange wid)) Nothing)
  | (i,BusS (Bus o wid)) <- tagged outs ]
  where
    wireName i = "w_"++instName c++if length outs==1 then "" else "_"++show i

busRange :: Width -> Range
busRange wid = Range (lit 0) (lit (wid - 1))
 where
   lit = ExprLit Nothing . ExprNum . fromIntegral

instName :: (CompNum,Comp') -> String
instName (num,(name,_,_)) = name ++"_I"++show num

-- | Generates a bit-blasted list of primary inputs of
-- the module.
modulePorts :: Comp' -> ([PinToWireDesc],[(Ident, Maybe Range)])
modulePorts comp' = 
  case comp' of 
    ("In", [], outs) -> unzip (ports "In" outs)
    ("Out",ins,[])   -> ([],map snd $ ports "Out" ins) 
    _                -> 
      error $ "Circat.Netlist.modulePorts: Comp " ++ show comp' 
               ++ " not recognized." 
  where
    ports :: String -> [Source] -> [(PinToWireDesc,(Ident, Maybe Range))]
    ports dir ps =
      [ let name = portName dir ps i in
          ((p,(wid,name)),(name,Just (busRange wid))) -- TODO: redesign
      | (i,BusS (Bus p wid)) <- tagged ps
      ]

portName :: Show b => String -> [a] -> b  -> String
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
    fC = filter (\ (n,_,_) -> n == dir) comps
    floc = "Circat.Netlist.gPortComp"
    eIllegalDir = 
      floc ++ ": Illegal value for dir " ++ dir
           ++ ". Valid values are In or Out"            
    eIncorrectComps = 
      floc ++ ": Incorrect number of comps named " ++ dir 
           ++ " found in the list of comps. "
           ++ if length fC > 1 then " Multiple comps found " ++ show fC 
              else " No comps found."
