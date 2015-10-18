{-# LANGUAGE TypeOperators, ConstraintKinds, FlexibleContexts, CPP #-}
{-# LANGUAGE ViewPatterns, PatternGuards, ParallelListComp, ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  Circat.Netlist
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

import Data.Monoid (mempty,(<>),mconcat)
import Control.Arrow (first)
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Char (isDigit)
import Text.Printf (printf)

import System.Directory (createDirectoryIfMissing)

import Circat.Circuit
  ( CompS(..), compOuts, compName, compOuts, tagged
  , Width, PinId, Bus(..),Name,DGraph,GraphInfo
  , (:>), GenBuses,unitize,mkGraph,unDelayName
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
toNetlist name comps =
  Module name' (clockIns++ins) outs [] (nets++assigns++clockDecls)
 where
   (p2wIn,ins)    = modPorts "In"
   (_,outs)       = modPorts "Out"
   (p2wNets,nets) = moduleNets comps
   p2w            = p2wIn <> p2wNets
   assigns        = moduleAssigns p2w comps
   modPorts str   = maybe mempty modulePorts (portComp str comps)
   (clockIns,clockDecls) = clocked p2w comps
   name' = map tweak name
    where
      tweak '-' = '_'
      tweak c   = c

-- Whether to handle dynamic reset vs initialization.
withReset :: Bool
withReset = True

clocked :: PinMap -> DGraph -> ([(Ident,Maybe Range)],[Decl])
clocked p2w comps
  | null states = mempty
  | otherwise =
      ( ("clock",Nothing) : if withReset then [("reset",Nothing)] else []
      , [ProcessDecl
           (Event (ExprVar "clock") PosEdge) Nothing
           (if withReset then
             If (ExprBinary Equals
                  (ExprVar "reset") (ExprLit Nothing (ExprBit T)))
                (updates starts)
                (Just (updates news))
            else
              updates news)] )
 where
  starts,news,states :: [Expr]
  (starts,news,states) =
    unzip3 [ (start,var new,var state)
           | CompS _ (delayStart -> Just start) [new] [state] _ <- comps]
  var :: Bus -> Expr
  var = sourceExp p2w  -- Move to view pattern
  updates :: [Expr] -> Stmt
  updates sources = sseq (zipWith Assign states sources)

delayStart :: Name -> Maybe Expr
delayStart = fmap readLitExpr . unDelayName

readLitExpr :: String -> Expr
readLitExpr = ExprLit Nothing . lit
 where
   lit :: String -> ExprLit
   lit "False" = ExprBit F
   lit "True"  = ExprBit T
   lit (reads -> [(n,"")]) = ExprNum n
   lit s = error ("Circat.Netlist.clocked.lit: bad lit: " ++ s)

--   always @ (posedge clock)
--     if (reset == 1'b1) begin s0 <= inits0; ... end
--     else begin s0 <= t0; ... end
--   end

-- Statment Seq tidied for singletons sequences.
sseq :: [Stmt] -> Stmt
sseq [s] = s
sseq ss = Seq ss

-- TODO: Rework toNetlist with a Writer monad, aggregating a PinMap.
-- Ditto for modulePorts and moduleNets.
-- Maybe gather the ins & outs similarly in the monoid.
-- Maybe then a Reader with the same info for moduleAssigns.

toVerilog :: GraphInfo -> String
toVerilog (name,M.keys -> graph,_report) =
  printf "%s"
   (show (V.ppModule (mk_module (toNetlist name graph))))

saveAsVerilog :: GraphInfo -> IO ()
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
-- etc.) to a variable name which is a wire in verilog parlance eg. xor_I1 =
-- In_0 ^ In_1 // (`^` is xor)
moduleAssigns :: PinMap -> [CompS] -> [Decl]
moduleAssigns p2w = concatMap (moduleAssign p2w)

isInput, isOutput, isTerminal :: String -> Bool
isInput  = (== "In" )
isOutput = (== "Out")
isTerminal s = isInput s || isOutput s

moduleAssign :: PinMap -> CompS -> [Decl]

moduleAssign _ (CompS _ "In"    _ _ _) = [] 

moduleAssign _ (CompS _ (delayStart -> Just _) _ _ _) = []   -- see clocked

-- binary operations
moduleAssign p2w (CompS _ name [i0,i1] [o] _) = 
  [NetAssign (busName p2w o) (ExprBinary binOp i0E i1E)]
  where
    i0E   = sourceExp p2w i0
    i1E   = sourceExp p2w i1
    binOp = fromMaybe err (translateBinOp name)
    err   = error $ "Circat.Netlist.moduleAssign: BinaryOp " 
                    ++ show name ++ " not supported."

moduleAssign p2w (CompS _ "if" [a,b,c] [o] _) =
  [NetAssign (busName p2w o)
    (ExprCond (sourceExp p2w a) (sourceExp p2w b) (sourceExp p2w c))]

moduleAssign p2w (CompS _ "Bool→Int" [i] [o] _) = 
  [NetAssign (busName p2w o) (sourceExp p2w i)]  -- implicit conversion

-- unary operations                                                  
moduleAssign p2w c@(CompS _ name [i] [o] _) = 
  [NetAssign (busName p2w o) (ExprUnary unOp iE)]
  where
    iE = sourceExp p2w i
    unOp = fromMaybe err (translateUnOp name)
    err = error $ "Circat.Netlist.moduleAssign: UnaryOp " 
                  ++ show name ++ " not supported." ++ show c

moduleAssign p2w (CompS _ name [] [o] _) = 
  [NetAssign (busName p2w o) (ExprLit Nothing val)]
  where 
    val = case name of 
            "True"  -> ExprBit T
            "False" -> ExprBit F
            "⊥"     -> ExprNum 0  -- default
            _       ->
              case reads name of
                [(n :: Int   ,"")] -> ExprNum (fromIntegral n)
                -- Uh oh! There doesn't seem to be a Netlist representation for
                -- real-valued literals, although at least Verilog supports it.
                -- [(x :: Double,"")] -> ExprNum (fromIntegral n)
                _ -> err $ "Literal " ++ name ++ " not recognized."
    err = error . ("Circat.Netlist.moduleAssign: " ++)

-- output assignments
moduleAssign p2w (CompS _ name ps [] _) | isOutput name =
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

-- (x≡y ∨ x≠y) ∧ (x<y ∨ x≥y) ∧ (x>y ∨ x≤y)

translateUnOp  :: String -> Maybe UnaryOp
translateUnOp  = \ case
  "¬"      -> Just Neg
  "not"    -> Just Neg
  "negate" -> Just UMinus
  _        -> Nothing

translateBinOp :: String -> Maybe BinaryOp
translateBinOp = \ case
  "≡"   -> Just Equals
  "=="  -> Just Equals
  "≠"   -> Just NotEquals
  "/="  -> Just NotEquals
  "<"   -> Just LessThan
  ">"   -> Just GreaterThan
  "≤"   -> Just LessEqual
  "<="  -> Just LessEqual
  "≥"   -> Just GreaterEqual
  ">="  -> Just GreaterEqual
  "+"   -> Just Plus
  "−"   -> Just Minus
  "×"   -> Just Times
  "*"   -> Just Times
  "∧"   -> Just And
  "&&"  -> Just And
  "∨"   -> Just Or
  "||"  -> Just Or
  "⊕"   -> Just Xor
  "xor" -> Just Xor
  _     -> Nothing

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
    wireName i = instName c++if length outs==1 then "" else "_"++show i

valDecl :: Name -> Ident -> Maybe Range -> Decl
valDecl (delayStart -> Just x0) s r =
  MemDecl s Nothing r (if withReset then Nothing else Just [x0])
valDecl _                       s r =
  NetDecl s r Nothing

busRange :: Width -> Range
busRange wid = Range (lit (wid - 1)) (lit 0)
 where
   lit = ExprLit Nothing . ExprNum . fromIntegral

instName :: CompS -> String
instName (CompS num (tweakName -> name') _ _ _) = name' ++"_I"++show num

tweakName :: String -> String
-- tweakName "undefined"                 = "⊥"
-- tweakName "if"                        = "Cond"
tweakName (translateUnOp  -> Just op) = show op
tweakName (translateBinOp -> Just op) = show op
tweakName name = prefix name ++ map tweakC name
 where
   -- Added for delay components.
   tweakC ' ' = '_'
   tweakC c   = c
   prefix (c:_) | isDigit c = "Const_"
   prefix _                 = ""

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
portComp :: String -> [CompS] -> Maybe CompS
portComp name comps =
  case filter ((== name) . compName) comps of
    [c] -> Just c
    _   -> Nothing

-- TODO: Build a Name-to-CompS map and use repeatedly in portComp calls
