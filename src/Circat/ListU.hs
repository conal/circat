{-# LANGUAGE CPP #-}
-- #define ListRep
#define AsGADT

{-# LANGUAGE TypeOperators, TypeFamilies, Rank2Types #-}
{-# LANGUAGE LambdaCase #-}
#ifdef AsGADT
{-# LANGUAGE GADTs #-}
#else
{-# LANGUAGE ExistentialQuantification #-}
#endif
{-# OPTIONS_GHC -Wall #-}

#ifdef ListRep
{-# OPTIONS_GHC -fno-warn-orphans #-} -- TEMP
#endif
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.ListU
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Unfold-based lists
----------------------------------------------------------------------

module Circat.ListU where

-- TODO: explicit exports

import Data.List (unfoldr)

#ifdef ListRep
import Circat.Rep
#endif

#ifdef AsGADT
data ListU :: * -> * where
  UnfoldR :: (s -> Maybe (a,s)) -> s -> ListU a
#else
data ListU a = forall s. UnfoldR (s -> Maybe (a,s)) s
#endif

toListU :: [a] -> ListU a
toListU = UnfoldR (\ case []   -> Nothing
                          a:as -> Just (a, as))

unListU :: ListU a -> [a]
unListU (UnfoldR h s) = unfoldr h s

#ifdef ListRep
-- TODO: move this orphan to Circat.Rep, and remove -fno-warn-orphans above.
type instance Rep [a] = ListU a
instance HasRep [a] where
  repr = toListU
  abst = unListU
#endif

