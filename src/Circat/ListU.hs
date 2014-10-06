{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators, TypeFamilies, Rank2Types, ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wall #-}

-- #define ListRep

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

import Circat.Misc ((:*))
#ifdef ListRep
import Circat.Rep
#endif

data ListU a = forall s. ListU (s -> Maybe (a,s)) s

toListU :: [a] -> ListU a
toListU = ListU (\ case  []     -> Nothing
                         (a:as) -> Just (a, as))

unListU :: ListU a -> [a]
unListU (ListU h s) = unfoldr h s

-- unListU  (ListU f s0) = go s0
--  where
--    go s = case f s of Nothing -> []
--                       Just (a,s') -> a : go s'

#ifdef ListRep

type instance Rep [a] = ListU a
instance HasRep [a] where
  repr = toListU
  abst = unListU

#endif

