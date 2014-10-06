-- {-# LANGUAGE #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.ShowUtils
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Show-related utilities
----------------------------------------------------------------------

module Circat.ShowUtils (Show'(..)) where

-- Show for all type arguments
class Show' f where
  show'      ::        f a -> String
  showsPrec' :: Int -> f a -> ShowS
  showsPrec' _ x s = show' x ++ s
  show' x          = showsPrec' 0 x ""
