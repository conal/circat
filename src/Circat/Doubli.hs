{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Doubli
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- newtype wrapper around Double to work around a problem finding instances
-- defined in GHC.Float.
----------------------------------------------------------------------

module Circat.Doubli where

import Control.Arrow (first)

newtype Doubli = Doubli Double
 deriving (Enum,Eq,Floating,Fractional,Num,Ord,Real,RealFloat,RealFrac)

instance Show Doubli where
  showsPrec p (Doubli d) = showsPrec p d

instance Read Doubli where
  readsPrec p str = first Doubli <$> readsPrec p str
  -- readsPrec p str = fmap (first Doubli) (readsPrec p str)
  -- readsPrec p = map (first Doubli) . readsPrec p
