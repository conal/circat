{-# LANGUAGE CPP #-}
-- #define ListRep
#define AsGADT

{-# LANGUAGE TypeOperators, TypeFamilies, Rank2Types #-}
{-# LANGUAGE LambdaCase, TupleSections #-}
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

import Data.Monoid (Monoid(..))
import Control.Arrow (first,second)
import Control.Applicative (Applicative(..))
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

instance Monoid (ListU a) where
  mempty = UnfoldR (const Nothing) undefined
  UnfoldR f s0 `mappend` UnfoldR g t0 = UnfoldR h u0
   where
     u0 = Left s0
     h (Left  s) = case f s of
                     Nothing     -> h (Right t0)
                     Just (a,s') -> Just (a, Left s')
     h (Right t) = case g t of
                     Nothing     -> Nothing
                     Just (a,t') -> Just (a, Right t')

-- Alternatively,
--
--      h (Left  s) = maybe (h (Right t0)) (Just . second Left) (f s)
--      h (Right t) = (fmap.second) Right (g t)

instance Functor ListU where
  fmap f (UnfoldR h s0) = UnfoldR ((fmap.fmap.first) f h) s0

--   UnfoldR (\ s -> case h s of
--                     Nothing -> Nothing
--                     Just (a,s') -> Just (f a, s')) s0

-- Synchronous version, i.e., homomorphic with ZipList rather than []

-- #define LikeZipList

#ifdef LikeZipList

instance Applicative ListU where
  pure a = UnfoldR (\ s -> Just (a,s)) ()
  UnfoldR hf sf0 <*> UnfoldR hx sx0 = UnfoldR h (sf0,sx0)
   where
     h (sf,sx) = case (hf sf, hx sx) of
                   (Just (f,sf'), Just (x,sx')) -> Just (f x, (sf',sx'))
                   _                            -> Nothing

#else

instance Applicative ListU where
  pure a = UnfoldR (\ done -> if done then Nothing else Just (a,True)) False
  UnfoldR hf sf0 <*> UnfoldR hx sx0 = UnfoldR h (sf0,sx0)
   where
     h (sf,sx) = case (hf sf, hx sx) of
                   (Just (f,_  ), Just (x,sx')) -> Just (f x, (sf,sx'))
                   (Just (_,sf'), Nothing)      -> h (sf',sx0)
                   _                            -> Nothing

-- Note the recursion in h, which could be removed as in the "nothing at all"
-- paper. Note also the redundant application of hf sf, which could perhaps be
-- cached in the state if we could save functions.

#endif
