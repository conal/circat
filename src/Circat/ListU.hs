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

import Data.Monoid (Monoid(..),Sum(..),Product(..))
import Data.Functor ((<$>))
import Data.Foldable (Foldable(..))
import Control.Arrow (first)
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

unfoldRU :: (s -> Maybe (a,s)) -> s -> ListU a
unfoldRU = UnfoldR

foldlU :: (b -> a -> b) -> b -> ListU a -> b
foldlU op b0 (UnfoldR h s0) = go b0 s0
 where
   go b s = case h s of
              Nothing     -> b
              Just (a,s') -> go (b `op` a) s'

-- Noting how `b` and `s` travel together, I suspect that we can define `foldlU`
-- in terms of a simpler state machine primitive.

dfa :: (s -> Maybe s) -> s -> s
dfa f = go where go s = maybe s go (f s)

-- dfa f = go
--  where
--    go s = case f s of
--             Nothing -> s
--             Just s' -> go s'

-- Now redefine `foldlU` via `dfa`:

foldlU2 :: (b -> a -> b) -> b -> ListU a -> b

-- foldlU' op b0 (UnfoldR h s0) = fst (dfa f (b0,s0))
--  where
--    f (b,s) = case h s of
--                Nothing     -> Nothing
--                Just (a,s') -> Just (b `op` a,s')

-- Equivalently (using the `Functor` instance for `Maybe` and `first`, which transforms the first member of a pair),

foldlU2 op b0 (UnfoldR h s0) = fst (dfa f (b0,s0))
 where
   f (b,s) = first (b `op`) <$> h s

-- The `dfa` definition above troubles me in that what would be the final state
-- in a DFA is replaced by `Nothing`, preventing us from extracting any
-- information. Instead, the previous state is returned. Here's a variant on
-- `dfa` from above, with a final value that might not be of state type:

dfa' :: (s -> Either a s) -> s -> a

-- dfa' f = go
--  where
--    go s = case f s of
--             Right s' -> go s'
--             Left  a  -> a

-- Equivalently,

-- dfa' f = go where go s = either id go (f s)

dfa' f = go where go = either id go . f

-- It's then easy to define the previous version of `dfa`:

dfa2 :: (s -> Maybe s) -> s -> s
dfa2 f = dfa' (\ s -> case f s of Nothing -> Left  s
                                  Just s' -> Right s')

-- dfa2 f = dfa' (\ s -> maybe (Left s) Right (f s))

-- or `dfa (flip maybe id)`, but I wouldn't go there.

-- We could also define variants for explicitly identifying final states.
-- For instance,

dfa'' :: (s -> s) -> (s -> Bool) -> s -> s
dfa'' f final = dfa' (\ s -> if final s then Left s else Right (f s))

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

mconcatU :: Monoid m => ListU m -> m
mconcatU = foldlU mappend mempty

instance Foldable ListU where
  foldMap f = mconcatU . fmap f

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

-- Alternative variable naming:
-- 
-- instance Applicative ListU where
--   pure a = UnfoldR (\ done -> if done then Nothing else Just (a,True)) False
--   UnfoldR p s0 <*> UnfoldR q t0 = UnfoldR r (s0,t0)
--    where
--      r (s,t) = case (p s, q t) of
--                  (Just (f,_ ), Just (x,t')) -> Just (f x, (s,t'))
--                  (Just (_,s'), Nothing)     -> r (s',t0)
--                  _                          -> Nothing

-- instance Monad ListU where
--   return = pure
--   UnfoldR p s0 >>= h = UnfoldR r (s0,?)
--    where
--      h (s,?) = case p s of
--                  Just (f,s') -> 

#endif

-- | Count from low to high inclusive
fromTo :: (Ord a, Enum a) => a -> a -> ListU a
fromTo low high = unfoldRU (\ n -> if n > high then Nothing else Just (n,succ n)) low

-- | Count from 0 to high inclusive
upTo :: (Enum a, Ord a, Num a) => a -> ListU a
upTo = fromTo 0
