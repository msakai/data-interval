{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, BangPatterns, TupleSections #-}
{-# LANGUAGE Safe #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.IntervalMap.Base
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (BangPatterns, TupleSections)
--
-- Mapping from intervals to values.
--
-- API of this module is strict in both the keys and the values.
-- If you need value-lazy maps, use "Data.IntervalMap.Lazy" instead.
-- The 'IntervalMap' type itself is shared between the lazy and strict modules,
-- meaning that the same 'IntervalMap' value can be passed to functions in
-- both modules (although that is rarely needed).
--
-- These modules are intended to be imported qualified, to avoid name
-- clashes with Prelude functions, e.g.
--
-- >  import Data.IntervalMap.Strict (IntervalMap)
-- >  import qualified Data.IntervalMap.Strict as IntervalMap
--
-----------------------------------------------------------------------------
module Data.IntervalMap.Strict
  (
  -- * Strictness properties
  -- $strictness

  -- * IntervalMap type
    IntervalMap
  , module Data.ExtendedReal

  -- * Operators
  , (!)
  , (\\)

  -- * Query
  , null
  , member
  , notMember
  , lookup
  , findWithDefault
  , span

  -- * Construction
  , whole
  , empty
  , singleton

  -- ** Insertion
  , insert
  , insertWith

  -- ** Delete\/Update
  , delete
  , adjust
  , update
  , alter

  -- * Combine
  , union
  , unionWith
  , unions
  , unionsWith
  , intersection
  , intersectionWith
  , difference

  -- * Traversal
  , map
  , mapKeysMonotonic

  -- * Conversion
  , elems
  , keys
  , assocs
  , keysSet

  -- ** List
  , fromList
  , fromListWith
  , toList

  -- ** Ordered List
  , toAscList
  , toDescList

  -- * Filter
  , filter
  , split

  -- * Submap
  , isSubmapOf
  , isSubmapOfBy
  , isProperSubmapOf
  , isProperSubmapOfBy
  )
  where


import Prelude hiding (null, lookup, map, filter, span)
import Data.ExtendedReal
import Data.Interval (Interval)
import qualified Data.Interval as Interval
import Data.IntervalMap.Base hiding
  ( whole
  , singleton
  , insert
  , insertWith
  , adjust
  , update
  , alter
  , unionWith
  , unionsWith
  , intersectionWith
  , map
  , fromList
  , fromListWith
  )
import qualified Data.IntervalMap.Base as B
import qualified Data.IntervalSet as IntervalSet
import Data.List (foldl')
import qualified Data.Map.Strict as Map
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<$>))
#endif

-- $strictness
--
-- This module satisfies the following strictness properties:
--
-- 1. Key arguments are evaluated to WHNF;
--
-- 2. Keys and values are evaluated to WHNF before they are stored in
--    the map.
--
-- Here's an example illustrating the first property:
--
-- > delete undefined m  ==  undefined
--
-- Here are some examples that illustrate the second property:
--
-- > map (\ v -> undefined) m  ==  undefined      -- m is not empty
-- > mapKeysMonotonic (\ k -> undefined) m  ==  undefined  -- m is not empty

-- | The map that maps whole range of k to a.
whole :: Ord k => a -> IntervalMap k a
whole !a = B.whole a

-- | A map with a single interval.
singleton :: Ord k => Interval k -> a -> IntervalMap k a
singleton i !a = B.singleton i a

-- | insert a new key and value in the map.
-- If the key is already present in the map, the associated value is
-- replaced with the supplied value.
insert :: Ord k => Interval k -> a -> IntervalMap k a -> IntervalMap k a
insert i !a m = B.insert i a m

-- | Insert with a function, combining new value and old value.
-- @'insertWith' f key value mp@ will insert the pair (interval, value) into @mp@.
-- If the interval overlaps with existing entries, the value for the entry is replace
-- with @(f new_value old_value)@.
insertWith :: Ord k => (a -> a -> a) -> Interval k -> a -> IntervalMap k a -> IntervalMap k a
insertWith _ i _ m | Interval.null i = m
insertWith f i !a m = alter g i m
  where
    g Nothing = Just a
    g (Just a') = Just $! f a a'

-- | Update a value at a specific interval with the result of the provided function.
-- When the interval does not overlatp with the map, the original map is returned.
adjust :: Ord k => (a -> a) -> Interval k -> IntervalMap k a -> IntervalMap k a
adjust f = update (Just . f)

-- | The expression (@'update' f i map@) updates the value @x@
-- at @i@ (if it is in the map). If (@f x@) is 'Nothing', the element is
-- deleted. If it is (@'Just' y@), the key @i@ is bound to the new value @y@.
update :: Ord k => (a -> Maybe a) -> Interval k -> IntervalMap k a -> IntervalMap k a
update _ i m | Interval.null i = m
update f i m =
  case split i m of
    (IntervalMap m1, IntervalMap m2, IntervalMap m3) ->
      IntervalMap $ Map.unions [m1, Map.mapMaybe (\(j,a) -> (\b -> seq b (j,b)) <$> f a) m2, m3]

-- | The expression (@'alter' f i map@) alters the value @x@ at @i@, or absence thereof.
-- 'alter' can be used to insert, delete, or update a value in a 'IntervalMap'.
alter :: Ord k => (Maybe a -> Maybe a) -> Interval k -> IntervalMap k a -> IntervalMap k a
alter _ i m | Interval.null i = m
alter f i m =
  case split i m of
    (IntervalMap m1, IntervalMap m2, IntervalMap m3) ->
      let m2' = Map.mapMaybe (\(j,a) -> (\b -> seq b (j,b)) <$> f (Just a)) m2
          js = IntervalSet.singleton i `IntervalSet.difference` keysSet (IntervalMap m2)
          IntervalMap m2'' =
            case f Nothing of
              Nothing -> empty
              Just !a -> B.fromList [(j,a) | j <- IntervalSet.toList js]
      in seq m2' $ IntervalMap $ Map.unions [m1, m2', m2'', m3]

-- ------------------------------------------------------------------------
-- Combine

-- | Union with a combining function.
unionWith :: Ord k => (a -> a -> a) -> IntervalMap k a -> IntervalMap k a -> IntervalMap k a
unionWith f m1 m2 =
  foldl' (\m (i,a) -> insertWith f i a m) m2 (toList m1)

-- | The union of a list of maps, with a combining operation:
--   (@'unionsWith' f == 'Prelude.foldl' ('unionWith' f) 'empty'@).
unionsWith :: Ord k => (a -> a -> a) -> [IntervalMap k a] -> IntervalMap k a
unionsWith f = foldl' (unionWith f) empty

-- | Intersection with a combining function.
intersectionWith :: Ord k => (a -> b -> c) -> IntervalMap k a -> IntervalMap k b -> IntervalMap k c
intersectionWith f im1@(IntervalMap m1) im2@(IntervalMap m2)
  | Map.size m1 >= Map.size m2 = g f im1 im2
  | otherwise = g (flip f) im2 im1
  where
    g :: Ord k => (a -> b -> c) -> IntervalMap k a -> IntervalMap k b -> IntervalMap k c
    g h jm1 (IntervalMap m3) = IntervalMap $ Map.unions $ go jm1 (Map.elems m3)
      where
        go _ [] = []
        go im ((i,b) : xs) =
          case split i im of
            (_, IntervalMap m, jm2) ->
              Map.map (\(j, a) -> (j,) $! h a b) m : go jm2 xs

-- ------------------------------------------------------------------------
-- Traversal

-- | Map a function over all values in the map.
map :: (a -> b) -> IntervalMap k a -> IntervalMap k b
map f (IntervalMap m) = IntervalMap $ Map.map (\(i, a) -> (i,) $! f a) m

-- ------------------------------------------------------------------------
-- Conversion

-- | Build a map from a list of key\/value pairs.
-- If the list contains more than one value for the same key, the last value
-- for the key is retained.
fromList :: Ord k => [(Interval k, a)] -> IntervalMap k a
fromList = foldl' (\m (i,a) -> insert i a m) empty

-- | Build a map from a list of key\/value pairs with a combining function.
fromListWith :: Ord k => (a -> a -> a) -> [(Interval k, a)] -> IntervalMap k a
fromListWith f = foldl' (\m (i,a) -> insertWith f i a m) empty
