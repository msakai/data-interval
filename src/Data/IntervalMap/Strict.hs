{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, BangPatterns, TupleSections #-}
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
-- Interval datatype and interval arithmetic.
--
-----------------------------------------------------------------------------
module Data.IntervalMap.Strict
  (
  -- * IntervalMap type
    IntervalMap
  , module Data.ExtendedReal
  , EndPoint

  -- * Operators
  , (!)
  , (\\)

  -- * Query
  , null
  , member
  , notMember
  , lookup
  , findWithDefault

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
  , split

  -- * Submap
  , isSubmapOf
  , isSubmapOfBy
  , isProperSubmapOf
  , isProperSubmapOfBy
  )
  where


import Prelude hiding (null, lookup, map)
import Control.Applicative hiding (empty)
import Data.ExtendedReal
import Data.Interval (Interval, EndPoint)
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
      IntervalMap $ Map.unions [m1, Map.mapMaybe (\(i,a) -> (\b -> seq b (i,b)) <$> f a) m2, m3]

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
    g f im1 (IntervalMap m2) = IntervalMap $ Map.unions $ go im1 (Map.elems m2)
      where
        go _ [] = []
        go im ((i,b) : xs) =
          case split i im of
            (_, IntervalMap m, im2) ->
              Map.map (\(j, a) -> (j,) $! f a b) m : go im2 xs

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
