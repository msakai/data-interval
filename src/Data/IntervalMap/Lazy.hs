{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE Safe #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.IntervalMap.Base
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Mapping from intervals to values.
--
-- API of this module is strict in the keys, but lazy in the values.
-- If you need value-strict maps, use "Data.IntervalMap.Strict" instead.
-- The 'IntervalMap' type itself is shared between the lazy and strict modules,
-- meaning that the same 'IntervalMap' value can be passed to functions in
-- both modules (although that is rarely needed).
--
-- These modules are intended to be imported qualified, to avoid name
-- clashes with Prelude functions, e.g.
--
-- >  import Data.IntervalMap.Lazy (IntervalMap)
-- >  import qualified Data.IntervalMap.Lazy as IntervalMap
--
-----------------------------------------------------------------------------
module Data.IntervalMap.Lazy
  (
  -- * Strictness properties
  -- $strictness

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
  , filter
  , split

  -- * Submap
  , isSubmapOf
  , isSubmapOfBy
  , isProperSubmapOf
  , isProperSubmapOfBy
  )
  where


import Prelude hiding (null, lookup, map, filter)
import Data.IntervalMap.Base
import Data.ExtendedReal

-- $strictness
--
-- This module satisfies the following strictness property:
--
-- * Key arguments are evaluated to WHNF
--
-- Here are some examples that illustrate the property:
--
-- > insert undefined v m  ==  undefined
-- > insert k undefined m  ==  OK
-- > delete undefined m  ==  undefined
