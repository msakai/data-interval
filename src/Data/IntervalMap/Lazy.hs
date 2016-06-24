{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable, MultiWayIf, GeneralizedNewtypeDeriving #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.IntervalMap.Base
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (CPP, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable, MultiWayIf, GeneralizedNewtypeDeriving)
--
-- Interval datatype and interval arithmetic.
--
-----------------------------------------------------------------------------
module Data.IntervalMap.Lazy
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
import Data.IntervalMap.Base
import Data.ExtendedReal
