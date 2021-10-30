{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, DeriveDataTypeable, DeriveGeneric #-}
{-# LANGUAGE Safe #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.IntervalRelation
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (CPP, DeriveDataTypeable, DeriveGeneric)
--
-- Interval relations and their algebra.
--
-----------------------------------------------------------------------------
module Data.IntervalRelation
  ( Relation(..)
  , invert
  )
  where

import Data.Data
import GHC.Generics (Generic)

-- | Describes how two intervals @x@ and @y@ can be related.
-- See [Allen's interval algebra](https://en.wikipedia.org/wiki/Allen%27s_interval_algebra)
-- and [Intervals and their relations](http://marcosh.github.io/post/2020/05/04/intervals-and-their-relations.html).
data Relation
  = Before
  -- ^ Any element of @x@ is smaller than any element of @y@,
  -- and intervals are not connected. In other words, there exists an element
  -- that is bigger than any element of @x@ and smaller than any element of @y@.
  | JustBefore
  -- ^ Any element of @x@ is smaller than any element of @y@,
  -- but intervals are connected and non-empty. This implies that intersection
  -- of intervals is empty, and union is a single interval.
  | Overlaps
  -- ^ Intersection of @x@ and @y@ is non-empty,
  -- @x@ start and finishes earlier than @y@. This implies that union
  -- is a single interval, and @x@ finishes no earlier than @y@ starts.
  | Starts
  -- ^ @x@ is a proper subset of @y@,
  -- and they share lower bounds.
  | During
  -- ^ @x@ is a proper subset of @y@,
  -- but they share neither lower nor upper bounds.
  | Finishes
  -- ^ @x@ is a proper subset of @y@,
  -- and they share upper bounds.
  | Equal
  -- ^ Intervals are equal.
  | FinishedBy
  -- ^ Inverse of 'Finishes'.
  | Contains
  -- ^ Inverse of 'During'.
  | StartedBy
  -- ^ Inverse of 'Starts'.
  | OverlappedBy
  -- ^ Inverse of 'Overlaps'.
  | JustAfter
  -- ^ Inverse of 'JustBefore'.
  | After
  -- ^ Inverse of 'Before'.
  deriving (Eq, Ord, Enum, Bounded, Show, Read, Generic, Data, Typeable)

-- | Inverts a relation, such that @'invert' ('Data.Interval.relate' x y) = 'Data.Interval.relate' y x@
invert :: Relation -> Relation
invert relation = case relation of
  Before       -> After
  JustBefore   -> JustAfter
  Overlaps     -> OverlappedBy
  Starts       -> StartedBy
  During       -> Contains
  Finishes     -> FinishedBy
  Equal        -> Equal
  FinishedBy   -> Finishes
  Contains     -> During
  StartedBy    -> Starts
  OverlappedBy -> Overlaps
  JustAfter    -> JustBefore
  After        -> Before
