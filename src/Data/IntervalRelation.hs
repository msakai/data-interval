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
  ( Relation
  )
  where

import Data.Data
import Data.Interval
import GHC.Generics (Generic)

-- | describes how two intervals @x@ and @y@ can be related.
-- See [Allen's interval algebra](https://en.wikipedia.org/wiki/Allen%27s_interval_algebra)
data Relation
  = Equal
  | Starts
  | Finishes
  | During
  | StartedBy
  | FinishedBy
  | Contains
  | Before
  | After
  | JustBefore
  | JustAfter
  | Overlaps
  | OverlappedBy
  deriving (Eq, Ord, Enum, Bounded, Show, Read, Generic, Data, Typeable)

relate :: Ord r => Interval r -> Interval r -> Relation
relate interval1 interval2 =
  case (interval1 `intersection` interval2 == interval1, interval1 `intersection` interval2 == interval2) of
    -- both intervals are equal to their intersection, hence they are equal
    (True , True ) -> Equal
    -- 'interval1' is equal to the intersection, hence it must be strictly contained in `interval2`
    (True , False) | lowerBound interval1 == lowerBound interval2 -> Starts
                   | upperBound interval1 == upperBound interval2 -> Finishes
                   | otherwise                                    -> During
    -- 'interval2' is equal to the intersection, hence it must be strictly contained in `interval1`
    (False, True ) | lowerBound interval1 == lowerBound interval2 -> StartedBy
                   | upperBound interval1 == upperBound interval2 -> FinishedBy
                   | otherwise                                    -> Contains
    -- neither `interval1` nor `interval2` is equal to the intersection, so neither is contained in the other
    (False, False) -> _poiu
