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
  , relate
  , invert
  )
  where

import Prelude hiding (null)
import Data.Data
import Data.Interval
import GHC.Generics (Generic)

-- | describes how two intervals @x@ and @y@ can be related.
-- See [Allen's interval algebra](https://en.wikipedia.org/wiki/Allen%27s_interval_algebra)
data Relation
  = Before
  | JustBefore
  | Overlaps
  | Starts
  | During
  | Finishes
  | Equal
  | FinishedBy
  | Contains
  | StartedBy
  | OverlappedBy
  | JustAfter
  | After
  deriving (Eq, Ord, Enum, Bounded, Show, Read, Generic, Data, Typeable)

-- | Computes how two intervals are related according to the @`Relation`@ classification
relate :: Ord r => Interval r -> Interval r -> Relation
relate i1 i2 =
  case (i1 `isSubsetOf` i2, i2 `isSubsetOf` i1) of
    -- 'i1' ad 'i2' are equal
    (True , True ) -> Equal
    -- 'i1' is strictly contained in `i2`
    (True , False) | lowerBound i1 == lowerBound i2 -> Starts
                   | upperBound i1 == upperBound i2 -> Finishes
                   | otherwise                                    -> During
    -- 'i2' is strictly contained in `i1`
    (False, True ) | lowerBound i1 == lowerBound i2 -> StartedBy
                   | upperBound i1 == upperBound i2 -> FinishedBy
                   | otherwise                                    -> Contains
    -- neither `i1` nor `i2` is contained in the other
    (False, False) -> case ( null (i1 `intersection` i2)
                           , lowerBound i1 <= lowerBound i2
                           , i1 `isConnected` i2
                           ) of
      (True , True , True ) -> JustBefore
      (True , True , False) -> Before
      (True , False, True ) -> JustAfter
      (True , False, False) -> After
      (False, True , _    ) -> Overlaps
      (False, False, _    ) -> OverlappedBy

-- | inverts a relation, such that @'invert' ('relate' x y) = 'relate' y x@
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
