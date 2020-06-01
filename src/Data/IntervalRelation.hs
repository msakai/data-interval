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
