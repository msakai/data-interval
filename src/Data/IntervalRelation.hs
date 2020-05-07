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
