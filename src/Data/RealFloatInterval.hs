{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE CPP, LambdaCase, ScopedTypeVariables #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE RoleAnnotations #-}
-- |
-- Module      :  Data.RealFloatInterval
-- Copyright   :  (c) Masahiro Sakai 2011-2013, Andrew Lelechenko 2020
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (CPP, ScopedTypeVariables, DeriveDataTypeable)
--
module Data.RealFloatInterval
  (
  -- * Interval type
    Interval
  , Boundary(..)

  -- * Construction
  , interval
  , (<=..<=)
  , (<..<=)
  , (<=..<)
  , (<..<)
  , whole
  , empty
  , singleton

  -- * Query
  , null
  , isSingleton
  , extractSingleton
  , member
  , notMember
  , isSubsetOf
  , isProperSubsetOf
  , isConnected
  , lowerBound
  , upperBound
  , lowerBound'
  , upperBound'
  , width

  -- * Universal comparison operators
  , (<!), (<=!), (==!), (>=!), (>!), (/=!)

  -- * Existential comparison operators
  , (<?), (<=?), (==?), (>=?), (>?), (/=?)

  -- * Existential comparison operators that produce witnesses (experimental)
  , (<??), (<=??), (==??), (>=??), (>??), (/=??)

  -- * Combine
  , intersection
  , intersections
  , hull
  , hulls

  -- * Map
  , mapMonotonic

  -- * Operations
  , pickup
  , simplestRationalWithin

  -- * Intervals relation
  , relate
  ) where

import Data.ExtendedReal
import Data.Interval (null, isSingleton, extractSingleton, isSubsetOf, isProperSubsetOf, isConnected, (<!), (<=!), (==!), (>=!), (>!), (/=!), (<?), (<=?), (==?), (>=?), (>?), (/=?), (<??), (<=??), (==??), (>=??), (>??), (/=??), intersection, intersections, hull, hulls, pickup, simplestRationalWithin, relate)
import Data.Interval.Internal (Boundary(..), Interval, empty)
import qualified Data.Interval.Internal as Internal
import Prelude hiding (null)
import Control.Arrow (first)

infix 5 <=..<=
infix 5 <..<=
infix 5 <=..<
infix 5 <..<

lowerBound' :: RealFloat r => Interval r -> (r, Boundary)
lowerBound' = first toRealFloat . Internal.lowerBound'

upperBound' :: RealFloat r => Interval r -> (r, Boundary)
upperBound' = first toRealFloat . Internal.upperBound'

-- | Lower endpoint (/i.e./ greatest lower bound)  of the interval.
lowerBound :: RealFloat r => Interval r -> r
lowerBound = fst . lowerBound'

-- | Upper endpoint (/i.e./ least upper bound) of the interval.
upperBound :: RealFloat r => Interval r -> r
upperBound = fst . upperBound'

interval :: RealFloat r => (r, Boundary) -> (r, Boundary) -> Interval r
interval lb ub = Internal.interval (first fromRealFloat lb) (first fromRealFloat ub)

-- | closed interval [@l@,@u@]
(<=..<=)
  :: (Ord r, RealFloat r)
  => r -- ^ lower bound @l@
  -> r -- ^ upper bound @u@
  -> Interval r
(<=..<=) lb ub = interval (lb, Closed) (ub, Closed)

-- | left-open right-closed interval (@l@,@u@]
(<..<=)
  :: (Ord r, RealFloat r)
  => r -- ^ lower bound @l@
  -> r -- ^ upper bound @u@
  -> Interval r
(<..<=) lb ub = interval (lb, Open) (ub, Closed)

-- | left-closed right-open interval [@l@, @u@)
(<=..<)
  :: (Ord r, RealFloat r)
  => r -- ^ lower bound @l@
  -> r -- ^ upper bound @u@
  -> Interval r
(<=..<) lb ub = interval (lb, Closed) (ub, Open)

-- | open interval (@l@, @u@)
(<..<)
  :: (Ord r, RealFloat r)
  => r -- ^ lower bound @l@
  -> r -- ^ upper bound @u@
  -> Interval r
(<..<) lb ub = interval (lb, Open) (ub, Open)

-- | whole real number line (-∞, ∞)
whole :: Ord r => Interval r
whole = Internal.interval (NegInf, Open) (PosInf, Open)

-- | singleton set [x,x]
singleton :: (Ord r, RealFloat r) => r -> Interval r
singleton x = interval (x, Closed) (x, Closed)

-- | Is the element finite and in the interval?
member :: (Ord r, RealFloat r) => r -> Interval r -> Bool
member x i = condLB && condUB
  where
    (x1, in1) = lowerBound' i
    (x2, in2) = upperBound' i
    condLB = case in1 of
      Open   -> x1 <  x
      Closed -> x1 <= x
    condUB = case in2 of
      Open   -> x <  x2
      Closed -> x <= x2

-- | Is the element infinite or not in the interval?
notMember :: (Ord r, RealFloat r) => r -> Interval r -> Bool
notMember a i = not $ member a i

-- | Width of a interval. Width of an unbounded interval is infinite.
width :: (Num r, Ord r, RealFloat r) => Interval r -> r
width x
  | null x = 0
  | otherwise = fst (upperBound' x) - fst (lowerBound' x)

-- | @mapMonotonic f i@ is the image of @i@ under @f@, where @f@ must be a strict monotone function,
-- preserving negative and positive infinities.
mapMonotonic :: (Ord a, Ord b, RealFloat a, RealFloat b) => (a -> b) -> Interval a -> Interval b
mapMonotonic f i = Internal.interval (applyF lb, in1) (applyF ub, in2)
  where
    (lb, in1) = Internal.lowerBound' i
    (ub, in2) = Internal.upperBound' i
    applyF = \case
      PosInf -> PosInf
      NegInf -> NegInf
      Finite r -> fromRealFloat $ f r
