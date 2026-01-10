module BenchInterval where

import Test.Tasty.Bench

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Interval
  ((<=..<=), (<..<), (<=..<), (<..<=), Interval, Extended(..))
import qualified Data.Interval as Interval
import qualified Data.IntervalSet as IntervalSet
import Data.IntervalSet (IntervalSet)

------------------------- Alternative implementations --------------------------

-- The following implementations are alternatives that were tried but are slower
-- than the implementations exported by the library.

-- same semantics as Interval.withoutMapKeysFromInterval
withoutMapKeysFromIntervalComplement ::  Ord k => Interval k -> Map k a -> Map k a
withoutMapKeysFromIntervalComplement is m =
  IntervalSet.restrictMapKeysToIntervalSet m $
            IntervalSet.complement (IntervalSet.singleton is)


------------------------- Example data for benchmarks --------------------------

minMap, maxMap :: Rational
minMap = 0
maxMap = 1000000

largeMap :: Map.Map Rational Rational
largeMap = Map.fromList [(i, i) | i <- [minMap .. maxMap]]

smallClosedInterval :: Interval Rational
smallClosedInterval = 40000 <=..<= 60000

smallOpenInterval :: Interval Rational
smallOpenInterval = 40000 <..< 60000

largeClosedInterval :: Interval Rational
largeClosedInterval = 250000 <=..<= 750000

largeOpenInterval :: Interval Rational
largeOpenInterval = 250000 <..< 750000

pointInterval :: Interval Rational
pointInterval = 500000 <=..<= 500000

---------------------------------- Benchmarks ----------------------------------

benchRestrictMapKeysToInterval :: Ord k => Map k a -> Interval k -> [Benchmark]
benchRestrictMapKeysToInterval m i =
    [ bench "Interval.restrictMapKeysToInterval" $
      whnf (Interval.restrictMapKeysToInterval m) i
    , bench "Map.filterKeys" $
      whnf (Map.filterWithKey (\k _ -> Interval.member k i)) m
    ]

benchWithoutKeysFromInterval :: Ord k => Interval k -> Map k a -> [Benchmark]
benchWithoutKeysFromInterval i m =
  [ bench "Interval.withoutMapKeysFromInterval" $
      whnf (Interval.withoutMapKeysFromInterval i) m
  , bench "withoutMapKeysFromInterval (complement)" $
      whnf (withoutMapKeysFromIntervalComplement i) m
  , bench "Map.filterKeys" $
      whnf (Map.filterWithKey
          (\k _ -> not (Interval.member k i)))
        m
  ]

bgroupInterval :: Benchmark
bgroupInterval =
  bgroup "Interval"
    [
      bgroup "restrictMapKeysToInterval"
        [
          bgroup "large closed interval" $
            benchRestrictMapKeysToInterval largeMap largeClosedInterval,
          bgroup "large open interval" $
            benchRestrictMapKeysToInterval largeMap largeOpenInterval
        ],
      bgroup "withoutMapKeysFromInterval"
      [ bgroup "small closed interval" $
          benchWithoutKeysFromInterval smallClosedInterval largeMap
      , bgroup "small open interval" $
          benchWithoutKeysFromInterval smallOpenInterval largeMap
      , bgroup "large closed interval" $
          benchWithoutKeysFromInterval largeClosedInterval largeMap
      , bgroup "large open interval" $
          benchWithoutKeysFromInterval largeOpenInterval largeMap
      , bgroup "point interval" $
          benchWithoutKeysFromInterval pointInterval largeMap
      ]
    ]
