module BenchIntervalSet where

import Test.Tasty.Bench

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Interval
  ((<=..<=), (<..<), (<=..<), (<..<=), Interval, Extended(..))
import qualified Data.Interval as Interval
import qualified Data.IntervalSet as IntervalSet
import Data.IntervalSet (IntervalSet)

------------------------- Alternative implementations --------------------------

-- The following implementations are alternatives that were tried but are slower
-- than the implementations exported by the library.


-- same semantics as IntervalSet.restrictMapKeysToIntervalSet
restrictMapKeysToIntervalSetFoldr :: Ord k => Map k a -> IntervalSet k -> Map k a
restrictMapKeysToIntervalSetFoldr m is =
    let f i acc = Map.union acc (Interval.restrictMapKeysToInterval m i) in
    IntervalSet.foldr f Map.empty is


-- same semantics as IntervalSet.withoutMapKeysFromIntervalSet
withoutMapKeysFromIntervalSetComplement :: Ord k
  => IntervalSet k -> Map k a -> Map k a
withoutMapKeysFromIntervalSetComplement is m =
  IntervalSet.foldr Interval.withoutMapKeysFromInterval m is

-- same semantics as IntervalSet.intersectionSetAndIntervalSet
intersectionSetAndIntervalSetFoldr :: Ord k
  => Set k -> IntervalSet k -> Set k
intersectionSetAndIntervalSetFoldr s is =
    let f i acc = Set.union acc (Interval.intersectionSetAndInterval s i) in
    IntervalSet.foldr f Set.empty is


------------------------- Example data for benchmarks --------------------------

minMap, maxMap :: Rational
minMap = 0
maxMap = 1000000

largeMap :: Map Rational Rational
largeMap = Map.fromList [(i, i) | i <- [minMap .. maxMap]]

largeSet :: Set Rational
largeSet = Set.fromList [minMap .. maxMap]


alternate ::
  Rational -> -- min
  Rational -> -- max
  Int ->      -- number of parts
  IntervalSet Rational
alternate minV maxV n =
  let step = (maxV - minV) / fromIntegral n in
  IntervalSet.fromList
  [ Finite (minV + step * fromIntegral i)
    Interval.<..<=
    Finite (minV + step * (fromIntegral i + 1 / 2))
  | i <- [0..n-1]]

---------------------------------- Benchmarks ----------------------------------

benchRestrictMapKeysToInterval :: Ord k => Map k a -> Interval k -> [Benchmark]
benchRestrictMapKeysToInterval m i =
    [ bench "Interval.restrictMapKeysToInterval" $
      whnf (Interval.restrictMapKeysToInterval m) i
    , bench "Map.filterKeys" $
      whnf (Map.filterWithKey (\k _ -> Interval.member k i)) m
    ]

benchRestrictMapKeysToIntervals ::
  Ord k =>  Map k a -> IntervalSet k -> [Benchmark]
benchRestrictMapKeysToIntervals m i =
  [ bench "IntervalSet.restrictMapKeysToIntervalSet" $
      whnf (IntervalSet.restrictMapKeysToIntervalSet m) i
  , bench "Map.filterKeys" $ whnf (Map.filterWithKey
              (\k _ -> IntervalSet.member k i)) m
  , bench "restrictMapKeysToIntervalSet (foldr)" $ whnf (restrictMapKeysToIntervalSetFoldr m) i
  ]

foldFilterThreshold :: Float
foldFilterThreshold = 0.25

benchRestrictMapKeysToIntervalsPercentage ::
     Float
  -> Benchmark
benchRestrictMapKeysToIntervalsPercentage a =
  bgroup ("num of intervals / map size = " ++ show a) $
    benchRestrictMapKeysToIntervals largeMap
      (alternate minMap maxMap (round numberOfIntervals))
  where
    numberOfIntervals = (maxMap - minMap) * toRational a

benchWithoutMapKeysFromIntervals :: Ord k => IntervalSet k -> Map k a -> [Benchmark]
benchWithoutMapKeysFromIntervals is m =
  [ bench "IntervalSet.withoutMapKeysFromIntervalSet" $
      whnf (IntervalSet.withoutMapKeysFromIntervalSet is) m
  , bench "withoutMapKeysFromIntervalSet (complement)" $
      whnf (withoutMapKeysFromIntervalSetComplement is) m
  , bench "Map.filterKeys" $
      whnf (Map.filterWithKey
          (\k _ -> not (IntervalSet.member k is)))
        m
  ]

benchWithoutMapKeysFromIntervalsPercentage ::
     Float -- ^  number of intervals / map size
  -> Benchmark
benchWithoutMapKeysFromIntervalsPercentage n =
  bgroup ("num of intervals / map size = " ++ show n ) $
    benchWithoutMapKeysFromIntervals
      (alternate minMap maxMap (round numberOfIntervals)) largeMap
  where
    numberOfIntervals = (maxMap - minMap) * toRational n


benchIntersectIntervals :: Ord k => Set k -> IntervalSet k ->  [Benchmark]
benchIntersectIntervals s is =
  [ bench "IntervalSet.intersectionSetAndIntervalSet" $
      whnf (IntervalSet.intersectionSetAndIntervalSet s) is
  , bench "intersectionSetAndIntervalSet (foldr)" $
      whnf (intersectionSetAndIntervalSetFoldr s) is
  ]

benchIntersectIntervalsPercentage ::
     Float -- ^  number of intervals / set size
  -> Benchmark
benchIntersectIntervalsPercentage a =
  bgroup ("num of intervals / set size = " ++ show a ) $
    benchIntersectIntervals largeSet
      (alternate minMap maxMap (round numberOfIntervals))
  where
    numberOfIntervals = (maxMap - minMap) * toRational a

-- these percentages aims to determine the fold/filter threshold when filtering
-- starts to be more efficient than folding
intervalPercentages :: [Float]
intervalPercentages =
     [10 ^^ n | n <- [-6 .. -2]]
  ++ [n/10 | n <- [1 .. 10]]
  ++ [2,4]

bgroupIntervalSet :: Benchmark
bgroupIntervalSet =
  bgroup "IntervalSet"
    [
      bgroup "withoutMapKeysFromIntervalSet"
        [ benchWithoutMapKeysFromIntervalsPercentage (10 ^^ n) | n <- [-6 .. 0]],
      bgroup "restrictMapKeysToIntervalSet" $
        benchRestrictMapKeysToIntervalsPercentage <$> intervalPercentages,
      bgroup "intersectionSetAndIntervalSet" $
        benchIntersectIntervalsPercentage <$> intervalPercentages
    ]
