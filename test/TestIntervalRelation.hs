{-# LANGUAGE ScopedTypeVariables, TemplateHaskell #-}
module TestIntervalRelation (intervalRelationTestGroup) where

import Prelude hiding (null)
import Control.Monad

import Test.Tasty.QuickCheck
import Test.Tasty.TH

import Data.Interval
import Data.IntervalRelation

{--------------------------------------------------------------------
  relate
--------------------------------------------------------------------}

prop_relate_equals =
  forAll intervals $ \a ->
    relate a a == Equal

prop_relate_empty_contained_in_non_empty =
  forAll (intervals `suchThat` (not . null)) $ \a ->
    relate a empty == Contains

prop_relate_detects_before =
  forAll (nonEmptyIntervalPairs (\_ (ub1, _) (lb2, _) _ -> ub1 < lb2)) $ \(a, b) ->
    relate a b == Before

prop_relate_open_intervals_with_common_boundary_are_before =
  forAll (arbitrary `suchThat` \(b1, b2, i) -> fst b1 < i && i < fst b2) $
      \(b1 :: (Extended Rational, Boundary), b2, i :: Extended Rational) ->
        relate (interval b1 (i, Open)) (interval (i, Open) b2) == Before

prop_relate_right_closed_interval_just_before =
  forAll (arbitrary `suchThat` \(b1, b2, i) -> fst b1 < i && i < fst b2) $
      \(b1 :: (Extended Rational, Boundary), b2, i :: Extended Rational) ->
        relate (interval b1 (i, Closed)) (interval (i, Open) b2) == JustBefore

prop_relate_right_open_interval_just_before =
  forAll (arbitrary `suchThat` \(b1, b2, i) -> fst b1 < i && i < fst b2) $
      \(b1 :: (Extended Rational, Boundary), b2, i :: Extended Rational) ->
        relate (interval b1 (i, Open)) (interval (i, Closed) b2) == JustBefore

prop_relate_two_intervals_overlap =
  forAll (nonEmptyIntervalPairs (\(lb1, _) (ub1, _) (lb2, _) (ub2, _) -> lb1 < lb2 && lb2 < ub1 && ub1 < ub2)) $ \(a, b) ->
    relate a b == Overlaps

prop_relate_interval_starts_another =
  forAll (nonEmptyIntervalPairs (\(lb1, _) (ub1, _) (lb2, _) (ub2, _) -> lb1 == lb2 && ub1 < ub2)) $ \(a, b) ->
    relate a b == Starts

prop_relate_interval_finishes_another =
  forAll (nonEmptyIntervalPairs (\(lb1, _) (ub1, _) (lb2, _) (ub2, _) -> lb1 > lb2 && ub1 == ub2)) $ \(a, b) ->
    relate a b == Finishes

prop_relate_interval_contains_another =
  forAll (nonEmptyIntervalPairs (\(lb1, _) (ub1, _) (lb2, _) (ub2, _) -> lb1 < lb2 && ub1 > ub2)) $ \(a, b) ->
    relate a b == Contains

prop_relate_one_singleton_before_another =
  forAll (arbitrary `suchThat` uncurry (<)) $ \(r1 :: Rational, r2) ->
    relate (singleton r1) (singleton r2) == Before

prop_relate_singleton_starts_interval =
  forAll (arbitrary `suchThat` uncurry (<)) $ \(r1 :: Rational, r2) b ->
    relate (singleton r1) (interval (Finite r1, Closed) (Finite r2, b)) == Starts

prop_relate_singleton_just_before_interval =
  forAll (arbitrary `suchThat` uncurry (<)) $ \(r1 :: Rational, r2) b ->
    relate (singleton r1) (interval (Finite r1, Open) (Finite r2, b)) == JustBefore

prop_relate_singleton_finishes_interval =
  forAll (arbitrary `suchThat` uncurry (<)) $ \(r1 :: Rational, r2) b ->
    relate (singleton r2) (interval (Finite r1, b) (Finite r2, Closed)) == Finishes

prop_relate_singleton_just_after_interval =
  forAll (arbitrary `suchThat` uncurry (<)) $ \(r1 :: Rational, r2) b ->
    relate (singleton r2) (interval (Finite r1, b) (Finite r2, Open)) == JustAfter

{--------------------------------------------------------------------
  invert
--------------------------------------------------------------------}

prop_invert_is_involution a =
  invert (invert a) == a

prop_invert_inverts_relation =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    relate a b == invert (relate b a)

{--------------------------------------------------------------------
  Generators
--------------------------------------------------------------------}

instance Arbitrary Boundary where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary r => Arbitrary (Extended r) where
  arbitrary =
    oneof
    [ return NegInf
    , return PosInf
    , liftM Finite arbitrary
    ]

instance (Arbitrary r, Ord r) => Arbitrary (Interval r) where
  arbitrary = do
    lb <- arbitrary
    ub <- arbitrary
    return $ interval lb ub

intervals :: Gen (Interval Rational)
intervals = arbitrary

nonEmptyIntervalPairs
  :: ((Extended Rational, Boundary) -> (Extended Rational, Boundary) -> (Extended Rational, Boundary) -> (Extended Rational, Boundary) -> Bool)
  -> Gen (Interval Rational, Interval Rational)
nonEmptyIntervalPairs boundariesComparer = ((,) <$> intervals <*> intervals) `suchThat`
  (\(i1, i2) ->
    (not . null $ i1) &&
    (not . null $ i2) &&
    boundariesComparer
      (lowerBound' i1)
      (upperBound' i1)
      (lowerBound' i2)
      (upperBound' i2)
  )

instance Arbitrary Relation where
  arbitrary =
    oneof
    [ return Equal
    , return Starts
    , return Finishes
    , return During
    , return StartedBy
    , return FinishedBy
    , return Contains
    , return Before
    , return After
    , return JustBefore
    , return JustAfter
    , return Overlaps
    , return OverlappedBy
    ]

------------------------------------------------------------------------
-- Test harness

intervalRelationTestGroup = $(testGroupGenerator)
