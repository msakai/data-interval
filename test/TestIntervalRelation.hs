{-# LANGUAGE TemplateHaskell #-}
module TestIntervalRelation (intervalRelationTestGroup) where

import Control.Monad

import Test.Tasty.QuickCheck
import Test.Tasty.TH

import Data.Interval (Interval, Extended(..))
import qualified Data.Interval as Interval
import Data.IntervalRelation

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

instance Arbitrary Interval.Boundary where
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
    return $ Interval.interval lb ub

intervals :: Gen (Interval Rational)
intervals = arbitrary

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
