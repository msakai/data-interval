module TestInstances where

import Control.Monad

import Test.Tasty.QuickCheck

import Data.Interval
import Data.IntervalRelation

instance Arbitrary Boundary where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary r => Arbitrary (Extended r) where
  arbitrary =
    oneof
    [ return NegInf
    , return PosInf
    , liftM Finite arbitrary
    ]
  shrink NegInf = []
  shrink (Finite x) = map Finite (shrink x)
  shrink PosInf = []

instance (Arbitrary r, Ord r) => Arbitrary (Interval r) where
  arbitrary = do
    lb <- arbitrary
    ub <- arbitrary
    return $ interval lb ub
  shrink a = map (lb `interval`) (shrink ub) ++ map (`interval` ub) (shrink lb)
    where
      lb = lowerBound' a
      ub = upperBound' a

intervals :: Gen (Interval Rational)
intervals = arbitrary

instance Arbitrary Relation where
  arbitrary = arbitraryBoundedEnum
