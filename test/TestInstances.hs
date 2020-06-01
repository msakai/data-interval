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

instance (Arbitrary r, Ord r) => Arbitrary (Interval r) where
  arbitrary = do
    lb <- arbitrary
    ub <- arbitrary
    return $ interval lb ub

intervals :: Gen (Interval Rational)
intervals = arbitrary

instance Arbitrary Relation where
  arbitrary = arbitraryBoundedEnum
