module TestInstances where

import Control.Monad

import Test.Tasty.QuickCheck

import Data.Interval
import Data.IntervalRelation

instance Arbitrary Boundary where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary r => Arbitrary (Extended r) where
  arbitrary = frequency
    [ (1, return NegInf)
    , (1, return PosInf)
    , (3, liftM Finite arbitrary)
    ]
  shrink NegInf = []
  shrink (Finite x) = NegInf : PosInf : map Finite (shrink x)
  shrink PosInf = []

instance (Arbitrary r, Ord r) => Arbitrary (Interval r) where
  arbitrary = do
    x <- arbitrary
    y <- arbitrary
    frequency
      [ (1, return $ interval x y)
      , (3, return $ interval (min x y) (max x y))
      ]
  shrink a
    | isSingleton a = case lowerBound a of
      Finite x -> map singleton $ shrink x
      _ -> []
    | otherwise = mkPoint lb ++ mkPoint ub ++ map (lb `interval`) (shrink ub) ++ map (`interval` ub) (shrink lb)
    where
      lb = lowerBound' a
      ub = upperBound' a

      mkPoint (Finite x, _) = [singleton x]
      mkPoint _ = []

intervals :: Gen (Interval Rational)
intervals = arbitrary

instance Arbitrary Relation where
  arbitrary = arbitraryBoundedEnum
