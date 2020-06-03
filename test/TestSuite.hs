module Main where

import TestInterval
import TestIntervalMap
import TestIntervalRelation
import TestIntervalSet
import TestIntegerInterval
import Test.Tasty

main :: IO ()
main = defaultMain $ testGroup "data-interval test suite"
  [ intervalTestGroup
  , intervalMapTestGroup
  , intervalRelationTestGroup
  , intervalSetTestGroup
  , integerIntervalTestGroup
  ]
