module Main where

import TestInterval
import TestIntervalSet
import TestIntegerInterval
import Test.Tasty

main :: IO ()
main = defaultMain $ testGroup "data-interval test suite"
  [ intervalTestGroup
  , intervalSetTestGroup
  , integerIntervalTestGroup
  ]
