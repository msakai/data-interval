module Main where

import Test.Framework (defaultMain)
import TestInterval
import TestIntegerInterval

main :: IO ()
main = defaultMain
  [ intervalTestGroup
  , integerIntervalTestGroup
  ]
