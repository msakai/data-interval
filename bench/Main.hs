
import Test.Tasty.Bench

import BenchInterval
import BenchIntervalSet

main :: IO ()
main = defaultMain
  [
    bgroupInterval,
    bgroupIntervalSet
  ]
