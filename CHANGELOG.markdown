1.3.0
-----
* add `Data.IntervalSet` module
* add `Data.IntervalMap` module
* add new function `mapMonotonic` to `Data.Interval` and `Data.IntegerInterval`
* add new function `isConnected` to `Data.Interval`.

1.2.0
-----
* add `Data.IntegerInterval`
* use extended-reals >=0.2
* `EndPoint` is deprecated. Use `Extended` instead.

1.1.1
-----
* remove unnecessary `Real` constraint from comparison operators.

1.1.0
-----
* remove unnecessary Num constraint from bunch of constructors and operations:
  `interval`, `(<=..<=)`, `(<..<=)`, `(<=..<)`, `(<..<)`, `whole`, `empty`,
  `singleton`, `intersection`, `intersections`, `hull`, `hulls`.
  Thanks to Tad Doxsee for pointing out that.

1.0.0
-----
* use extended-reals package for representing endpoints
* add (experimental) comparison operators that produce witnesses:
  `(<??)`, `(<=??)`, `(==??)`, `(>=??)`, `(>??)`

0.6.0
-----
* add `hulls, intersections :: (Num r, Ord r) => [Interval r] -> Interval r`
* fix a bug of `(<=?)` operator

0.5.0
-----
* fix dependency issue with QuickCheck and test-framework-quickcheck2

0.4.0
-----
* add `simplestRationalWithin :: RealFrac r => Interval r -> Maybe Rational`
