1.0.0
-----
* use extended-reals package for representing endpoints
* add (experimental) comparison operators that produce witnesses:
  `(<??)`, `(<=??)`, `(==??)`, `(>=??)`, `(>??)`

0.6.0
-----
* add hulls, intersections :: (Num r, Ord r) => [Interval r] -> Interval r
* fix a bug of (<=?) operator

0.5.0
-----
* fix dependency issue with QuickCheck and test-framework-quickcheck2

0.4.0
-----
* add simplestRationalWithin :: RealFrac r => Interval r -> Maybe Rational
