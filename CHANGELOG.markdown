2.1.0
-----

* introduce operations for Allen's interval algebra (#18, thanks to marcosh)
* amend `recip` so that `recip (recip xs) == xs // {0}` (#21)
* add `instance Storable` for `Interval` (#25)
* add `instance Floating` for `Interval` (#26)

2.0.0
-----
* change internal representation of `Interval` and `IntegerInterval` to
  reduce memory footprint (#7, thanks Bodigrim)
* introduce `Boundary` type (#10, thanks Bodigrim)
* export `isSingleton` function for `Interval` and `IntegerInterval` (#13)
* remove deprecated `EndPoint` data type (#14, thanks Bodigrim)

1.3.1
-----
* support lattices-2.0 (Thanks to Bodigrim).
* move definitions of `Interval` and `IntegerInterval` data types into
  internal modules and abstract away representations from the rest of
  modules (Thanks to Bodigrim).


1.3.0
-----
* add `Data.IntervalSet`, `Data.IntervalMap.Lazy`, `Data.IntervalMap.Strict` modules
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
