{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module TestIntervalSet (intervalSetTestGroup) where

import qualified Algebra.Lattice as L
import Control.Applicative ((<$>))
import Control.DeepSeq
import Control.Monad
import Data.Maybe
import Data.Ratio

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH

import Data.Interval ( Interval, Extended (..), (<=..<=), (<=..<), (<..<=), (<..<) )
import qualified Data.Interval as Interval
import Data.IntervalSet (IntervalSet)
import qualified Data.IntervalSet as IntervalSet

{--------------------------------------------------------------------
  empty
--------------------------------------------------------------------}

prop_empty_is_bottom =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.isSubsetOf IntervalSet.empty a

prop_null_empty =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.null a == (a == IntervalSet.empty)

case_null_empty =
  IntervalSet.null (IntervalSet.empty :: IntervalSet Rational) @?= True

{--------------------------------------------------------------------
  whole
--------------------------------------------------------------------}

prop_whole_is_top =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.isSubsetOf a IntervalSet.whole

case_nonnull_top =
  IntervalSet.null (IntervalSet.whole :: IntervalSet Rational) @?= False

{--------------------------------------------------------------------
  singleton
--------------------------------------------------------------------}

prop_singleton_member =
  forAll arbitrary $ \r ->
    IntervalSet.member (r::Rational) (IntervalSet.singleton r)

prop_singleton_nonnull =
  forAll arbitrary $ \r1 ->
    not $ IntervalSet.null $ IntervalSet.singleton (r1::Rational)

{--------------------------------------------------------------------
  complement
--------------------------------------------------------------------}

prop_complement_involution =
  forAll arbitrary $ \(s :: IntervalSet Rational) ->
    IntervalSet.complement (IntervalSet.complement s) == s

prop_complement_union =
  forAll arbitrary $ \(is :: IntervalSet Rational) ->
    IntervalSet.union is (IntervalSet.complement is) == IntervalSet.whole

prop_complement_intersection =
  forAll arbitrary $ \(is :: IntervalSet Rational) ->
    IntervalSet.intersection is (IntervalSet.complement is) == IntervalSet.empty

{--------------------------------------------------------------------
  fromIntervalList
--------------------------------------------------------------------}

case_fromIntervalList_connected =
  IntervalSet.fromIntervalList [ (0 <=..< 1 :: Interval Rational), 1 <=..<2 ]
  @?= IntervalSet.fromIntervalList [ 0 <=..<2 ]

{--------------------------------------------------------------------
  insert
--------------------------------------------------------------------}

prop_insert_Interval_whole =
  forAll arbitrary $ \(i :: Interval Rational) ->
     IntervalSet.insert i IntervalSet.whole == IntervalSet.whole

prop_insert_whole_IntervalSet =
  forAll arbitrary $ \(is :: IntervalSet Rational) ->
     IntervalSet.insert Interval.whole is == IntervalSet.whole

prop_insert_comm =
  forAll arbitrary $ \(is :: IntervalSet Rational) ->
  forAll arbitrary $ \(i1 :: Interval Rational) ->
  forAll arbitrary $ \(i2 :: Interval Rational) ->
     IntervalSet.insert i1 (IntervalSet.insert i2 is)
     ==
     IntervalSet.insert i2 (IntervalSet.insert i1 is)

case_insert_connected =
  IntervalSet.insert (1 <=..< 2 :: Interval Rational) (IntervalSet.fromIntervalList [ 0 <=..< 1, 2 <=..< 3 ])
  @?= IntervalSet.fromIntervalList [ 0 <=..< 3 ]

{--------------------------------------------------------------------
  delete
--------------------------------------------------------------------}

prop_delete_Interval_empty =
  forAll arbitrary $ \(i :: Interval Rational) ->
     IntervalSet.delete i IntervalSet.empty == IntervalSet.empty

prop_delete_empty_IntervalSet =
  forAll arbitrary $ \(is :: IntervalSet Rational) ->
     IntervalSet.delete Interval.empty is == is

prop_delete_comm =
  forAll arbitrary $ \(is :: IntervalSet Rational) ->
  forAll arbitrary $ \(i1 :: Interval Rational) ->
  forAll arbitrary $ \(i2 :: Interval Rational) ->
     IntervalSet.delete i1 (IntervalSet.delete i2 is)
     ==
     IntervalSet.delete i2 (IntervalSet.delete i1 is)

case_delete_connected =
  IntervalSet.delete (1 <=..< 2) (IntervalSet.fromIntervalList [ 0 <=..< 3 :: Interval Rational ])
  @?=  (IntervalSet.fromIntervalList [ 0 <=..< 1, 2 <=..< 3 ])

{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}

prop_intersection_comm =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
    IntervalSet.intersection a b == IntervalSet.intersection b a

prop_intersection_assoc =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    IntervalSet.intersection a (IntervalSet.intersection b c) ==
    IntervalSet.intersection (IntervalSet.intersection a b) c

prop_intersection_unitL =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.intersection IntervalSet.whole a == a

prop_intersection_unitR =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.intersection a IntervalSet.whole == a

prop_intersection_empty =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.intersection a IntervalSet.empty == IntervalSet.empty

prop_intersection_isSubsetOf =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
    IntervalSet.isSubsetOf (IntervalSet.intersection a b) a

prop_intersection_isSubsetOf_equiv =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
    (IntervalSet.intersection a b == a)
    == IntervalSet.isSubsetOf a b

case_intersections_empty_list =
  IntervalSet.intersections [] @?= (IntervalSet.whole :: IntervalSet Rational)

prop_intersections_singleton_list =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.intersections [a] == a

prop_intersections_two_elems =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
    IntervalSet.intersections [a,b] == IntervalSet.intersection a b

{--------------------------------------------------------------------
  Union
--------------------------------------------------------------------}

prop_union_comm =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
    IntervalSet.union a b == IntervalSet.union b a

prop_union_assoc =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    IntervalSet.union a (IntervalSet.union b c) ==
    IntervalSet.union (IntervalSet.union a b) c

prop_union_unitL =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.union IntervalSet.empty a == a

prop_union_unitR =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.union a IntervalSet.empty == a

prop_union_whole =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.union a IntervalSet.whole == IntervalSet.whole

prop_union_isSubsetOf =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
    IntervalSet.isSubsetOf a (IntervalSet.union a b)

prop_union_isSubsetOf_equiv =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
    (IntervalSet.union a b == b)
    == IntervalSet.isSubsetOf a b

case_unions_empty_list =
  IntervalSet.unions [] @?= (IntervalSet.empty :: IntervalSet Rational)

prop_unions_singleton_list =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.unions [a] == a

prop_unions_two_elems =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
    IntervalSet.unions [a,b] == IntervalSet.union a b

prop_union_intersection_duality =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
    IntervalSet.complement (IntervalSet.union a b) ==
    IntervalSet.intersection (IntervalSet.complement a) (IntervalSet.complement b)

{--------------------------------------------------------------------
  member
--------------------------------------------------------------------}

prop_notMember_empty =
  forAll arbitrary $ \(r::Rational) ->
    r `IntervalSet.notMember` IntervalSet.empty

{--------------------------------------------------------------------
  toIntervalList / fromIntervalList
--------------------------------------------------------------------}

prop_fromIntervalList_toIntervalList_id =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.fromIntervalList (IntervalSet.toIntervalList a) == a

{--------------------------------------------------------------------
  Show / Read
--------------------------------------------------------------------}

prop_show_read_invariance =
  forAll arbitrary $ \(i :: IntervalSet Rational) ->
    i == read (show i)

{--------------------------------------------------------------------
  NFData
--------------------------------------------------------------------}

prop_rnf =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    rnf a == ()

{--------------------------------------------------------------------
  Num
--------------------------------------------------------------------}

prop_scale_empty =
  forAll arbitrary $ \r ->
    IntervalSet.singleton (r::Rational) * IntervalSet.empty == IntervalSet.empty

prop_add_comm =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
    a + b == b + a

prop_add_assoc =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    a + (b + c) == (a + b) + c

prop_add_unitL =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.singleton 0 + a == a

prop_add_unitR =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    a + IntervalSet.singleton 0 == a

prop_add_member =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
    and [ (x+y) `IntervalSet.member` (a+b)
        | x <- maybeToList $ pickup a
        , y <- maybeToList $ pickup b
        ]

prop_mult_comm =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
    a * b == b * a

prop_mult_assoc =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    a * (b * c) == (a * b) * c

prop_mult_unitL =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.singleton 1 * a == a

prop_mult_unitR =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    a * IntervalSet.singleton 1 == a

prop_mult_dist =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    (a * (b + c)) `IntervalSet.isSubsetOf` (a * b + a * c)

prop_mult_empty =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    IntervalSet.empty * a == IntervalSet.empty

prop_mult_zero =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    not (IntervalSet.null a) ==> IntervalSet.singleton 0 * a ==  IntervalSet.singleton 0

prop_mult_member =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
  forAll arbitrary $ \b ->
    and [ (x*y) `IntervalSet.member` (a*b)
        | x <- maybeToList $ pickup a
        , y <- maybeToList $ pickup b
        ]

prop_abs_signum =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    abs (signum a) `IntervalSet.isSubsetOf` IntervalSet.fromInterval (0 <=..<= 1)

prop_negate_negate =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    negate (negate a) == a

{--------------------------------------------------------------------
  Fractional
--------------------------------------------------------------------}

prop_recip_singleton =
  forAll arbitrary $ \r ->
    let n = fromIntegral (numerator r)
        d = fromIntegral (denominator r)
    in IntervalSet.singleton n / IntervalSet.singleton d == IntervalSet.singleton (r::Rational)

prop_recip_zero =
  forAll arbitrary $ \(a :: IntervalSet Rational) ->
    0 `IntervalSet.member` a ==> recip a == IntervalSet.whole

{--------------------------------------------------------------------
  Generators
--------------------------------------------------------------------}

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
    return $ Interval.interval lb ub

instance (Arbitrary r, Ord r) => Arbitrary (IntervalSet r) where
  arbitrary =  do
    b <- arbitrary
    if b then
      return IntervalSet.whole
    else do
      xs <- IntervalSet.fromIntervalList <$> listOf arbitrary
      b2 <- arbitrary
      if b2 then
        return xs
      else
        return $ IntervalSet.complement xs

intervals :: Gen (Interval Rational)
intervals = arbitrary

pos :: Interval Rational
pos = 0 <..< PosInf

neg :: Interval Rational
neg = NegInf <..< 0

nonpos :: Interval Rational
nonpos = NegInf <..<= 0

nonneg :: Interval Rational
nonneg = 0 <=..< PosInf

pickup :: (Ord r, Real r, Fractional r) => IntervalSet r -> Maybe r
pickup xs = do
  x <- listToMaybe (IntervalSet.toIntervalList xs)
  Interval.pickup x

------------------------------------------------------------------------
-- Test harness

intervalSetTestGroup = $(testGroupGenerator)
