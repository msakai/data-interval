{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module TestInterval (intervalTestGroup) where

import qualified Algebra.Lattice as L
import Control.DeepSeq
import Control.Monad
import Data.Maybe
import Data.Ratio

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH

import Data.Interval
  ( Interval, Extended (..), (<=..<=), (<=..<), (<..<=), (<..<)
  , (<!), (<=!), (==!), (>=!), (>!), (/=!)
  , (<?), (<=?), (==?), (>=?), (>?), (/=?)
  , (<??), (<=??), (==??), (>=??), (>??), (/=??)
  )
import qualified Data.Interval as Interval

{--------------------------------------------------------------------
  empty
--------------------------------------------------------------------}

prop_empty_is_bottom =
  forAll intervals $ \a ->
    Interval.isSubsetOf Interval.empty a

prop_null_empty =
  forAll intervals $ \a ->
    Interval.null a == (a == Interval.empty)

case_null_empty =
  Interval.null (Interval.empty :: Interval Rational) @?= True

{--------------------------------------------------------------------
  whole
--------------------------------------------------------------------}

prop_whole_is_top =
  forAll intervals $ \a ->
    Interval.isSubsetOf a Interval.whole

case_nonnull_top =
  Interval.null (Interval.whole :: Interval Rational) @?= False

{--------------------------------------------------------------------
  singleton
--------------------------------------------------------------------}

-- prop_singleton_isSingleton =
--   forAll arbitrary $ \(r::Rational) ->
--     Interval.isSingleton (Interval.singleton r)

prop_singleton_member =
  forAll arbitrary $ \r ->
    Interval.member (r::Rational) (Interval.singleton r)

prop_singleton_member_intersection =
  forAll intervals $ \a ->
  forAll arbitrary $ \r ->
    let b = Interval.singleton r
    in Interval.member (r::Rational) a
       ==> Interval.intersection a b == b

prop_singleton_nonnull =
  forAll arbitrary $ \r1 ->
    not $ Interval.null $ Interval.singleton (r1::Rational)

prop_distinct_singleton_intersection =
  forAll arbitrary $ \r1 ->
  forAll arbitrary $ \r2 ->
    (r1::Rational) /= r2 ==>
      Interval.intersection (Interval.singleton r1) (Interval.singleton r2)
      == Interval.empty

{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}

prop_intersection_comm =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    Interval.intersection a b == Interval.intersection b a

prop_intersection_assoc =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
  forAll intervals $ \c ->
    Interval.intersection a (Interval.intersection b c) ==
    Interval.intersection (Interval.intersection a b) c

prop_intersection_unitL =
  forAll intervals $ \a ->
    Interval.intersection Interval.whole a == a

prop_intersection_unitR =
  forAll intervals $ \a ->
    Interval.intersection a Interval.whole == a

prop_intersection_empty =
  forAll intervals $ \a ->
    Interval.intersection a Interval.empty == Interval.empty

prop_intersection_isSubsetOf =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    Interval.isSubsetOf (Interval.intersection a b) a

prop_intersection_isSubsetOf_equiv =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    (Interval.intersection a b == a)
    == Interval.isSubsetOf a b

case_intersections_empty_list = Interval.intersections [] @?= (Interval.whole :: Interval Rational)

prop_intersections_singleton_list =
  forAll intervals $ \a -> Interval.intersections [a] == a

prop_intersections_two_elems =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    Interval.intersections [a,b] == Interval.intersection a b

{--------------------------------------------------------------------
  Hull
--------------------------------------------------------------------}

prop_hull_comm =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    Interval.hull a b == Interval.hull b a

prop_hull_assoc =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
  forAll intervals $ \c ->
    Interval.hull a (Interval.hull b c) ==
    Interval.hull (Interval.hull a b) c

prop_hull_unitL =
  forAll intervals $ \a ->
    Interval.hull Interval.empty a == a

prop_hull_unitR =
  forAll intervals $ \a ->
    Interval.hull a Interval.empty == a

prop_hull_whole =
  forAll intervals $ \a ->
    Interval.hull a Interval.whole == Interval.whole

prop_hull_isSubsetOf =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    Interval.isSubsetOf a (Interval.hull a b)

prop_hull_isSubsetOf_equiv =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    (Interval.hull a b == b)
    == Interval.isSubsetOf a b

case_hulls_empty_list = Interval.hulls [] @?= (Interval.empty :: Interval Rational)

prop_hulls_singleton_list =
  forAll intervals $ \a -> Interval.hulls [a] == a

prop_hulls_two_elems =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    Interval.hulls [a,b] == Interval.hull a b

{--------------------------------------------------------------------
  member
--------------------------------------------------------------------}

prop_member_isSubsetOf =
  forAll arbitrary $ \r ->
  forAll intervals $ \a ->
    Interval.member r a == Interval.isSubsetOf (Interval.singleton r) a

prop_notMember_empty =
  forAll arbitrary $ \(r::Rational) ->
    r `Interval.notMember` Interval.empty

{--------------------------------------------------------------------
  isSubsetOf
--------------------------------------------------------------------}

prop_isSubsetOf_refl =
  forAll intervals $ \a ->
    Interval.isSubsetOf a a

prop_isSubsetOf_trans =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
  forAll intervals $ \c ->
    Interval.isSubsetOf a b && Interval.isSubsetOf b c
    ==> Interval.isSubsetOf a c

-- prop_isSubsetOf_antisym =
--   forAll intervals $ \a ->
--   forAll intervals $ \b ->
--     Interval.isSubsetOf a b && Interval.isSubsetOf b a
--     ==> a == b

prop_isProperSubsetOf_not_refl =
  forAll intervals $ \a ->
    not (a `Interval.isProperSubsetOf` a)

-- too slow
-- prop_isProperSubsetOf_trans =
--   forAll intervals $ \a ->
--   forAll (liftM (Interval.intersection a) intervals) $ \b ->
--   forAll (liftM (Interval.intersection b) intervals) $ \c ->
--     Interval.isProperSubsetOf c b && Interval.isProperSubsetOf b a
--     ==> Interval.isProperSubsetOf c a

case_isProperSubsetOf =
  (0 <=..<= 1) `Interval.isProperSubsetOf` (0 <=..<= 2) @?= True

{-- -----------------------------------------------------------------
  isConnected
----------------------------------------------------------------- --}

prop_isConnected_reflexive =
  forAll intervals $ \a ->
    a `Interval.isConnected` a

prop_isConnected_symmetric =
  forAll intervals $ \a ->
    forAll intervals $ \b ->
      (a `Interval.isConnected` b) == (b `Interval.isConnected` a)

{--------------------------------------------------------------------
  simplestRationalWithin
--------------------------------------------------------------------}

prop_simplestRationalWithin_member =
  forAll intervals $ \a ->
    case Interval.simplestRationalWithin a of
      Nothing -> True
      Just x -> x `Interval.member` a

prop_simplestRationalWithin_and_approxRational =
  forAll arbitrary $ \(r::Rational) ->
    forAll arbitrary $ \(eps::Rational) ->
      eps > 0 ==> Interval.simplestRationalWithin (Finite (r-eps) <=..<= Finite (r+eps)) == Just (approxRational r eps)

prop_simplestRationalWithin_singleton =
  forAll arbitrary $ \(r::Rational) ->
      Interval.simplestRationalWithin (Interval.singleton r) == Just r

case_simplestRationalWithin_empty =
  Interval.simplestRationalWithin Interval.empty @?= Nothing

case_simplestRationalWithin_test1 =
  Interval.simplestRationalWithin (Finite (-0.5 :: Rational) <=..<= 0.5) @?= Just 0

case_simplestRationalWithin_test2 =
  Interval.simplestRationalWithin (Finite (2 :: Rational) <..< 3) @?= Just 2.5

case_simplestRationalWithin_test2' =
  Interval.simplestRationalWithin (Finite (-3 :: Rational) <..< (-2)) @?= Just (-2.5)

case_simplestRationalWithin_test3 =
  Interval.simplestRationalWithin (Finite (1.4142135623730951 :: Rational) <..< Finite 1.7320508075688772) @?= Just 1.5

-- http://en.wikipedia.org/wiki/Best_rational_approximation#Best_rational_approximations
case_simplestRationalWithin_test4 =
  Interval.simplestRationalWithin (Finite (3.14155 :: Rational) <..< Finite 3.14165) @?= Just (355/113)

case_simplestRationalWithin_test5 =
  Interval.simplestRationalWithin (Finite (1.1e-20 :: Rational) <..< Finite (1.2e-20)) @?= Just (1/83333333333333333334)

{--------------------------------------------------------------------
  pickup
--------------------------------------------------------------------}

prop_pickup_member_null =
  forAll intervals $ \a ->
    case Interval.pickup a of
      Nothing -> Interval.null a
      Just x -> Interval.member x a

case_pickup_empty =
  Interval.pickup (Interval.empty :: Interval Rational) @?= Nothing

case_pickup_whole =
  isJust (Interval.pickup (Interval.whole :: Interval Rational)) @?= True

prop_pickup_singleton =
  forAll arbitrary $ \(x::Rational) ->
    Interval.pickup (Interval.singleton x) == Just x

{--------------------------------------------------------------------
  width
--------------------------------------------------------------------}

case_width_null =
  Interval.width Interval.empty @?= 0

prop_width_singleton =
  forAll arbitrary $ \(r::Rational) ->
    Interval.width (Interval.singleton r) == 0

{--------------------------------------------------------------------
  Comparison
--------------------------------------------------------------------}

case_lt_all_1 = (a <! b) @?= False
  where
    a, b :: Interval Rational
    a = NegInf <..<= 0
    b = 0 <=..< PosInf

case_lt_all_2 = (a <! b) @?= True
  where
    a, b :: Interval Rational
    a = NegInf <..< 0
    b = 0 <=..< PosInf

case_lt_all_3 = (a <! b) @?= True
  where
    a, b :: Interval Rational
    a = NegInf <..<= 0
    b = 0 <..< PosInf

case_lt_all_4 = (a <! b) @?= False
  where
    a, b :: Interval Rational
    a = 0 <=..< PosInf
    b = 1 <=..< PosInf

case_lt_some_1 = (a <? b) @?= False
  where
    a, b :: Interval Rational
    a = 0 <=..< PosInf
    b = NegInf <..<= 0

case_lt_some_2 = (a <? b) @?= False
  where
    a, b :: Interval Rational
    a = 0 <..< PosInf
    b = NegInf <..<= 0

case_lt_some_3 = (a <? b) @?= False
  where
    a, b :: Interval Rational
    a = 0 <=..< PosInf
    b = NegInf <..< 0

case_lt_some_4 = (a <! b) @?= False
  where
    a, b :: Interval Rational
    a = 0 <=..< PosInf
    b = 1 <=..< PosInf

case_le_some_1 = (a <=? b) @?= True
  where
    a, b :: Interval Rational
    a = 0 <=..< PosInf
    b = NegInf <..<= 0

case_le_some_2 = (a <=? b) @?= False
  where
    a, b :: Interval Rational
    a = 0 <..< PosInf
    b = NegInf <..<= 0

case_le_some_3 = (a <=? b) @?= False
  where
    a, b :: Interval Rational
    a = 0 <=..< PosInf
    b = NegInf <..< 0

prop_lt_all_not_refl =
  forAll intervals $ \a -> not (Interval.null a) ==> not (a <! a)

prop_le_some_refl =
  forAll intervals $ \a -> not (Interval.null a) ==> a <=? a

prop_ne_all_not_refl =
  forAll intervals $ \a -> not (Interval.null a) ==> not (a /=! a)

prop_lt_all_singleton =
  forAll arbitrary $ \a ->
  forAll arbitrary $ \b ->
    (a::Rational) < b ==> Interval.singleton a <! Interval.singleton b

prop_lt_all_singleton_2 =
  forAll arbitrary $ \a ->
    not $ Interval.singleton (a::Rational) <! Interval.singleton a

prop_le_all_singleton =
  forAll arbitrary $ \a ->
  forAll arbitrary $ \b ->
    (a::Rational) <= b ==> Interval.singleton a <=! Interval.singleton b

prop_le_all_singleton_2 =
  forAll arbitrary $ \a ->
    Interval.singleton (a::Rational) <=! Interval.singleton a

prop_eq_all_singleton =
  forAll arbitrary $ \a ->
    Interval.singleton (a::Rational) ==! Interval.singleton a

prop_ne_all_singleton =
  forAll arbitrary $ \a ->
  forAll arbitrary $ \b ->
    (a::Rational) /= b ==> Interval.singleton a /=! Interval.singleton b

prop_ne_all_singleton_2 =
  forAll arbitrary $ \a ->
    not $ Interval.singleton (a::Rational) /=! Interval.singleton a

prop_lt_some_singleton =
  forAll arbitrary $ \a ->
  forAll arbitrary $ \b ->
    (a::Rational) < b ==> Interval.singleton a <? Interval.singleton b

prop_lt_some_singleton_2 =
  forAll arbitrary $ \a ->
    not $ Interval.singleton (a::Rational) <? Interval.singleton a

prop_le_some_singleton =
  forAll arbitrary $ \a ->
  forAll arbitrary $ \b ->
    (a::Rational) <= b ==> Interval.singleton a <=? Interval.singleton b

prop_le_some_singleton_2 =
  forAll arbitrary $ \a ->
    Interval.singleton (a::Rational) <=? Interval.singleton a

prop_eq_some_singleton =
  forAll arbitrary $ \a ->
    Interval.singleton (a::Rational) ==? Interval.singleton a

prop_lt_all_empty =
  forAll intervals $ \a -> a <! Interval.empty

prop_lt_all_empty_2 =
  forAll intervals $ \a -> Interval.empty <! a

prop_le_all_empty =
  forAll intervals $ \a -> a <=! Interval.empty

prop_le_all_empty_2 =
  forAll intervals $ \a -> Interval.empty <=! a

prop_eq_all_empty =
  forAll intervals $ \a -> a ==! Interval.empty

prop_ne_all_empty =
  forAll intervals $ \a -> a /=! Interval.empty

prop_lt_some_empty =
  forAll intervals $ \a -> not (a <? Interval.empty)

prop_lt_some_empty_2 =
  forAll intervals $ \a -> not (Interval.empty <? a)

prop_le_some_empty =
  forAll intervals $ \a -> not (a <=? Interval.empty)

prop_le_some_empty_2 =
  forAll intervals $ \a -> not (Interval.empty <=? a)

prop_eq_some_empty =
  forAll intervals $ \a -> not (a ==? Interval.empty)

prop_intersect_le_some =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    not (Interval.null (Interval.intersection a b))
    ==> a <=? b

prop_intersect_eq_some =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    not (Interval.null (Interval.intersection a b))
    ==> a ==? b

prop_le_some_witness =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    case a <=?? b of
      Nothing ->
        forAll arbitrary $ \(x,y) ->
          not (Interval.member x a && Interval.member y b && x <= y)
      Just (x,y) ->
        Interval.member x a .&&. Interval.member y b .&&. x <= y

prop_lt_some_witness =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    case a <?? b of
      Nothing ->
        forAll arbitrary $ \(x,y) ->
          not (Interval.member x a && Interval.member y b && x < y)
      Just (x,y) ->
        Interval.member x a .&&. Interval.member y b .&&. x < y

case_lt_some_witness_test1 = do
  let i1 = 0
      i2 = 0 <=..<= 1
  case i1 <?? i2 of
    Nothing -> assertFailure "should not be Nothing"
    Just (a,b) -> do
      unless (a `Interval.member` i1) $ assertFailure (show a ++ "is not a member of " ++ show i1)
      unless (b `Interval.member` i2) $ assertFailure (show b ++ "is not a member of " ++ show i2)
      unless (a < b) $ assertFailure (show a ++ " < " ++ show b ++ " failed")

prop_eq_some_witness =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    case a ==?? b of
      Nothing ->
        forAll arbitrary $ \x ->
          not (Interval.member x a && Interval.member x b)
      Just (x,y) ->
        Interval.member x a .&&. Interval.member y b .&&. x == y

prop_ne_some_witness =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    case a /=?? b of
      Nothing ->
        forAll arbitrary $ \x ->
        forAll arbitrary $ \y ->
          not (Interval.member x a && Interval.member y b && x /= y)
      Just (x,y) ->
        Interval.member x a .&&. Interval.member y b .&&. x /= y

case_ne_some_witness_test1 = do
  let i1 = 0
      i2 = 0 <=..<= 1
  case i1 /=?? i2 of
    Nothing -> assertFailure "should not be Nothing"
    Just (a,b) -> do
      unless (a `Interval.member` i1) $ assertFailure (show a ++ "is not a member of " ++ show i1)
      unless (b `Interval.member` i2) $ assertFailure (show b ++ "is not a member of " ++ show i2)
      unless (a /= b) $ assertFailure (show a ++ " /= " ++ show b ++ " failed")

case_ne_some_witness_test2 = do
  let i1 = 0 <=..<= 1
      i2 = 1
  case i1 /=?? i2 of
    Nothing -> assertFailure "should not be Nothing"
    Just (a,b) -> do
      unless (a `Interval.member` i1) $ assertFailure (show a ++ "is not a member of " ++ show i1)
      unless (b `Interval.member` i2) $ assertFailure (show b ++ "is not a member of " ++ show i2)
      unless (a /= b) $ assertFailure (show a ++ " /= " ++ show b ++ " failed")

prop_le_some_witness_forget =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    isJust (a <=?? b) == (a <=? b)

prop_lt_some_witness_forget =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    isJust (a <?? b) == (a <? b)

prop_eq_some_witness_forget =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    isJust (a ==?? b) == (a ==? b)

prop_ne_some_witness_forget =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    isJust (a /=?? b) == (a /=? b)

{--------------------------------------------------------------------
  Num
--------------------------------------------------------------------}

prop_scale_empty =
  forAll arbitrary $ \r ->
    Interval.singleton (r::Rational) * Interval.empty == Interval.empty

prop_add_comm =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    a + b == b + a

prop_add_assoc =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
  forAll intervals $ \c ->
    a + (b + c) == (a + b) + c

prop_add_unitL =
  forAll intervals $ \a ->
    Interval.singleton 0 + a == a

prop_add_unitR =
  forAll intervals $ \a ->
    a + Interval.singleton 0 == a

prop_add_member =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    and [ (x+y) `Interval.member` (a+b)
        | x <- maybeToList $ Interval.pickup a
        , y <- maybeToList $ Interval.pickup b
        ]

prop_mult_comm =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    a * b == b * a

prop_mult_assoc =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
  forAll intervals $ \c ->
    a * (b * c) == (a * b) * c

prop_mult_unitL =
  forAll intervals $ \a ->
    Interval.singleton 1 * a == a

prop_mult_unitR =
  forAll intervals $ \a ->
    a * Interval.singleton 1 == a

prop_mult_dist =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
  forAll intervals $ \c ->
    (a * (b + c)) `Interval.isSubsetOf` (a * b + a * c)

prop_mult_empty =
  forAll intervals $ \a ->
    Interval.empty * a == Interval.empty

prop_mult_zero =
  forAll intervals $ \a ->
    not (Interval.null a) ==> Interval.singleton 0 * a ==  Interval.singleton 0

prop_mult_member =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    and [ (x*y) `Interval.member` (a*b)
        | x <- maybeToList $ Interval.pickup a
        , y <- maybeToList $ Interval.pickup b
        ]

case_mult_test1 = ival1 * ival2 @?= ival3
  where
    ival1 :: Interval Rational
    ival1 = 1 <=..<= 2
    ival2 = 1 <=..<= 2
    ival3 = 1 <=..<= 4

case_mult_test2 = ival1 * ival2 @?= ival3
  where
    ival1 :: Interval Rational
    ival1 = 1 <=..<= 2
    ival2 = 1 <..< 2
    ival3 = 1 <..< 4

case_mult_test3 = ival1 * ival2 @?= ival3
  where
    ival1 :: Interval Rational
    ival1 = 1 <..< 2
    ival2 = 1 <..< 2
    ival3 = 1 <..< 4

case_mult_test4 = ival1 * ival2 @?= ival3
  where
    ival1 :: Interval Rational
    ival1 = 2 <..< PosInf
    ival2 = 3 <..< PosInf
    ival3 = 6 <..< PosInf

case_mult_test5 = ival1 * ival2 @?= ival3
  where
    ival1 :: Interval Rational
    ival1 = NegInf <..< (-3)
    ival2 = NegInf <..< (-2)
    ival3 = 6 <..< PosInf

case_mult_test6 = ival1 * ival2 @?= ival3
  where
    ival1 :: Interval Rational
    ival1 = 2 <..< PosInf
    ival2 = NegInf <..< (-2)
    ival3 = NegInf <..< (-4)

prop_abs_signum =
  forAll intervals $ \a ->
    abs (signum a) `Interval.isSubsetOf` (0 <=..<= 1)

prop_negate_negate =
  forAll intervals $ \a ->
    negate (negate a) == a

{--------------------------------------------------------------------
  Fractional
--------------------------------------------------------------------}

prop_recip_singleton =
  forAll arbitrary $ \r ->
    let n = fromIntegral (numerator r)
        d = fromIntegral (denominator r)
    in Interval.singleton n / Interval.singleton d == Interval.singleton (r::Rational)

case_recip_empty =
  recip Interval.empty @?= Interval.empty

case_recip_pos =
  recip pos @?= pos

case_recip_neg =
  recip neg @?= neg

case_recip_test1 = recip i1 @?= i2
  where
    i1, i2 :: Interval Rational
    i1 = 2 <=..< PosInf
    i2 = 0 <..<= (1/2)

case_recip_test2 = recip i1 @?= i2
  where
    i1, i2 :: Interval Rational
    i1 = 0 <..<= 10
    i2 = (1/10) <=..< PosInf

case_recip_test3 = recip i1 @?= i2
  where
    i1, i2 :: Interval Rational
    i1 = -10 <=..< 0
    i2 = NegInf <..<= (-1/10)

prop_recip_zero =
  forAll intervals $ \a ->
    0 `Interval.member` a ==> recip a == Interval.whole

{--------------------------------------------------------------------
  Lattice
--------------------------------------------------------------------}

prop_Lattice_Leq_welldefined =
  forAll intervals $ \a b ->
    a `L.meetLeq` b == a `L.joinLeq` b

prop_top =
  forAll intervals $ \a ->
    a `L.joinLeq` L.top

prop_bottom =
  forAll intervals $ \a ->
    L.bottom `L.joinLeq` a

{--------------------------------------------------------------------
  Read
--------------------------------------------------------------------}

prop_show_read_invariance =
  forAll intervals $ \i -> do
    i == read (show i)

case_read_old =
  read "interval (Finite (0 % 1), True) (PosInf, False)" @?= 
  (Interval.interval (Finite 0, True) (PosInf, False) :: Interval Rational)

{--------------------------------------------------------------------
  NFData
--------------------------------------------------------------------}

prop_rnf =
  forAll intervals $ \a ->
    rnf a == ()

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

------------------------------------------------------------------------
-- Test harness

intervalTestGroup = $(testGroupGenerator)
