{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module TestIntervalMap (intervalMapTestGroup) where

import Control.Applicative ((<$>))
import Control.DeepSeq
import Control.Exception (evaluate)
import Control.Monad
import Data.Functor.Identity
import qualified Data.Foldable as F
import Data.Hashable
import Data.Monoid
import Data.Traversable

import Test.ChasingBottoms.IsBottom
import Test.QuickCheck.Function
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH

import Data.Interval ( Interval, Extended (..), (<=..<=), (<=..<), (<..<=), (<..<), (<!))
import qualified Data.Interval as Interval
import qualified Data.IntervalSet as IntervalSet
import Data.IntervalMap.Lazy (IntervalMap)
import qualified Data.IntervalMap.Lazy as IntervalMap
import qualified Data.IntervalMap.Strict as IntervalMapStrict

{--------------------------------------------------------------------
  empty
--------------------------------------------------------------------}

prop_empty_is_bottom =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IntervalMap.isSubmapOf IntervalMap.empty a

prop_null_empty =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IntervalMap.null a == (a == IntervalMap.empty)

case_null_empty =
  IntervalMap.null (IntervalMap.empty :: IntervalMap Rational Integer) @?= True

{--------------------------------------------------------------------
  whole
--------------------------------------------------------------------}

case_nonnull_top =
  IntervalMap.null (IntervalMap.whole 0 :: IntervalMap Rational Integer) @?= False

case_whole_nonstrict = do
  _ <- evaluate (IntervalMap.whole bottom :: IntervalMap Rational Integer)
  return ()

case_whole_strict =
  isBottom (IntervalMapStrict.whole bottom :: IntervalMap Rational Integer) @?= True

{--------------------------------------------------------------------
  singleton
--------------------------------------------------------------------}

case_singleton_nonstrict = do
  _ <- evaluate (IntervalMap.singleton 0 bottom :: IntervalMap Rational Integer)
  return ()

case_singleton_strict =
  isBottom (IntervalMapStrict.singleton 0 bottom :: IntervalMap Rational Integer) @?= True

{--------------------------------------------------------------------
  insert
--------------------------------------------------------------------}

prop_insert_whole =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
     forAll arbitrary $ \a ->
       IntervalMap.insert Interval.whole a m == IntervalMap.singleton Interval.whole a

prop_insert_empty =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \a ->
      IntervalMap.insert Interval.empty a m == m

prop_insert_comm =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \((i1,a1) :: (Interval Rational, Integer)) ->
  forAll arbitrary $ \((i2,a2) :: (Interval Rational, Integer)) ->
    Interval.null (Interval.intersection i1 i2)
    ==>
    (IntervalMap.insert i1 a1 (IntervalMap.insert i2 a2 m)
     ==
     IntervalMap.insert i2 a2 (IntervalMap.insert i1 a1 m))

prop_insert_isSubmapOf =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      forAll arbitrary $ \a ->
        IntervalMap.isSubmapOf (IntervalMap.singleton i a) (IntervalMap.insert i a m)

prop_insert_member =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      forAll arbitrary $ \a ->
        case Interval.pickup i of
          Just k -> IntervalMap.member k (IntervalMap.insert i a m)
          Nothing -> True

prop_insert_lookup =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      forAll arbitrary $ \a ->
        case Interval.pickup i of
          Just k -> IntervalMap.lookup k (IntervalMap.insert i a m) == Just a
          Nothing -> True

prop_insert_bang =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      forAll arbitrary $ \a ->
        case Interval.pickup i of
          Just k -> IntervalMap.insert i a m IntervalMap.! k == a
          Nothing -> True

prop_insert_nonstrict =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      IntervalMap.insert i bottom m `seq` True

prop_insert_strict =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      isBottom $ IntervalMapStrict.insert i bottom m

case_insertWith_nonstrict = evaluate (IntervalMap.insertWith (\_ _ -> bottom) (3 <=..< 7) 1 m) >> return ()
  where
    m :: IntervalMap Rational Integer
    m = IntervalMap.singleton (0 <=..< 10) 0

case_insertWith_strict = isBottom (IntervalMapStrict.insertWith (\_ _ -> bottom) (3 <=..< 7) 1 m) @?= True
  where
    m :: IntervalMap Rational Integer
    m = IntervalMap.singleton (0 <=..< 10) 0

{--------------------------------------------------------------------
  delete / update
--------------------------------------------------------------------}

prop_delete_empty =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
     IntervalMap.delete Interval.empty m == m

prop_delete_whole =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
     IntervalMap.delete Interval.whole m == IntervalMap.empty

prop_delete_from_empty =
  forAll arbitrary $ \(i :: Interval Rational) ->
     IntervalMap.delete i (IntervalMap.empty :: IntervalMap Rational Integer) == IntervalMap.empty

prop_delete_comm =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \(i1 :: Interval Rational) ->
  forAll arbitrary $ \(i2 :: Interval Rational) ->
     IntervalMap.delete i1 (IntervalMap.delete i2 m)
     ==
     IntervalMap.delete i2 (IntervalMap.delete i1 m)

prop_delete_notMember =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      case Interval.pickup i of
        Just k -> IntervalMap.notMember k (IntervalMap.delete i m)
        Nothing -> True

prop_delete_lookup =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      case Interval.pickup i of
        Just k -> IntervalMap.lookup k (IntervalMap.delete i m) == Nothing
        Nothing -> True

case_adjust = IntervalMap.adjust (+1) (3 <=..< 7) m @?= expected
  where
    m :: IntervalMap Rational Integer
    m =
      IntervalMap.fromList
      [ (0 <=..< 2, 0)
      , (2 <=..< 4, 2)
      , (4 <=..< 6, 4)
      , (6 <=..< 8, 6)
      , (8 <=..< 10, 8)
      ]
    expected =
      IntervalMap.fromList
      [ (0 <=..< 2, 0)
      , (2 <=..< 3, 2)
      , (3 <=..< 4, 3)
      , (4 <=..< 6, 5)
      , (6 <=..< 7, 7)
      , (7 <=..< 8, 6)
      , (8 <=..< 10, 8)
      ]

case_asjust_nonstrict = do
  _ <- evaluate $ IntervalMap.adjust (\_ -> bottom) (3 <=..< 7) m
  return ()
  where
    m :: IntervalMap Rational Integer
    m = IntervalMap.singleton (0 <=..< 10) 0

case_asjust_strict = isBottom (IntervalMapStrict.adjust (\_ -> bottom) (3 <=..< 7) m) @?= True
  where
    m :: IntervalMap Rational Integer
    m = IntervalMap.singleton (0 <=..< 10) 0

prop_alter =
  forAll arbitrary $ \(f :: Fun (Maybe Int) (Maybe Int)) ->
  forAll arbitrary $ \(i :: Interval Rational) ->
  forAll arbitrary $ \(m :: IntervalMap Rational Int) ->
    case Interval.pickup i of
      Nothing -> True
      Just k ->
        IntervalMap.lookup k (IntervalMap.alter (apply f) i m) == apply f (IntervalMap.lookup k m)

prop_alter_nonstrict =
  forAll arbitrary $ \(i :: Interval Rational) ->
  forAll arbitrary $ \(m :: IntervalMap Rational Int) ->
    not (Interval.null i)
    ==>
    (IntervalMap.alter (\_ -> Just bottom) i m `seq` True)

prop_alter_strict =
  forAll arbitrary $ \(i :: Interval Rational) ->
  forAll arbitrary $ \(m :: IntervalMap Rational Int) ->
    not (Interval.null i)
    ==>
    isBottom (IntervalMapStrict.alter (\_ -> Just bottom) i m)

{--------------------------------------------------------------------
  Union
--------------------------------------------------------------------}

prop_union_assoc =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    IntervalMap.union a (IntervalMap.union b c) ==
    IntervalMap.union (IntervalMap.union a b) c

prop_union_unitL =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IntervalMap.union IntervalMap.empty a == a

prop_union_unitR =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IntervalMap.union a IntervalMap.empty == a

prop_union_isSubmapOf =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
    IntervalMap.isSubmapOf a (IntervalMap.union a b)

prop_union_isSubmapOf_equiv =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
    IntervalMap.isSubmapOf (IntervalMap.union a b) b
    == IntervalMap.isSubmapOf a b

case_unions_empty_list =
  IntervalMap.unions [] @?= (IntervalMap.empty :: IntervalMap Rational Integer)

prop_unions_singleton_list =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IntervalMap.unions [a] == a

prop_unions_two_elems =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
    IntervalMap.unions [a,b] == IntervalMap.union a b

case_unionWith = actual @?= expected
  where
    actual, expected :: IntervalMap Rational Integer
    actual = IntervalMap.unionWith (+) (IntervalMap.singleton (0 <=..<= 10) 1) (IntervalMap.singleton (5 <=..<= 15) 2)
    expected = IntervalMap.fromList [(0 <=..< 5, 1), (5 <=..<= 10, 3), (10 <..<= 15, 2)]

prop_unionWith_nonstrict =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
    IntervalMap.unionWith (\_ _ -> bottom) a b `seq` True

prop_unionWith_strict =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
    not (IntervalSet.null (IntervalMapStrict.keysSet a `IntervalSet.intersection` IntervalMapStrict.keysSet b))
    ==>
    isBottom (IntervalMapStrict.unionWith (\_ _ -> bottom) a b)

{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}

prop_intersection_isSubmapOf =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \b ->
      IntervalMap.isSubmapOf (IntervalMap.intersection a b) a

case_intersectionWith = actual @?= expected
  where
    actual, expected :: IntervalMap Rational Integer
    actual = IntervalMap.intersectionWith (+) (IntervalMap.singleton (0 <=..< 10) 1) (IntervalMap.singleton (5 <..<= 5) 1)
    expected = IntervalMap.singleton (5 <..< 5) 2

prop_intersectionWith_nonstrict =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \(b :: IntervalMap Rational Integer) ->
    IntervalMap.intersectionWith (\_ _ -> bottom :: Integer) a b `seq` True

prop_intersectionWith_strict =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \(b :: IntervalMap Rational Integer) ->
    not (IntervalSet.null (IntervalMapStrict.keysSet a `IntervalSet.intersection` IntervalMapStrict.keysSet b))
    ==>
    isBottom (IntervalMapStrict.intersectionWith (\_ _ -> bottom :: Integer) a b)

{--------------------------------------------------------------------
  Difference
--------------------------------------------------------------------}

prop_difference_isSubmapOf =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \(b :: IntervalMap Rational Integer) ->
      IntervalMap.isSubmapOf (a IntervalMap.\\ b) a

{--------------------------------------------------------------------
  member / lookup
--------------------------------------------------------------------}

prop_notMember_empty =
  forAll arbitrary $ \(r::Rational) ->
    r `IntervalMap.notMember` (IntervalMap.empty :: IntervalMap Rational Integer)

case_findWithDefault_case1 = IntervalMap.findWithDefault "B" 0 m @?= "A"
  where
    m :: IntervalMap Rational String
    m = IntervalMap.singleton (0 <=..<1) "A"

case_findWithDefault_case2 = IntervalMap.findWithDefault "B" 1 m @?= "B"
  where
    m :: IntervalMap Rational String
    m = IntervalMap.singleton (0 <=..<1) "A"

{--------------------------------------------------------------------
  isSubsetOf
--------------------------------------------------------------------}

prop_isSubmapOf_reflexive =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    a `IntervalMap.isSubmapOf` a

prop_isProperSubsetOf_irreflexive =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    not (a `IntervalMap.isProperSubmapOf` a)

{--------------------------------------------------------------------
  map
--------------------------------------------------------------------}

case_mapKeysMonotonic = IntervalMap.mapKeysMonotonic (+1) m1 @?= m2
  where
    m1, m2 :: IntervalMap Rational String
    m1 = IntervalMap.fromList [(0 <=..< 1, "A"), (2 <..<= 3, "B")]
    m2 = IntervalMap.fromList [(1 <=..< 2, "A"), (3 <..<= 4, "B")]

prop_map_nonstrict =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IntervalMap.map (const (bottom :: Integer)) a `seq` True

prop_map_strict =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    not (IntervalMapStrict.null a)
    ==>
    isBottom (IntervalMapStrict.map (const (bottom :: Integer)) a)

{--------------------------------------------------------------------
  Functor / Foldable / Traversal
--------------------------------------------------------------------}

prop_Functor_identity :: Property
prop_Functor_identity =
  forAll arbitrary $ \(m :: IntervalMap Rational Int) ->
    fmap id m == m

prop_Functor_compsition :: Property
prop_Functor_compsition =
  forAll arbitrary $ \(m :: IntervalMap Rational Int) ->
    forAll arbitrary $ \(f :: Fun Int Int) ->
      forAll arbitrary $ \(g :: Fun Int Int) ->
        fmap (apply f . apply g) m == fmap (apply f) (fmap (apply g) m)

prop_Foldable_foldMap :: Property
prop_Foldable_foldMap =
  forAll arbitrary $ \(m :: IntervalMap Rational Int) ->
    forAll arbitrary $ \(f :: Fun Int String) ->
      F.foldMap (apply f) m == F.fold (fmap (apply f) m)

prop_Traversable_identity :: Property
prop_Traversable_identity =
  forAll arbitrary $ \(m :: IntervalMap Rational Int) ->
    traverse Identity m == Identity m

{--------------------------------------------------------------------
  toList / fromList
--------------------------------------------------------------------}

prop_fromList_toList_id =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IntervalMap.fromList (IntervalMap.toList a) == a

prop_toAscList_toDescList =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IntervalMap.toDescList a == reverse (IntervalMap.toAscList a)

case_fromList = actual @?= expected  
  where
    actual, expected :: IntervalMap Rational Integer
    actual = IntervalMap.fromList [(0 <=..< 10, 1), (5 <..<= 15, 2)]
    expected = IntervalMap.fromList [(0 <=..<= 5, 1), (5 <..<= 15, 2)]

case_fromListWith = actual @?= expected  
  where
    actual, expected :: IntervalMap Rational Integer
    actual = IntervalMap.fromListWith (+) [(0 <=..< 10, 1), (5 <..<= 15, 2)]
    expected = IntervalMap.fromList [(0 <=..<= 5, 1), (5 <..< 10, 3), (10 <=..<= 15, 2)]

case_fromList_nonstrict = evaluate m >> return ()
  where
    m :: IntervalMap Rational Integer
    m = IntervalMap.fromList [(0 <=..< 10, bottom), (5 <..<= 15, bottom)]

case_fromList_strict = isBottom m @?= True
  where
    m :: IntervalMap Rational Integer
    m = IntervalMapStrict.fromList [(0 <=..< 10, bottom), (5 <..<= 15, bottom)]

case_fromListWith_nonstrict = evaluate m >> return ()
  where
    m :: IntervalMap Rational Integer
    m = IntervalMap.fromListWith (\_ _ -> bottom) [(0 <=..< 10, 1), (5 <..<= 15, 2)]

case_fromListWith_strict = isBottom m @?= True
  where
    m :: IntervalMap Rational Integer
    m = IntervalMapStrict.fromListWith (\_ _ -> bottom) [(0 <=..< 10, 1), (5 <..<= 15, 2)]

{--------------------------------------------------------------------
  Split
--------------------------------------------------------------------}

prop_split =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \(i :: Interval Rational) ->
      not (Interval.null i)
      ==>
      (case IntervalMap.split i m of
         (m1,m2,m3) ->
           and
           [ and [j <! i | j <- IntervalMap.keys m1]
           , and [j `Interval.isSubsetOf` i | j <- IntervalMap.keys m2]
           , and [i <! j | j <- IntervalMap.keys m3]
           ])

case_split_case1 =
  IntervalMap.split (5 <=..<= 9) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IntervalMap.fromList
      [ (2  <..<= 10, "A")
      , (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]
    smaller =
      IntervalMap.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IntervalMap.fromList
      [ (5 <=..<= 9, "A")
      ]
    larger =
      IntervalMap.fromList
      [ (9  <..<= 10, "A")
      , (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]

case_split_case2 =
  IntervalMap.split (5 <=..< 10) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IntervalMap.fromList
      [ (2  <..<= 10, "A")
      , (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]
    smaller =
      IntervalMap.fromList
      [ (2 <..< 5, "A")
      ]
    middle =
      IntervalMap.fromList
      [ (5 <=..< 10, "A")
      ]
    larger =
      IntervalMap.fromList
      [ (10, "A")
      , (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]

case_split_case3 =
  IntervalMap.split (5 <=..<= 10) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IntervalMap.fromList
      [ (2  <..<= 10, "A")
      , (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]
    smaller =
      IntervalMap.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IntervalMap.fromList
      [ (5 <=..<= 10, "A")
      ]
    larger =
      IntervalMap.fromList
      [ (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]

case_split_case4 =
  IntervalMap.split (5 <=..< 10) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IntervalMap.fromList
      [ (2   <..<  10, "A")
      , (10 <=..<= 20, "B")
      , (20  <..<= 30, "C")
      ]
    smaller =
      IntervalMap.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IntervalMap.fromList
      [ (5 <=..< 10, "A")
      ]
    larger =
      IntervalMap.fromList
      [ (10 <=..<= 20, "B")
      , (20  <..<= 30, "C")
      ]

case_split_case5 =
  IntervalMap.split (5 <=..<= 10) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IntervalMap.fromList
      [ (2   <..<  10, "A")
      , (10 <=..<= 20, "B")
      , (20  <..<= 30, "C")
      ]
    smaller =
      IntervalMap.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IntervalMap.fromList
      [ (5 <=..< 10, "A")
      , (10, "B")
      ]
    larger =
      IntervalMap.fromList
      [ (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]

case_split_case6 =
  IntervalMap.split (5 <=..< 20) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IntervalMap.fromList
      [ (2   <..<  10, "A")
      , (10 <=..<= 20, "B")
      , (20  <..<= 30, "C")
      ]
    smaller =
      IntervalMap.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IntervalMap.fromList
      [ (5  <=..< 10, "A")
      , (10 <=..< 20, "B")
      ]
    larger =
      IntervalMap.fromList
      [ (20, "B")
      , (20 <..<= 30, "C")
      ]

case_split_case7 =
  IntervalMap.split (5 <=..<= 20) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IntervalMap.fromList
      [ (2   <..<  10, "A")
      , (10 <=..<= 20, "B")
      , (20  <..<= 30, "C")
      ]
    smaller =
      IntervalMap.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IntervalMap.fromList
      [ (5  <=..<  10, "A")
      , (10 <=..<= 20, "B")
      ]
    larger =
      IntervalMap.fromList
      [ (20 <..<= 30, "C")
      ]

case_split_case8 =
  IntervalMap.split (5 <=..< 21) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IntervalMap.fromList
      [ (2   <..<  10, "A")
      , (10 <=..<= 20, "B")
      , (20  <..<= 30, "C")
      ]
    smaller =
      IntervalMap.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IntervalMap.fromList
      [ (5  <=..<  10, "A")
      , (10 <=..<= 20, "B")
      , (20  <..<  21, "C")
      ]
    larger =
      IntervalMap.fromList
      [ (21 <=..<= 30, "C")
      ]

{--------------------------------------------------------------------
  Eq
--------------------------------------------------------------------}

prop_Eq_reflexive =
  forAll arbitrary $ \(i :: IntervalMap Rational Integer) ->
    i == i

{--------------------------------------------------------------------
  Show / Read
--------------------------------------------------------------------}

prop_show_read_invariance =
  forAll arbitrary $ \(i :: IntervalMap Rational Integer) ->
    i == read (show i)

{--------------------------------------------------------------------
  Monoid
--------------------------------------------------------------------}

prop_monoid_assoc =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    a <> (b <> c) == (a <> b) <> c

prop_monoid_unitL =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    mempty <> a == a

prop_monoid_unitR =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    a <> mempty == a

{--------------------------------------------------------------------
  NFData
--------------------------------------------------------------------}

prop_rnf =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    rnf a == ()

{--------------------------------------------------------------------
  Hashable
--------------------------------------------------------------------}

prop_hash =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    hash a `seq` True

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

instance (Arbitrary k, Arbitrary a, Ord k) => Arbitrary (IntervalMap k a) where
  arbitrary = IntervalMap.fromList <$> listOf arbitrary

------------------------------------------------------------------------
-- Test harness

intervalMapTestGroup = $(testGroupGenerator)
