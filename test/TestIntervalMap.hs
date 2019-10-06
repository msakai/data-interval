{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE CPP, TemplateHaskell, ScopedTypeVariables #-}
module TestIntervalMap (intervalMapTestGroup) where

import Control.DeepSeq
import Control.Exception (evaluate)
import Control.Monad
import Data.Functor.Identity
import qualified Data.Foldable as F
import Data.Generics.Schemes
import Data.Hashable
import Data.Maybe
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<$>))
import Data.Traversable (Traversable(..))
#endif
#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup ((<>))
#endif
import Data.Typeable

import Test.ChasingBottoms.IsBottom
import Test.QuickCheck.Function
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH

import Data.Interval ( Interval, Extended (..), (<=..<=), (<=..<), (<..<=), (<..<), (<!))
import qualified Data.Interval as Interval
import qualified Data.IntervalSet as IntervalSet
import Data.IntervalMap.Lazy (IntervalMap)
import qualified Data.IntervalMap.Lazy as IML
import qualified Data.IntervalMap.Strict as IMS

{--------------------------------------------------------------------
  empty
--------------------------------------------------------------------}

prop_empty_is_bottom :: Property
prop_empty_is_bottom =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IML.isSubmapOf IML.empty a

prop_null_empty :: Property
prop_null_empty =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IML.null a == (a == IML.empty)

case_null_empty :: Assertion
case_null_empty =
  IML.null (IML.empty :: IntervalMap Rational Integer) @?= True

{--------------------------------------------------------------------
  whole
--------------------------------------------------------------------}

case_nonnull_whole :: Assertion
case_nonnull_whole =
  IML.null (IML.whole 0 :: IntervalMap Rational Integer) @?= False

prop_whole_Lazy_Strict :: Property
prop_whole_Lazy_Strict = do
  forAll arbitrary $ \(a :: Integer) ->
    (IML.whole a :: IntervalMap Rational Integer) == IMS.whole a

case_whole_nonstrict :: Assertion
case_whole_nonstrict = do
  _ <- evaluate (IML.whole bottom :: IntervalMap Rational Integer)
  return ()

case_whole_strict :: Assertion
case_whole_strict =
  isBottom (IMS.whole bottom :: IntervalMap Rational Integer) @?= True

{--------------------------------------------------------------------
  singleton
--------------------------------------------------------------------}

prop_singleton_insert :: Property
prop_singleton_insert = do
  forAll arbitrary $ \(i :: Interval Rational) ->
    forAll arbitrary $ \(a :: Integer) ->
      IML.singleton i a == IML.insert i a IML.empty

prop_singleton_Lazy_Strict :: Property
prop_singleton_Lazy_Strict = do
  forAll arbitrary $ \(i :: Interval Rational) ->
    forAll arbitrary $ \(a :: Integer) ->
      IML.singleton i a == IMS.singleton i a

case_singleton_nonstrict :: Assertion
case_singleton_nonstrict = do
  _ <- evaluate (IML.singleton 0 bottom :: IntervalMap Rational Integer)
  return ()

case_singleton_strict :: Assertion
case_singleton_strict =
  isBottom (IMS.singleton 0 bottom :: IntervalMap Rational Integer) @?= True

{--------------------------------------------------------------------
  insert
--------------------------------------------------------------------}

prop_insert_whole :: Property
prop_insert_whole =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \a ->
      IML.insert Interval.whole a m == IML.whole a

prop_insert_empty :: Property
prop_insert_empty =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \a ->
      IML.insert Interval.empty a m == m

prop_insert_comm :: Property
prop_insert_comm =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \(i1,a1) ->
  forAll arbitrary $ \(i2,a2) ->
    Interval.null (Interval.intersection i1 i2)
    ==>
    (IML.insert i1 a1 (IML.insert i2 a2 m) == IML.insert i2 a2 (IML.insert i1 a1 m))

prop_insert_isSubmapOf :: Property
prop_insert_isSubmapOf =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      forAll arbitrary $ \a ->
        IML.isSubmapOf (IML.singleton i a) (IML.insert i a m)

prop_insert_member :: Property
prop_insert_member =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      forAll arbitrary $ \a ->
        case Interval.pickup i of
          Just k -> IML.member k (IML.insert i a m)
          Nothing -> True

prop_insert_lookup :: Property
prop_insert_lookup =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      forAll arbitrary $ \a ->
        case Interval.pickup i of
          Just k -> IML.lookup k (IML.insert i a m) == Just a
          Nothing -> True

prop_insert_bang :: Property
prop_insert_bang =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      forAll arbitrary $ \a ->
        case Interval.pickup i of
          Just k -> IML.insert i a m IML.! k == a
          Nothing -> True

prop_insert_Lazy_Strict :: Property
prop_insert_Lazy_Strict =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      forAll arbitrary $ \a ->
        IML.insert i a m == IMS.insert i a m

prop_insert_nonstrict :: Property
prop_insert_nonstrict =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      IML.insert i bottom m `seq` True

prop_insert_strict :: Property
prop_insert_strict =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      isBottom $ IMS.insert i bottom m

prop_insertWith_Lazy_Strict :: Property
prop_insertWith_Lazy_Strict =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \(f :: Fun (Integer,Integer) Integer) ->
      forAll arbitrary $ \i ->
        forAll arbitrary $ \a ->
          IML.insertWith (curry (apply f)) i a m == IMS.insertWith (curry (apply f)) i a m

case_insertWith_nonstrict :: Assertion
case_insertWith_nonstrict = evaluate (IML.insertWith (\_ _ -> bottom) (3 <=..< 7) 1 m) >> return ()
  where
    m :: IntervalMap Rational Integer
    m = IML.singleton (0 <=..< 10) 0

case_insertWith_strict :: Assertion
case_insertWith_strict = isBottom (IMS.insertWith (\_ _ -> bottom) (3 <=..< 7) 1 m) @?= True
  where
    m :: IntervalMap Rational Integer
    m = IMS.singleton (0 <=..< 10) 0

{--------------------------------------------------------------------
  delete / update
--------------------------------------------------------------------}

prop_delete_empty :: Property
prop_delete_empty =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
     IML.delete Interval.empty m == m

prop_delete_whole :: Property
prop_delete_whole =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
     IML.delete Interval.whole m == IML.empty

prop_delete_from_empty :: Property
prop_delete_from_empty =
  forAll arbitrary $ \(i :: Interval Rational) ->
     IML.delete i (IML.empty :: IntervalMap Rational Integer) == IML.empty

prop_delete_comm :: Property
prop_delete_comm =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \i1 ->
  forAll arbitrary $ \i2 ->
     IML.delete i1 (IML.delete i2 m) == IML.delete i2 (IML.delete i1 m)

prop_delete_notMember :: Property
prop_delete_notMember =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      case Interval.pickup i of
        Just k -> IML.notMember k (IML.delete i m)
        Nothing -> True

prop_delete_lookup :: Property
prop_delete_lookup =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      case Interval.pickup i of
        Just k -> IML.lookup k (IML.delete i m) == Nothing
        Nothing -> True

case_adjust :: Assertion
case_adjust = IML.adjust (+1) (3 <=..< 7) m @?= expected
  where
    m :: IntervalMap Rational Integer
    m =
      IML.fromList
      [ (0 <=..< 2, 0)
      , (2 <=..< 4, 2)
      , (4 <=..< 6, 4)
      , (6 <=..< 8, 6)
      , (8 <=..< 10, 8)
      ]
    expected =
      IML.fromList
      [ (0 <=..< 2, 0)
      , (2 <=..< 3, 2)
      , (3 <=..< 4, 3)
      , (4 <=..< 6, 5)
      , (6 <=..< 7, 7)
      , (7 <=..< 8, 6)
      , (8 <=..< 10, 8)
      ]

prop_adjust_Lazy_Strict :: Property
prop_adjust_Lazy_Strict =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \(f :: Fun Integer Integer) ->
      forAll arbitrary $ \i ->
        IML.adjust (apply f) i m == IMS.adjust (apply f) i m

case_asjust_nonstrict :: Assertion
case_asjust_nonstrict = do
  _ <- evaluate $ IML.adjust (\_ -> bottom) (3 <=..< 7) m
  return ()
  where
    m :: IntervalMap Rational Integer
    m = IML.singleton (0 <=..< 10) 0

case_asjust_strict :: Assertion
case_asjust_strict = isBottom (IMS.adjust (\_ -> bottom) (3 <=..< 7) m) @?= True
  where
    m :: IntervalMap Rational Integer
    m = IMS.singleton (0 <=..< 10) 0

prop_alter :: Property
prop_alter =
  forAll arbitrary $ \(m :: IntervalMap Rational Int) ->
  forAll arbitrary $ \i ->
  forAll arbitrary $ \f ->
    case Interval.pickup i of
      Nothing -> True
      Just k ->
        IML.lookup k (IML.alter (apply f) i m) == apply f (IML.lookup k m)

prop_alter_Lazy_Strict :: Property
prop_alter_Lazy_Strict =
  forAll arbitrary $ \(m :: IntervalMap Rational Int) ->
  forAll arbitrary $ \i ->
  forAll arbitrary $ \f ->
    IML.alter (apply f) i m == IMS.alter (apply f) i m

prop_alter_nonstrict :: Property
prop_alter_nonstrict =
  forAll arbitrary $ \(m :: IntervalMap Rational Int) ->
  forAll arbitrary $ \i ->
    not (Interval.null i)
    ==>
    (IML.alter (\_ -> Just bottom) i m `seq` True)

prop_alter_strict :: Property
prop_alter_strict =
  forAll arbitrary $ \(m :: IntervalMap Rational Int) ->
  forAll arbitrary $ \i ->
    not (Interval.null i)
    ==>
    isBottom (IMS.alter (\_ -> Just bottom) i m)

{--------------------------------------------------------------------
  Union
--------------------------------------------------------------------}

prop_union_assoc :: Property
prop_union_assoc =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    IML.union a (IML.union b c) == IML.union (IML.union a b) c

prop_union_unitL :: Property
prop_union_unitL =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IML.union IML.empty a == a

prop_union_unitR :: Property
prop_union_unitR =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IML.union a IML.empty == a

prop_union_isSubmapOf :: Property
prop_union_isSubmapOf =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
    IML.isSubmapOf a (IML.union a b)

prop_union_isSubmapOf_equiv :: Property
prop_union_isSubmapOf_equiv =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
    IML.isSubmapOf (IML.union a b) b
    == IML.isSubmapOf a b

case_unions_empty_list :: Assertion
case_unions_empty_list =
  IML.unions [] @?= (IML.empty :: IntervalMap Rational Integer)

prop_unions_singleton_list :: Property
prop_unions_singleton_list =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IML.unions [a] == a

prop_unions_two_elems :: Property
prop_unions_two_elems =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
    IML.unions [a,b] == IML.union a b

case_unionWith :: Assertion
case_unionWith = actual @?= expected
  where
    actual, expected :: IntervalMap Rational Integer
    actual = IML.unionWith (+) (IML.singleton (0 <=..<= 10) 1) (IML.singleton (5 <=..<= 15) 2)
    expected = IML.fromList [(0 <=..< 5, 1), (5 <=..<= 10, 3), (10 <..<= 15, 2)]

prop_unionWith_Lazy_Strict :: Property
prop_unionWith_Lazy_Strict =
  forAll arbitrary $ \(a :: IntervalMap Rational Int) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \f ->
    IML.unionWith (curry (apply f)) a b == IMS.unionWith (curry (apply f)) a b

prop_unionWith_nonstrict :: Property
prop_unionWith_nonstrict =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
    IML.unionWith (\_ _ -> bottom) a b `seq` True

prop_unionWith_strict :: Property
prop_unionWith_strict =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
    not (IntervalSet.null (IMS.keysSet a `IntervalSet.intersection` IMS.keysSet b))
    ==>
    isBottom (IMS.unionWith (\_ _ -> bottom) a b)

{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}

prop_intersection_isSubmapOf :: Property
prop_intersection_isSubmapOf =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \b ->
      IML.isSubmapOf (IML.intersection a b) a

case_intersectionWith :: Assertion
case_intersectionWith = actual @?= expected
  where
    actual, expected :: IntervalMap Rational Integer
    actual = IML.intersectionWith (+) (IML.singleton (0 <=..< 10) 1) (IML.singleton (5 <..<= 5) 1)
    expected = IML.singleton (5 <..< 5) 2

prop_intersectionWith_Lazy_Strict :: Property
prop_intersectionWith_Lazy_Strict =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \(b :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \(f :: Fun (Integer,Integer) Integer) ->
    IML.intersectionWith (curry (apply f)) a b == IMS.intersectionWith (curry (apply f)) a b

prop_intersectionWith_nonstrict :: Property
prop_intersectionWith_nonstrict =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \(b :: IntervalMap Rational Integer) ->
    IML.intersectionWith (\_ _ -> bottom :: Integer) a b `seq` True

prop_intersectionWith_strict :: Property
prop_intersectionWith_strict =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \(b :: IntervalMap Rational Integer) ->
    not (IntervalSet.null (IMS.keysSet a `IntervalSet.intersection` IMS.keysSet b))
    ==>
    isBottom (IMS.intersectionWith (\_ _ -> bottom :: Integer) a b)

{--------------------------------------------------------------------
  Difference
--------------------------------------------------------------------}

prop_difference_isSubmapOf :: Property
prop_difference_isSubmapOf =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \(b :: IntervalMap Rational Integer) ->
      IML.isSubmapOf (a IML.\\ b) a

{--------------------------------------------------------------------
  member / lookup
--------------------------------------------------------------------}

prop_notMember_empty :: Property
prop_notMember_empty =
  forAll arbitrary $ \(r::Rational) ->
    r `IML.notMember` (IML.empty :: IntervalMap Rational Integer)

case_findWithDefault_case1 :: Assertion
case_findWithDefault_case1 = IML.findWithDefault "B" 0 m @?= "A"
  where
    m :: IntervalMap Rational String
    m = IML.singleton (0 <=..<1) "A"

case_findWithDefault_case2 :: Assertion
case_findWithDefault_case2 = IML.findWithDefault "B" 1 m @?= "B"
  where
    m :: IntervalMap Rational String
    m = IML.singleton (0 <=..<1) "A"

{--------------------------------------------------------------------
  isSubsetOf
--------------------------------------------------------------------}

prop_isSubmapOf_reflexive :: Property
prop_isSubmapOf_reflexive =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    a `IML.isSubmapOf` a

prop_isProperSubsetOf_irreflexive :: Property
prop_isProperSubsetOf_irreflexive =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    not (a `IML.isProperSubmapOf` a)

{--------------------------------------------------------------------
  span
--------------------------------------------------------------------}

prop_span :: Property
prop_span =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IML.span a == IntervalSet.span (IML.keysSet a)

{--------------------------------------------------------------------
  map
--------------------------------------------------------------------}

case_mapKeysMonotonic :: Assertion
case_mapKeysMonotonic = IML.mapKeysMonotonic (+1) m1 @?= m2
  where
    m1, m2 :: IntervalMap Rational String
    m1 = IML.fromList [(0 <=..< 1, "A"), (2 <..<= 3, "B")]
    m2 = IML.fromList [(1 <=..< 2, "A"), (3 <..<= 4, "B")]

prop_map_Lazy_Strict :: Property
prop_map_Lazy_Strict =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \(f :: Fun Integer Integer) ->
    IML.map (apply f) m == IMS.map (apply f) m

prop_map_nonstrict :: Property
prop_map_nonstrict =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IML.map (const (bottom :: Integer)) a `seq` True

prop_map_strict :: Property
prop_map_strict =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    not (IMS.null a)
    ==>
    isBottom (IMS.map (const (bottom :: Integer)) a)

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

prop_fromList_toList_id :: Property
prop_fromList_toList_id =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IML.fromList (IML.toList a) == a

prop_toAscList_toDescList :: Property
prop_toAscList_toDescList =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IML.toDescList a == reverse (IML.toAscList a)

case_fromList :: Assertion
case_fromList = actual @?= expected
  where
    actual, expected :: IntervalMap Rational Integer
    actual = IML.fromList [(0 <=..< 10, 1), (5 <..<= 15, 2)]
    expected = IML.fromList [(0 <=..<= 5, 1), (5 <..<= 15, 2)]

case_fromListWith :: Assertion
case_fromListWith = actual @?= expected
  where
    actual, expected :: IntervalMap Rational Integer
    actual = IML.fromListWith (+) [(0 <=..< 10, 1), (5 <..<= 15, 2)]
    expected = IML.fromList [(0 <=..<= 5, 1), (5 <..< 10, 3), (10 <=..<= 15, 2)]

prop_fromList_Lazy_Strict :: Property
prop_fromList_Lazy_Strict =
  forAll arbitrary $ \xs ->
    (IML.fromList xs :: IntervalMap Rational Integer) == IMS.fromList xs

case_fromList_nonstrict :: Assertion
case_fromList_nonstrict = evaluate m >> return ()
  where
    m :: IntervalMap Rational Integer
    m = IML.fromList [(0 <=..< 10, bottom), (5 <..<= 15, bottom)]

case_fromList_strict :: Assertion
case_fromList_strict = isBottom m @?= True
  where
    m :: IntervalMap Rational Integer
    m = IMS.fromList [(0 <=..< 10, bottom), (5 <..<= 15, bottom)]

prop_fromListWith_Lazy_Strict :: Property
prop_fromListWith_Lazy_Strict =
  forAll arbitrary $ \xs ->
    forAll arbitrary $ \f ->
      (IML.fromListWith (curry (apply f)) xs :: IntervalMap Rational Integer) == IMS.fromListWith (curry (apply f))  xs

case_fromListWith_nonstrict :: Assertion
case_fromListWith_nonstrict = evaluate m >> return ()
  where
    m :: IntervalMap Rational Integer
    m = IML.fromListWith (\_ _ -> bottom) [(0 <=..< 10, 1), (5 <..<= 15, 2)]

case_fromListWith_strict :: Assertion
case_fromListWith_strict = isBottom m @?= True
  where
    m :: IntervalMap Rational Integer
    m = IMS.fromListWith (\_ _ -> bottom) [(0 <=..< 10, 1), (5 <..<= 15, 2)]

{--------------------------------------------------------------------
  Filter
--------------------------------------------------------------------}

case_filter :: Assertion
case_filter = actual @?= expected
  where
    m, expected, actual :: IntervalMap Rational Integer
    m =
      IML.fromList
      [ (2  <..<= 10, 1)
      , (10 <..<= 20, 2)
      , (20 <..<= 30, 3)
      , (30 <..<= 40, 4)
      ]
    expected =
      IML.fromList
      [ (10 <..<= 20, 2)
      , (30 <..<= 40, 4)
      ]
    actual = IML.filter even m

prop_split :: Property
prop_split =
  forAll arbitrary $ \(m :: IntervalMap Rational Integer) ->
    forAll arbitrary $ \i ->
      not (Interval.null i)
      ==>
      (case IML.split i m of
         (m1,m2,m3) ->
           and
           [ and [j <! i | j <- IML.keys m1]
           , and [j `Interval.isSubsetOf` i | j <- IML.keys m2]
           , and [i <! j | j <- IML.keys m3]
           ])

case_split_case1 :: Assertion
case_split_case1 =
  IML.split (5 <=..<= 9) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IML.fromList
      [ (2  <..<= 10, "A")
      , (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]
    smaller =
      IML.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IML.fromList
      [ (5 <=..<= 9, "A")
      ]
    larger =
      IML.fromList
      [ (9  <..<= 10, "A")
      , (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]

case_split_case2 :: Assertion
case_split_case2 =
  IML.split (5 <=..< 10) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IML.fromList
      [ (2  <..<= 10, "A")
      , (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]
    smaller =
      IML.fromList
      [ (2 <..< 5, "A")
      ]
    middle =
      IML.fromList
      [ (5 <=..< 10, "A")
      ]
    larger =
      IML.fromList
      [ (10, "A")
      , (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]

case_split_case3 :: Assertion
case_split_case3 =
  IML.split (5 <=..<= 10) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IML.fromList
      [ (2  <..<= 10, "A")
      , (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]
    smaller =
      IML.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IML.fromList
      [ (5 <=..<= 10, "A")
      ]
    larger =
      IML.fromList
      [ (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]

case_split_case4 :: Assertion
case_split_case4 =
  IML.split (5 <=..< 10) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IML.fromList
      [ (2   <..<  10, "A")
      , (10 <=..<= 20, "B")
      , (20  <..<= 30, "C")
      ]
    smaller =
      IML.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IML.fromList
      [ (5 <=..< 10, "A")
      ]
    larger =
      IML.fromList
      [ (10 <=..<= 20, "B")
      , (20  <..<= 30, "C")
      ]

case_split_case5 :: Assertion
case_split_case5 =
  IML.split (5 <=..<= 10) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IML.fromList
      [ (2   <..<  10, "A")
      , (10 <=..<= 20, "B")
      , (20  <..<= 30, "C")
      ]
    smaller =
      IML.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IML.fromList
      [ (5 <=..< 10, "A")
      , (10, "B")
      ]
    larger =
      IML.fromList
      [ (10 <..<= 20, "B")
      , (20 <..<= 30, "C")
      ]

case_split_case6 :: Assertion
case_split_case6 =
  IML.split (5 <=..< 20) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IML.fromList
      [ (2   <..<  10, "A")
      , (10 <=..<= 20, "B")
      , (20  <..<= 30, "C")
      ]
    smaller =
      IML.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IML.fromList
      [ (5  <=..< 10, "A")
      , (10 <=..< 20, "B")
      ]
    larger =
      IML.fromList
      [ (20, "B")
      , (20 <..<= 30, "C")
      ]

case_split_case7 :: Assertion
case_split_case7 =
  IML.split (5 <=..<= 20) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IML.fromList
      [ (2   <..<  10, "A")
      , (10 <=..<= 20, "B")
      , (20  <..<= 30, "C")
      ]
    smaller =
      IML.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IML.fromList
      [ (5  <=..<  10, "A")
      , (10 <=..<= 20, "B")
      ]
    larger =
      IML.fromList
      [ (20 <..<= 30, "C")
      ]

case_split_case8 :: Assertion
case_split_case8 =
  IML.split (5 <=..< 21) m @?= (smaller, middle, larger)
  where
    m :: IntervalMap Rational String
    m =
      IML.fromList
      [ (2   <..<  10, "A")
      , (10 <=..<= 20, "B")
      , (20  <..<= 30, "C")
      ]
    smaller =
      IML.fromList
      [ (2  <..< 5, "A")
      ]
    middle =
      IML.fromList
      [ (5  <=..<  10, "A")
      , (10 <=..<= 20, "B")
      , (20  <..<  21, "C")
      ]
    larger =
      IML.fromList
      [ (21 <=..<= 30, "C")
      ]

{--------------------------------------------------------------------
  Eq
--------------------------------------------------------------------}

prop_Eq_reflexive :: Property
prop_Eq_reflexive =
  forAll arbitrary $ \(i :: IntervalMap Rational Integer) ->
    i == i

{--------------------------------------------------------------------
  Show / Read
--------------------------------------------------------------------}

prop_show_read_invariance :: Property
prop_show_read_invariance =
  forAll arbitrary $ \(i :: IntervalMap Rational Integer) ->
    i == read (show i)

{--------------------------------------------------------------------
  Monoid
--------------------------------------------------------------------}

prop_monoid_assoc :: Property
prop_monoid_assoc =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    a <> (b <> c) == (a <> b) <> c

prop_monoid_unitL :: Property
prop_monoid_unitL =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    IML.empty <> a == a

prop_monoid_unitR :: Property
prop_monoid_unitR =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    a <> IML.empty == a

{--------------------------------------------------------------------
  NFData
--------------------------------------------------------------------}

prop_rnf :: Property
prop_rnf =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    rnf a == ()

{--------------------------------------------------------------------
  Hashable
--------------------------------------------------------------------}

prop_hash :: Property
prop_hash =
  forAll arbitrary $ \(a :: IntervalMap Rational Integer) ->
    hash a `seq` True

{- ------------------------------------------------------------------
  Data
------------------------------------------------------------------ -}

case_Data :: Assertion
case_Data = everywhere f i @?= (IML.singleton (1 <=..<= 2) 3 :: IntervalMap Integer Integer)
  where
    i :: IntervalMap Integer Integer
    i = IML.singleton (0 <=..<= 1) 2
    f x
      | Just (y :: Integer) <- cast x = fromJust $ cast (y + 1)
      | otherwise = x

{--------------------------------------------------------------------
  Generators
--------------------------------------------------------------------}

instance Arbitrary Interval.Boundary where
  arbitrary = arbitraryBoundedEnum

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
  arbitrary = IML.fromList <$> listOf arbitrary

------------------------------------------------------------------------
-- Test harness

intervalMapTestGroup :: TestTree
intervalMapTestGroup = $(testGroupGenerator)
