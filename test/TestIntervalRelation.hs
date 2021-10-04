{-# LANGUAGE ScopedTypeVariables, TemplateHaskell #-}
module TestIntervalRelation (intervalRelationTestGroup) where

import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.Tasty.TH

import Data.Interval as I
import Data.IntervalRelation
import Data.Ord (Down(..))

import TestInstances

{--------------------------------------------------------------------
  invert
--------------------------------------------------------------------}

prop_invert_is_involution a =
  invert (invert a) === a

prop_invert_inverts_relation =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    relate a b === invert (relate b a)

------------------------------------------------------------------------

case_empty1 =
  relate (empty :: Interval Rational) empty @?= Equal

prop_empty2 =
  forAllShrink intervals shrink $ \a -> not (I.null a) ==>
  relate (empty :: Interval Rational) a === During

prop_empty3 =
  forAllShrink intervals shrink $ \a -> not (I.null a) ==>
  relate a (empty :: Interval Rational) === Contains

prop_universal_lt =
  forAllShrink intervals shrink $ \a -> not (I.null a) ==>
  forAllShrink intervals shrink $ \b -> not (I.null b) ==>
    let r = relate a b in counterexample (show r) $
    if a <! b then r `elem`    [Before, JustBefore]
              else r `notElem` [Before, JustBefore]

prop_universal_le =
  forAllShrink intervals shrink $ \a -> not (I.null a) ==>
  forAllShrink intervals shrink $ \b -> not (I.null b) ==>
    let r = relate a b in counterexample (show r) $
    if a <=! b then r `elem`    [Before, JustBefore, Overlaps, Starts, Equal, FinishedBy]
               else r `notElem` [Before, JustBefore]

prop_universal_eq =
  forAllShrink intervals shrink $ \a -> not (I.null a) ==>
  forAllShrink intervals shrink $ \b -> not (I.null b) ==>
    not (a ==! b) || relate a b == Equal

prop_universal_gt =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    (a >! b) === (b <! a)

prop_universal_ge =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    (a >=! b) === (b <=! a)

prop_universal_ne =
  forAllShrink intervals shrink $ \a -> not (I.null a) ==>
  forAllShrink intervals shrink $ \b -> not (I.null b) ==>
    let r = relate a b in counterexample (show r) $
    if a /=! b then r `elem`    [Before, JustBefore, After, JustAfter]
               else r `notElem` [Before, JustBefore, After, JustAfter]

------------------------------------------------------------------------

prop_existential_lt =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    (a <? b) === not (a >=! b)

prop_existential_le =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    (a <=? b) === not (a >! b)

prop_existential_eq =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    (a ==? b) === not (a /=! b)

prop_existential_gt =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    (a >? b) === not (a <=! b)

prop_existential_ge =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    (a >=? b) === not (a <! b)

prop_existential_ne =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    (a /=? b) === not (a ==! b)

------------------------------------------------------------------------

prop_before =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    let r = relate a b in counterexample (show r) $
    (r == Before) === (a <! b && not (isConnected a b))

prop_just_before =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    let r = relate a b in counterexample (show r) $
    (r == JustBefore) === (a <! b && isConnected a b && not (I.null a) && not (I.null b))

prop_overlaps =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    let r = relate a b in counterexample (show r) $
    (r == Overlaps) === (not (I.null (intersection a b)) && fmap Down (lowerBound' a) < fmap Down (lowerBound' b) && upperBound' a < upperBound' b)

prop_starts =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    let r = relate a b in counterexample (show r) $
    (r == Starts) === (isProperSubsetOf a b && lowerBound' a == lowerBound' b)

prop_during =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    let r = relate a b in counterexample (show r) $
    (r == During) === (isProperSubsetOf a b && lowerBound' a /= lowerBound' b && upperBound' a /= upperBound' b)

prop_finishes =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    let r = relate a b in counterexample (show r) $
    (r == Finishes) === (isProperSubsetOf a b && upperBound' a == upperBound' b)

prop_equal =
  forAllShrink intervals shrink $ \a ->
  forAllShrink intervals shrink $ \b ->
    let r = relate a b in counterexample (show r) $
    (r == Equal) === (a == b)

------------------------------------------------------------------------
-- Test harness

intervalRelationTestGroup = $(testGroupGenerator)
