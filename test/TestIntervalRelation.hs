{-# LANGUAGE ScopedTypeVariables, TemplateHaskell #-}
module TestIntervalRelation (intervalRelationTestGroup) where

import Test.Tasty.QuickCheck
import Test.Tasty.TH

import Data.Interval
import Data.IntervalRelation

import TestInstances

{--------------------------------------------------------------------
  invert
--------------------------------------------------------------------}

prop_invert_is_involution a =
  invert (invert a) == a

prop_invert_inverts_relation =
  forAll intervals $ \a ->
  forAll intervals $ \b ->
    relate a b == invert (relate b a)

------------------------------------------------------------------------
-- Test harness

intervalRelationTestGroup = $(testGroupGenerator)
