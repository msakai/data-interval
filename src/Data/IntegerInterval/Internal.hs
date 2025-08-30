{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE RoleAnnotations #-}

module Data.IntegerInterval.Internal
  ( IntegerInterval
  , lowerBound
  , upperBound
  , (<=..<=)
  , empty
  ) where

import Control.DeepSeq
import Data.Data
import Data.ExtendedReal
import Data.Hashable

infix 5 <=..<=

-- | The intervals (/i.e./ connected and convex subsets) over integers (__Z__).
data IntegerInterval
  = Whole
  | Empty
  | Point !Integer
  | LessOrEqual !Integer
  | GreaterOrEqual !Integer
  | BothClosed !Integer !Integer
  deriving (Eq)

-- | Lower endpoint (/i.e./ greatest lower bound)  of the interval.
--
-- * 'lowerBound' of the empty interval is 'PosInf'.
--
-- * 'lowerBound' of a left unbounded interval is 'NegInf'.
--
-- * 'lowerBound' of an interval may or may not be a member of the interval.
lowerBound :: IntegerInterval -> Extended Integer
lowerBound = \case
  Whole            -> NegInf
  Empty            -> PosInf
  Point r          -> Finite r
  LessOrEqual _    -> NegInf
  GreaterOrEqual r -> Finite r
  BothClosed p _   -> Finite p

-- | Upper endpoint (/i.e./ least upper bound) of the interval.
--
-- * 'upperBound' of the empty interval is 'NegInf'.
--
-- * 'upperBound' of a right unbounded interval is 'PosInf'.
--
-- * 'upperBound' of an interval is a member of the interval.
upperBound :: IntegerInterval -> Extended Integer
upperBound = \case
  Whole            -> PosInf
  Empty            -> NegInf
  Point r          -> Finite r
  LessOrEqual r    -> Finite r
  GreaterOrEqual _ -> PosInf
  BothClosed _ p   -> Finite p

-- This instance preserves data abstraction at the cost of inefficiency.
-- We provide limited reflection services for the sake of data abstraction.

instance Data IntegerInterval where
  gfoldl k z x   = z (<=..<=) `k` lowerBound x `k` upperBound x
  toConstr _     = intervalConstr
  gunfold k z c  = case constrIndex c of
    1 -> k (k (z (<=..<=)))
    _ -> error "gunfold"
  dataTypeOf _   = intervalDataType

intervalConstr :: Constr
intervalConstr = mkConstr intervalDataType "<=..<=" [] Infix

intervalDataType :: DataType
intervalDataType = mkDataType "Data.IntegerInterval.Internal.IntegerInterval" [intervalConstr]

instance NFData IntegerInterval where
  rnf = \case
    Whole            -> ()
    Empty            -> ()
    Point r          -> rnf r
    LessOrEqual r    -> rnf r
    GreaterOrEqual r -> rnf r
    BothClosed p q   -> rnf p `seq` rnf q

instance Hashable IntegerInterval where
  hashWithSalt s = \case
    Whole            -> s `hashWithSalt`  (1 :: Int)
    Empty            -> s `hashWithSalt`  (2 :: Int)
    Point r          -> s `hashWithSalt`  (3 :: Int) `hashWithSalt` r
    LessOrEqual r    -> s `hashWithSalt`  (4 :: Int) `hashWithSalt` r
    GreaterOrEqual r -> s `hashWithSalt`  (5 :: Int) `hashWithSalt` r
    BothClosed p q   -> s `hashWithSalt`  (6 :: Int) `hashWithSalt` p `hashWithSalt` q

-- | closed interval [@l@,@u@]
(<=..<=)
  :: Extended Integer -- ^ lower bound @l@
  -> Extended Integer -- ^ upper bound @u@
  -> IntegerInterval
(<=..<=) PosInf _ = empty
(<=..<=) _ NegInf = empty
(<=..<=) NegInf PosInf = Whole
(<=..<=) NegInf (Finite ub) = LessOrEqual ub
(<=..<=) (Finite lb) PosInf = GreaterOrEqual lb
(<=..<=) (Finite lb) (Finite ub) =
  case compare lb ub of
    EQ -> Point lb
    LT -> BothClosed lb ub
    GT -> Empty
{-# INLINE (<=..<=) #-}

-- | empty (contradicting) interval
empty :: IntegerInterval
empty = Empty
