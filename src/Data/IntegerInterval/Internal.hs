{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, DeriveDataTypeable #-}
{-# LANGUAGE Safe #-}
#if __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE RoleAnnotations #-}
#endif

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
data IntegerInterval = Interval !(Extended Integer) !(Extended Integer)
  deriving (Eq, Typeable)

-- | Lower endpoint (/i.e./ greatest lower bound)  of the interval.
--
-- * 'lowerBound' of the empty interval is 'PosInf'.
--
-- * 'lowerBound' of a left unbounded interval is 'NegInf'.
--
-- * 'lowerBound' of an interval may or may not be a member of the interval.
lowerBound :: IntegerInterval -> Extended Integer
lowerBound (Interval lb _) = lb

-- | Upper endpoint (/i.e./ least upper bound) of the interval.
--
-- * 'upperBound' of the empty interval is 'NegInf'.
--
-- * 'upperBound' of a right unbounded interval is 'PosInf'.
--
-- * 'upperBound' of an interval is a member of the interval.
upperBound :: IntegerInterval -> Extended Integer
upperBound (Interval _ ub) = ub

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
  rnf (Interval lb ub) = rnf lb `seq` rnf ub

instance Hashable IntegerInterval where
  hashWithSalt s (Interval lb ub) = s `hashWithSalt` lb `hashWithSalt` ub

-- | closed interval [@l@,@u@]
(<=..<=)
  :: Extended Integer -- ^ lower bound @l@
  -> Extended Integer -- ^ upper bound @u@
  -> IntegerInterval
(<=..<=) PosInf _ = empty
(<=..<=) _ NegInf = empty
(<=..<=) lb ub
  | lb <= ub  = Interval lb ub
  | otherwise = empty

-- | empty (contradicting) interval
empty :: IntegerInterval
empty = Interval PosInf NegInf
