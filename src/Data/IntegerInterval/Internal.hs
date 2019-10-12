{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, DeriveDataTypeable, DeriveGeneric, LambdaCase #-}
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
import GHC.Generics (Generic)

infix 5 <=..<=

-- | The intervals (/i.e./ connected and convex subsets) over integers (__Z__).
data IntegerInterval
  = Whole
  | Empty
  | Point !Integer
  | LessOrEqual !Integer
  | GreaterOrEqual !Integer
  | Closed !Integer !Integer
  deriving (Eq, Generic, Typeable)

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
  Closed p _       -> Finite p

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
  Closed _ p       -> Finite p  

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

instance NFData IntegerInterval

instance Hashable IntegerInterval

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
    LT -> Closed lb ub
    GT -> Empty
{-# INLINE (<=..<=) #-}

-- | empty (contradicting) interval
empty :: IntegerInterval
empty = Empty
