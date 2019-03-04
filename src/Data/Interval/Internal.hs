{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, DeriveDataTypeable, DeriveGeneric #-}
{-# LANGUAGE Safe #-}
#if __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE RoleAnnotations #-}
#endif

module Data.Interval.Internal
  ( Interval
  , lowerBound'
  , upperBound'
  , interval
  , empty
  ) where

import Control.DeepSeq
import Data.Data
import Data.ExtendedReal
import Data.Hashable
import GHC.Generics (Generic)

-- | The intervals (/i.e./ connected and convex subsets) over real numbers __R__.
data Interval r = Interval
  { -- | 'lowerBound' of the interval and whether it is included in the interval.
    -- The result is convenient to use as an argument for 'interval'.
    lowerBound' :: !(Extended r, Bool)
  , -- | 'upperBound' of the interval and whether it is included in the interval.
    -- The result is convenient to use as an argument for 'interval'.
    upperBound' :: !(Extended r, Bool)
  } deriving (Eq, Generic, Data, Typeable)

#if __GLASGOW_HASKELL__ >= 708
type role Interval nominal
#endif

instance NFData r => NFData (Interval r)

instance Hashable r => Hashable (Interval r)

-- | empty (contradicting) interval
empty :: Ord r => Interval r
empty = Interval (PosInf, False) (NegInf, False)

-- | smart constructor for 'Interval'
interval
  :: (Ord r)
  => (Extended r, Bool) -- ^ lower bound and whether it is included
  -> (Extended r, Bool) -- ^ upper bound and whether it is included
  -> Interval r
interval lb@(x1,in1) ub@(x2,in2) =
  case x1 `compare` x2 of
    GT -> empty --  empty interval
    LT -> Interval (normalize lb) (normalize ub)
    EQ -> if in1 && in2 && isFinite x1 then Interval lb ub else empty
  where
    normalize x@(Finite _, _) = x
    normalize (x, _) = (x, False)

