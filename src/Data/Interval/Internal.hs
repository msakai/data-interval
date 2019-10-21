{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, DeriveDataTypeable, DeriveGeneric, LambdaCase #-}
{-# LANGUAGE Safe #-}
#if __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE RoleAnnotations #-}
#endif

module Data.Interval.Internal
  ( Boundary(..)
  , Interval
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

-- | Boundary of an interval may be
-- open (excluding an endpoint) or closed (including an endpoint).
--
-- @since 2.0.0
data Boundary
  = Open
  | Closed
  deriving (Eq, Ord, Enum, Bounded, Show, Read, Generic, Data, Typeable)

instance NFData Boundary

instance Hashable Boundary

data Interval r
  = Whole
  | Empty
  | Point !r
  | LessThan !r
  | LessOrEqual !r
  | GreaterThan !r
  | GreaterOrEqual !r
  | BothClosed !r !r
  | LeftOpen !r !r
  | RightOpen !r !r
  | BothOpen !r !r
  deriving (Eq, Generic, Typeable)

lowerBound' :: Interval r -> (Extended r, Boundary)
lowerBound' = \case
  Whole            -> (NegInf,   Open)
  Empty            -> (PosInf,   Open)
  Point r          -> (Finite r, Closed)
  LessThan{}       -> (NegInf,   Open)
  LessOrEqual{}    -> (NegInf,   Open)
  GreaterThan r    -> (Finite r, Open)
  GreaterOrEqual r -> (Finite r, Closed)
  BothClosed p _   -> (Finite p, Closed)
  LeftOpen p _     -> (Finite p, Open)
  RightOpen p _    -> (Finite p, Closed)
  BothOpen p _     -> (Finite p, Open)

upperBound' :: Interval r -> (Extended r, Boundary)
upperBound' = \case
  Whole            -> (PosInf,   Open)
  Empty            -> (NegInf,   Open)
  Point r          -> (Finite r, Closed)
  LessThan r       -> (Finite r, Open)
  LessOrEqual r    -> (Finite r, Closed)
  GreaterThan{}    -> (PosInf,   Open)
  GreaterOrEqual{} -> (PosInf,   Open)
  BothClosed _ q   -> (Finite q, Closed)
  LeftOpen _ q     -> (Finite q, Closed)
  RightOpen _ q    -> (Finite q, Open)
  BothOpen _ q     -> (Finite q, Open)

#if __GLASGOW_HASKELL__ >= 708
type role Interval nominal
#endif

instance (Ord r, Data r) => Data (Interval r) where
  gfoldl k z x   = z interval `k` lowerBound' x `k` upperBound' x
  toConstr _     = intervalConstr
  gunfold k z c  = case constrIndex c of
    1 -> k (k (z interval))
    _ -> error "gunfold"
  dataTypeOf _   = intervalDataType
  dataCast1 f    = gcast1 f

intervalConstr :: Constr
intervalConstr = mkConstr intervalDataType "interval" [] Prefix

intervalDataType :: DataType
intervalDataType = mkDataType "Data.Interval.Internal.Interval" [intervalConstr]

instance NFData r => NFData (Interval r)

instance Hashable r => Hashable (Interval r)

-- | empty (contradicting) interval
empty :: Ord r => Interval r
empty = Empty

-- | smart constructor for 'Interval'
interval
  :: (Ord r)
  => (Extended r, Boundary) -- ^ lower bound and whether it is included
  -> (Extended r, Boundary) -- ^ upper bound and whether it is included
  -> Interval r
interval = \case
  (NegInf, _) -> \case
    (NegInf, _) -> Empty
    (Finite r, Open) -> LessThan r
    (Finite r, Closed) -> LessOrEqual r
    (PosInf, _) -> Whole
  (Finite p, Open) -> \case
    (NegInf, _) -> Empty
    (Finite q, Open)
      | p < q -> BothOpen p q
      | otherwise -> Empty
    (Finite q, Closed)
      | p < q -> LeftOpen p q
      | otherwise -> Empty
    (PosInf, _) -> GreaterThan p
  (Finite p, Closed) -> \case
    (NegInf, _) -> Empty
    (Finite q, Open)
      | p < q -> RightOpen p q
      | otherwise -> Empty
    (Finite q, Closed) -> case p `compare` q of
      LT -> BothClosed p q
      EQ -> Point p
      GT -> Empty
    (PosInf, _) -> GreaterOrEqual p
  (PosInf, _) -> const Empty
{-# INLINE interval #-}
