{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, DeriveDataTypeable, LambdaCase #-}
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

data Interval r
  = Whole
  | Empty
  | Point !r
  | LessThan !r
  | LessOrEqual !r
  | GreaterThan !r
  | GreaterOrEqual !r
  | Closed !r !r
  | LeftOpen !r !r
  | RightOpen !r !r
  | Open !r !r
  deriving (Eq, Typeable)

lowerBound' :: Interval r -> (Extended r, Bool)
lowerBound' = \case
  Whole            -> (NegInf,   False)
  Empty            -> (PosInf,   False)
  Point r          -> (Finite r, True)
  LessThan{}       -> (NegInf,   False)
  LessOrEqual{}    -> (NegInf,   False)
  GreaterThan r    -> (Finite r, False)
  GreaterOrEqual r -> (Finite r, True)
  Closed p _       -> (Finite p, True)
  LeftOpen p _     -> (Finite p, False)
  RightOpen p _    -> (Finite p, True)
  Open p _         -> (Finite p, False)

upperBound' :: Interval r -> (Extended r, Bool)
upperBound' = \case
  Whole            -> (PosInf,   False)
  Empty            -> (NegInf,   False)
  Point r          -> (Finite r, True)
  LessThan r       -> (Finite r, False)
  LessOrEqual r    -> (Finite r, True)
  GreaterThan{}    -> (PosInf,   False)
  GreaterOrEqual{} -> (PosInf,   False)
  Closed _ q       -> (Finite q, True)
  LeftOpen _ q     -> (Finite q, True)
  RightOpen _ q    -> (Finite q, False)
  Open _ q         -> (Finite q, False)

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

instance NFData r => NFData (Interval r) where
  rnf = \case
    Whole            -> ()
    Empty            -> ()
    Point r          -> rnf r
    LessThan r       -> rnf r
    LessOrEqual r    -> rnf r
    GreaterThan r    -> rnf r
    GreaterOrEqual r -> rnf r
    Closed p q       -> rnf p `seq` rnf q
    LeftOpen p q     -> rnf p `seq` rnf q
    RightOpen p q    -> rnf p `seq` rnf q
    Open p q         -> rnf p `seq` rnf q

instance Hashable r => Hashable (Interval r) where
  hashWithSalt s = \case
    Whole            -> s `hashWithSalt`  (1 :: Int)
    Empty            -> s `hashWithSalt`  (2 :: Int)
    Point r          -> s `hashWithSalt`  (3 :: Int) `hashWithSalt` r
    LessThan r       -> s `hashWithSalt`  (4 :: Int) `hashWithSalt` r
    LessOrEqual r    -> s `hashWithSalt`  (5 :: Int) `hashWithSalt` r
    GreaterThan r    -> s `hashWithSalt`  (6 :: Int) `hashWithSalt` r
    GreaterOrEqual r -> s `hashWithSalt`  (7 :: Int) `hashWithSalt` r
    Closed p q       -> s `hashWithSalt`  (8 :: Int) `hashWithSalt` p `hashWithSalt` q
    LeftOpen p q     -> s `hashWithSalt`  (9 :: Int) `hashWithSalt` p `hashWithSalt` q
    RightOpen p q    -> s `hashWithSalt` (10 :: Int) `hashWithSalt` p `hashWithSalt` q
    Open p q         -> s `hashWithSalt` (11 :: Int) `hashWithSalt` p `hashWithSalt` q

-- | empty (contradicting) interval
empty :: Ord r => Interval r
empty = Empty

-- | smart constructor for 'Interval'
interval
  :: (Ord r)
  => (Extended r, Bool) -- ^ lower bound and whether it is included
  -> (Extended r, Bool) -- ^ upper bound and whether it is included
  -> Interval r
interval = \case
  (NegInf, _) -> \case
    (NegInf, _) -> Empty
    (Finite r, False) -> LessThan r
    (Finite r, True) -> LessOrEqual r
    (PosInf, _) -> Whole
  (Finite p, False) -> \case
    (NegInf, _) -> Empty
    (Finite q, False)
      | p < q -> Open p q
      | otherwise -> Empty
    (Finite q, True)
      | p < q -> LeftOpen p q
      | otherwise -> Empty
    (PosInf, _) -> GreaterThan p
  (Finite p, True) -> \case
    (NegInf, _) -> Empty
    (Finite q, False)
      | p < q -> RightOpen p q
      | otherwise -> Empty
    (Finite q, True) -> case p `compare` q of
      LT -> Closed p q
      EQ -> Point p
      GT -> Empty
    (PosInf, _) -> GreaterOrEqual p
  (PosInf, _) -> const Empty
{-# INLINE interval #-}
