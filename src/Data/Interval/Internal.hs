{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, LambdaCase, ScopedTypeVariables #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE RoleAnnotations #-}

module Data.Interval.Internal
  ( Boundary(..)
  , Interval(..)
  , lowerBound'
  , upperBound'
  , interval
  , empty
  ) where

import Control.DeepSeq
import Data.Data
import Data.ExtendedReal
import Data.Hashable
import Data.Int
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable
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

-- | The intervals (/i.e./ connected and convex subsets) over a type @r@.
data Interval r
  = Whole
  | Empty
  | Point !r
  | LessThan !r
  | LessOrEqual !r
  | GreaterThan !r
  | GreaterOrEqual !r
  -- For constructors below
  -- the first argument is strictly less than the second one
  | BothClosed !r !r
  | LeftOpen !r !r
  | RightOpen !r !r
  | BothOpen !r !r
  deriving
    ( Eq
    , Ord
      -- ^ Note that this Ord is derived and not semantically meaningful.
      -- The primary intended use case is to allow using 'Interval'
      -- in maps and sets that require ordering.
    , Typeable
    )

peekInterval :: (Applicative m, Monad m, Ord r) => m Int8 -> m r -> m r -> m (Interval r)
peekInterval tagM x y = do
  tag <- tagM
  case tag of
    0 -> pure Whole
    1 -> pure Empty
    2 -> Point           <$> x
    3 -> LessThan        <$> x
    4 -> LessOrEqual     <$> x
    5 -> GreaterThan     <$> x
    6 -> GreaterOrEqual  <$> x
    7 -> wrap BothClosed <$> x <*> y
    8 -> wrap LeftOpen   <$> x <*> y
    9 -> wrap RightOpen  <$> x <*> y
    _ -> wrap BothOpen   <$> x <*> y

-- | Enforce the internal invariant
-- of 'BothClosed' / 'LeftOpen' / 'RightOpen' / 'BothOpen'.
wrap :: Ord r => (r -> r -> Interval r) -> r -> r -> Interval r
wrap f x y
  | x < y = f x y
  | otherwise = Empty

pokeInterval :: Applicative m => (Int8 -> m ()) -> (r -> m ()) -> (r -> m ()) -> Interval r -> m ()
pokeInterval tag actX actY = \case
  Whole            -> tag (0 :: Int8)
  Empty            -> tag (1 :: Int8)
  Point          x -> tag (2 :: Int8) *> actX x
  LessThan       x -> tag (3 :: Int8) *> actX x
  LessOrEqual    x -> tag (4 :: Int8) *> actX x
  GreaterThan    x -> tag (5 :: Int8) *> actX x
  GreaterOrEqual x -> tag (6 :: Int8) *> actX x
  BothClosed   x y -> tag (7 :: Int8) *> actX x *> actY y
  LeftOpen     x y -> tag (8 :: Int8) *> actX x *> actY y
  RightOpen    x y -> tag (9 :: Int8) *> actX x *> actY y
  BothOpen     x y -> tag (10 :: Int8) *> actX x *> actY y

instance (Storable r, Ord r) => Storable (Interval r) where
  sizeOf _ = 3 * sizeOf (undefined :: r)
  alignment _ = alignment (undefined :: r)
  peek ptr = peekInterval
    (peek $ castPtr ptr)
    (peek $ castPtr ptr `advancePtr` 1)
    (peek $ castPtr ptr `advancePtr` 2)
  poke ptr = pokeInterval
    (poke $ castPtr ptr)
    (poke $ castPtr ptr `advancePtr` 1)
    (poke $ castPtr ptr `advancePtr` 2)

-- | Lower endpoint (/i.e./ greatest lower bound) of the interval,
-- together with 'Boundary' information.
-- The result is convenient to use as an argument for 'interval'.
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

-- | Upper endpoint (/i.e./ least upper bound) of the interval,
-- together with 'Boundary' information.
-- The result is convenient to use as an argument for 'interval'.
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

type role Interval nominal

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
    BothClosed p q   -> rnf p `seq` rnf q
    LeftOpen p q     -> rnf p `seq` rnf q
    RightOpen p q    -> rnf p `seq` rnf q
    BothOpen p q     -> rnf p `seq` rnf q

instance Hashable r => Hashable (Interval r) where
  hashWithSalt s = \case
    Whole            -> s `hashWithSalt`  (1 :: Int)
    Empty            -> s `hashWithSalt`  (2 :: Int)
    Point r          -> s `hashWithSalt`  (3 :: Int) `hashWithSalt` r
    LessThan r       -> s `hashWithSalt`  (4 :: Int) `hashWithSalt` r
    LessOrEqual r    -> s `hashWithSalt`  (5 :: Int) `hashWithSalt` r
    GreaterThan r    -> s `hashWithSalt`  (6 :: Int) `hashWithSalt` r
    GreaterOrEqual r -> s `hashWithSalt`  (7 :: Int) `hashWithSalt` r
    BothClosed p q   -> s `hashWithSalt`  (8 :: Int) `hashWithSalt` p `hashWithSalt` q
    LeftOpen p q     -> s `hashWithSalt`  (9 :: Int) `hashWithSalt` p `hashWithSalt` q
    RightOpen p q    -> s `hashWithSalt` (10 :: Int) `hashWithSalt` p `hashWithSalt` q
    BothOpen p q     -> s `hashWithSalt` (11 :: Int) `hashWithSalt` p `hashWithSalt` q

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
