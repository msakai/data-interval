{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, LambdaCase, ScopedTypeVariables #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE RoleAnnotations #-}

module Data.Interval.Internal
  ( Boundary(..)
  , Interval
  , lowerBound'
  , upperBound'
  , interval
  , fromUnorderedBounds
  , empty
  , restrictMapKeysToInterval
  , withoutMapKeysFromInterval
  , intersectionSetAndInterval
  , differenceSetAndInterval
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
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

-- | Boundary of an interval may be
-- open (excluding an endpoint) or closed (including an endpoint).
--
-- @since 2.0.0
data Boundary
  = Open
  | Closed
  deriving (Eq, Ord, Enum, Bounded, Show, Read, Generic, Data)

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

-- | Same as 'interval' but swaps the lower and upper bounds when given in
-- reverse order.
fromUnorderedBounds
  :: (Ord r)
  => (Extended r, Boundary) -- ^ lower or upper bound and whether it is included
  -> (Extended r, Boundary) -- ^ upper or upper bound and whether it is included
  -> Interval r
fromUnorderedBounds = \case
  (NegInf, _) -> \case
    (NegInf, _) -> Empty
    (Finite r, Open) -> LessThan r
    (Finite r, Closed) -> LessOrEqual r
    (PosInf, _) -> Whole
  (Finite p, Open) -> \case
    (NegInf, _) -> LessThan p
    (Finite q, Open) -> case p `compare` q of
      LT -> BothOpen p q
      GT -> BothOpen q p
      EQ -> Empty
    (Finite q, Closed) -> case p `compare` q of
      LT -> LeftOpen p q
      GT -> RightOpen q p
      EQ -> Empty
    (PosInf, _) -> GreaterThan p
  (Finite p, Closed) -> \case
    (NegInf, _) -> LessOrEqual p
    (Finite q, Open) -> case p `compare` q of
      LT -> RightOpen p q
      GT -> LeftOpen q p
      EQ -> Empty
    (Finite q, Closed) -> case p `compare` q of
      LT -> BothClosed p q
      EQ -> Point p
      GT -> BothClosed q p
    (PosInf, _) -> GreaterOrEqual p
  (PosInf, _) -> \case
    (NegInf, _) -> Whole
    (Finite r, Open) -> GreaterThan r
    (Finite r, Closed) -> GreaterOrEqual r
    (PosInf, _) -> Empty
{-# INLINE fromUnorderedBounds #-}

------------------------------------------------------------------------------

-- | \(O(\log n)\). Restrict a 'Map' to the keys contained in a given
-- 'Interval'.
--
-- >>> restrictMapKeysToInterval m i == filterKeys (\k -> Interval.member k i) m
--
-- [Usage:]
--
-- >>> m = Map.fromList [(-2.5,0),(3.1,1),(5,2), (8.5,3)] :: Map Rational Int
-- >>> restrictMapKeysToInterval m (3 <=..< 8.5)
-- fromList [(31 % 10,1),(5 % 1,2)]
--
-- [Performance:]
-- This outperforms 'filterKeys' which is \(O(n)\).
--
restrictMapKeysToInterval :: Ord k => Map k a -> Interval k -> Map k a
restrictMapKeysToInterval m = \case
  Whole -> m
  Empty -> Map.empty
  Point k -> maybe Map.empty (Map.singleton k) (Map.lookup k m)
  LessThan k -> Map.takeWhileAntitone (< k) m
  LessOrEqual k -> Map.takeWhileAntitone (<= k) m
  GreaterThan k -> Map.dropWhileAntitone (<= k) m
  GreaterOrEqual k -> Map.dropWhileAntitone (< k) m
  BothClosed lk uk ->
    Map.takeWhileAntitone (<= uk) $ Map.dropWhileAntitone (< lk) m
  LeftOpen lk uk ->
    Map.takeWhileAntitone (<= uk) $ Map.dropWhileAntitone (<= lk) m
  RightOpen lk uk ->
    Map.takeWhileAntitone (< uk) $ Map.dropWhileAntitone (< lk) m
  BothOpen lk uk ->
    Map.takeWhileAntitone (< uk) $ Map.dropWhileAntitone (<= lk) m
{-# INLINE restrictMapKeysToInterval #-}

-- | \(O(n)\). Delete keys contained in a given 'Interval' from a 'Map'.
--
-- >>> withoutMapKeysFromInterval i m == filterKeys (\k -> Interval.notMember k i) m
--
-- [Usage:]
--
-- >>> m = Map.fromList [(-2.5,0),(3.1,1),(5,2), (8.5,3)] :: Map Rational Int
-- >>> withoutMapKeysFromInterval (3 <=..< 8.5) m
-- fromList [((-5) % 2,0),(17 % 2,3)]
--
-- [Performance:] In practice, this outperforms 'filterKeys'.
--
withoutMapKeysFromInterval :: Ord k => Interval k -> Map k a -> Map k a
withoutMapKeysFromInterval i m = case i of
  Whole -> Map.empty
  Empty -> m
  Point k -> Map.delete k m
  LessThan k -> restrictMapKeysToInterval m (GreaterOrEqual k)
  LessOrEqual k -> restrictMapKeysToInterval m (GreaterThan k)
  GreaterThan k -> restrictMapKeysToInterval m (LessOrEqual k)
  GreaterOrEqual k -> restrictMapKeysToInterval m (LessThan k)
  BothClosed lk uk -> let (lt,_,gt) = Map.splitLookup uk m in
    restrictMapKeysToInterval lt (LessThan lk) `Map.union` gt
  LeftOpen lk uk -> let (lt,_,gt) = Map.splitLookup uk m in
    restrictMapKeysToInterval lt (LessOrEqual lk) `Map.union` gt
  RightOpen lk uk -> let (lt,_,gt) = Map.splitLookup lk m in
    lt `Map.union` restrictMapKeysToInterval gt (GreaterOrEqual uk)
  BothOpen lk uk ->
    restrictMapKeysToInterval m (LessOrEqual lk)
    `Map.union` restrictMapKeysToInterval m (GreaterOrEqual uk)
{-# INLINE withoutMapKeysFromInterval #-}

------------------------------------------------------------------------------

-- | \(O(\log n)\). Restrict a 'Set' to the keys contained in a given
-- 'Interval'.
--
-- >>> intersectionSetAndInterval s i == Set.filter (\k -> Interval.member k i) s
--
-- [Usage:]
--
-- >>> s = Set.fromList [-2.5, 3.1, 5 , 8.5] :: Set Rational
-- >>> intersectionSetAndInterval s (3 <=..< 8.5)
-- fromList [31 % 10,5 % 1]
--
-- [Performance:] This outperforms 'Set.filter' which is \(O(n)\).
--
intersectionSetAndInterval :: Ord k => Set k -> Interval k -> Set k
intersectionSetAndInterval s = \case
  Whole -> s
  Empty -> Set.empty
  Point k -> if Set.member k s then Set.singleton k else Set.empty
  LessThan k -> Set.takeWhileAntitone (< k) s
  LessOrEqual k -> Set.takeWhileAntitone (<= k) s
  GreaterThan k -> Set.dropWhileAntitone (<= k) s
  GreaterOrEqual k -> Set.dropWhileAntitone (< k) s
  BothClosed lk uk ->
    Set.takeWhileAntitone (<= uk) $ Set.dropWhileAntitone (< lk) s
  LeftOpen lk uk ->
    Set.takeWhileAntitone (<= uk) $ Set.dropWhileAntitone (<= lk) s
  RightOpen lk uk ->
    Set.takeWhileAntitone (< uk) $ Set.dropWhileAntitone (< lk) s
  BothOpen lk uk ->
    Set.takeWhileAntitone (< uk) $ Set.dropWhileAntitone (<= lk) s
{-# INLINE intersectionSetAndInterval #-}

-- | \(O(n)\). Delete keys contained in a given 'Interval' from a 'Set'.
--
-- >>> differenceSetAndInterval i s == Set.filter (\k -> Interval.notMember k i) s
--
-- [Usage:]
--
-- >>> s = Set.fromList [-2.5, 3.1, 5 , 8.5] :: Set Rational
-- >>> differenceSetAndInterval s (3 <=..< 8.5)
-- fromList [(-5) % 2,17 % 2]
--
-- [Performance:] In practice, this outperforms 'Set.filter'.
--
differenceSetAndInterval :: Ord k => Set k -> Interval k -> Set k
differenceSetAndInterval s i = case i of
  Whole -> Set.empty
  Empty -> s
  Point k -> Set.delete k s
  LessThan k -> intersectionSetAndInterval s (GreaterOrEqual k)
  LessOrEqual k -> intersectionSetAndInterval s (GreaterThan k)
  GreaterThan k -> intersectionSetAndInterval s (LessOrEqual k)
  GreaterOrEqual k -> intersectionSetAndInterval s (LessThan k)
  BothClosed lk uk -> let (lt,_,gt) = Set.splitMember uk s in
    Set.takeWhileAntitone (< lk) lt `Set.union` gt
  LeftOpen lk uk -> let (lt,_,gt) = Set.splitMember uk s in
    Set.takeWhileAntitone (<= lk) lt `Set.union` gt
  RightOpen lk uk -> let (lt,_,gt) = Set.splitMember lk s in
    lt `Set.union` Set.dropWhileAntitone (< uk) gt
  BothOpen lk uk ->
    Set.takeWhileAntitone (<= lk) s `Set.union` Set.dropWhileAntitone (< uk) s
{-# INLINE differenceSetAndInterval #-}
