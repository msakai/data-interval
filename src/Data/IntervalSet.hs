{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables, DeriveDataTypeable, MultiWayIf #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.IntervalSet
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, DeriveDataTypeable, MultiWayIf)
--
-- Interval datatype and interval arithmetic.
--
-----------------------------------------------------------------------------
module Data.IntervalSet
  (
  -- * IntervalSet type
    IntervalSet
  , module Data.ExtendedReal
  , EndPoint

  -- * Construction
  , whole
  , empty
  , singleton

  -- * Query
  , null
  , member
  , notMember
  , isSubsetOf
  , isProperSubsetOf
  , hull

  -- * Construction
  , complement
  , insert
  , delete

  -- * Combine
  , union
  , unions
  , intersection
  , intersections
  , difference

  -- * Conversion
  , fromInterval
  , fromIntervalList
  , toIntervalList
  )
  where

import Prelude hiding (null)
import Algebra.Lattice
import Control.DeepSeq
import Data.Data
import Data.ExtendedReal
import Data.Function
import Data.Hashable
import Data.List (sortBy, foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Interval (Interval, EndPoint)
import qualified Data.Interval as Interval

-- | A set comprising zero or more non-empty, disconnected intervals.
newtype IntervalSet r = IntervalSet (Map (Extended r) (Interval r))
  deriving (Eq, Typeable)

instance (Ord r, Show r) => Show (IntervalSet r) where
  showsPrec p (IntervalSet m) = showParen (p > appPrec) $
    showString "fromIntervalList " .
    showsPrec (appPrec+1) (Map.elems m)

instance (Ord r, Read r) => Read (IntervalSet r) where
  readsPrec p =
    (readParen (p > appPrec) $ \s0 -> do
      ("fromIntervalList",s1) <- lex s0
      (xs,s2) <- readsPrec (appPrec+1) s1
      return (fromIntervalList xs, s2))

appPrec :: Int
appPrec = 10

-- This instance preserves data abstraction at the cost of inefficiency.
-- We provide limited reflection services for the sake of data abstraction.

instance (Ord r, Data r) => Data (IntervalSet r) where
  gfoldl k z x   = z fromIntervalList `k` toIntervalList x
  toConstr _     = fromIntervalListConstr
  gunfold k z c  = case constrIndex c of
    1 -> k (z fromIntervalList)
    _ -> error "gunfold"
  dataTypeOf _   = mkNoRepType "Data.Interval.Interval"
  dataCast1 f    = gcast1 f

fromIntervalListConstr :: Constr
fromIntervalListConstr = mkConstr mapDataType "fromIntervalList" [] Prefix

mapDataType :: DataType
mapDataType = mkDataType "Data.IntervalSet.IntervalSet" [fromIntervalListConstr]

instance NFData r => NFData (IntervalSet r) where
  rnf (IntervalSet m) = rnf m

instance Hashable r => Hashable (IntervalSet r) where
  hashWithSalt s (IntervalSet m) = hashWithSalt s (Map.toList m)

instance (Ord r) => JoinSemiLattice (IntervalSet r) where
  join = union

instance (Ord r) => MeetSemiLattice (IntervalSet r) where
  meet = intersection

instance (Ord r) => Lattice (IntervalSet r)

instance (Ord r) => BoundedJoinSemiLattice (IntervalSet r) where
  bottom = empty

instance (Ord r) => BoundedMeetSemiLattice (IntervalSet r) where
  top = whole

instance (Ord r) => BoundedLattice (IntervalSet r)

lift1
  :: Ord r => (Interval r -> Interval r)
  -> IntervalSet r -> IntervalSet r
lift1 f as = fromIntervalList [f a | a <- toIntervalList as]

lift2
  :: Ord r => (Interval r -> Interval r -> Interval r)
  -> IntervalSet r -> IntervalSet r -> IntervalSet r
lift2 f as bs = fromIntervalList [f a b | a <- toIntervalList as, b <- toIntervalList bs]

instance (Num r, Ord r) => Num (IntervalSet r) where
  (+) = lift2 (+)

  (*) = lift2 (*)

  negate = lift1 negate

  abs = lift1 abs

  fromInteger i = singleton (fromInteger i)

  signum xs = fromIntervalList $ do
    x <- toIntervalList xs
    y <-
      [ if Interval.member 0 x
        then Interval.singleton 0
        else Interval.empty
      , if Interval.null ((0 Interval.<..< inf) `Interval.intersection` x)
        then Interval.empty
        else Interval.singleton 1
      , if Interval.null ((-inf Interval.<..< 0) `Interval.intersection` x)
        then Interval.empty
        else Interval.singleton (-1)
      ]
    return y

instance forall r. (Real r, Fractional r) => Fractional (IntervalSet r) where
  fromRational r = singleton (fromRational r)
  recip = lift1 recip

-- -----------------------------------------------------------------------

-- | whole real number line (-∞, ∞)
whole :: Ord r => IntervalSet r
whole = fromInterval $ Interval.whole

-- | empty interval set
empty :: Ord r => IntervalSet r
empty = IntervalSet Map.empty

-- | singleton set \[x,x\]
singleton :: Ord r => r -> IntervalSet r
singleton = fromInterval . Interval.singleton

-- -----------------------------------------------------------------------

-- | Is the interval set empty?
null :: IntervalSet r -> Bool
null (IntervalSet m) = Map.null m

-- | Is the element in the interval set?
member :: Ord r => r -> IntervalSet r -> Bool
member x (IntervalSet m) =
  case Map.lookupLE (Finite x) m of
    Nothing -> False
    Just (_,i) -> Interval.member x i

-- | Is the element not in the interval set?
notMember :: Ord r => r -> IntervalSet r -> Bool
notMember x is = not $ x `member` is

-- | Is this a subset?
-- @(is1 \``isSubsetOf`\` is2)@ tells whether @is1@ is a subset of @is2@.
isSubsetOf :: Ord r => IntervalSet r -> IntervalSet r -> Bool
isSubsetOf is1 is2 = all (\i1 -> f i1 is2) (toIntervalList is1)
  where
    f i1 (IntervalSet m) =
      case Map.lookupLE (Interval.lowerBound i1) m of
        Nothing -> False
        Just (_,i2) -> Interval.isSubsetOf i1 i2

-- | Is this a proper subset? (/i.e./ a subset but not equal).
isProperSubsetOf :: Ord r => IntervalSet r -> IntervalSet r -> Bool
isProperSubsetOf is1 is2 = isSubsetOf is1 is2 && is1 /= is2

-- | convex hull of a set of intervals.
hull :: Ord r => IntervalSet r -> Interval r
hull (IntervalSet m) =
  case Map.minView m of
    Nothing -> Interval.empty
    Just (i1, _) ->
      case Map.maxView m of
        Nothing -> Interval.empty
        Just (i2, _) ->
          Interval.interval (Interval.lowerBound' i1) (Interval.upperBound' i2)

-- -----------------------------------------------------------------------

-- | Complement the interval set.
complement :: Ord r => IntervalSet r -> IntervalSet r
complement (IntervalSet m) = IntervalSet $ fromIntervalAscList' $ f (NegInf,False) (Map.elems m)
  where
    f prev [] = [ Interval.interval prev (PosInf,False) ]
    f prev (i : is) =
      case (Interval.lowerBound' i, Interval.upperBound' i) of
        ((lb, in1), (ub, in2)) ->
          Interval.interval prev (lb, not in1) : f (ub, not in2) is

-- | Insert a new interval into the interval set.
insert :: Ord r => Interval r -> IntervalSet r -> IntervalSet r
insert i is | Interval.null i = is
insert i (IntervalSet is) = IntervalSet $
  case splitLookupLE (Interval.lowerBound i) is of
    (smaller, m1, xs) ->
      case splitLookupLE (Interval.upperBound i) xs of
        (_, m2, larger) ->
          Map.unions
          [ smaller
          , case fromIntervalList $ i : maybeToList m1 ++ maybeToList m2 of
              IntervalSet m -> m
          , larger
          ]

-- | Delete an interval from the interval set.
delete :: Ord r => Interval r -> IntervalSet r -> IntervalSet r
delete i is | Interval.null i = is
delete i (IntervalSet is) = IntervalSet $
  case splitLookupLE (Interval.lowerBound i) is of
    (smaller, m1, xs) ->
      case splitLookupLE (Interval.upperBound i) xs of
        (_, m2, larger) ->
          Map.unions
          [ smaller
          , case m1 of
              Nothing -> Map.empty
              Just j -> Map.fromList
                [ (Interval.lowerBound k, k)
                | i' <- [upTo i, downTo i], let k = i' `Interval.intersection` j, not (Interval.null k)
                ]
          , if
            | Just j <- m2, j' <- downTo i `Interval.intersection` j, not (Interval.null j') ->
                Map.singleton (Interval.lowerBound j') j'
            | otherwise -> Map.empty
          , larger
          ]

-- | union of two interval sets
union :: Ord r => IntervalSet r -> IntervalSet r -> IntervalSet r
union is1@(IntervalSet m1) is2@(IntervalSet m2) =
  if Map.size m1 >= Map.size m2
  then foldl' (\is i -> insert i is) is1 (toIntervalList is2)
  else foldl' (\is i -> insert i is) is2 (toIntervalList is1)

-- | union of a list of interval sets
unions :: Ord r => [IntervalSet r] -> IntervalSet r
unions = foldl' union empty

-- | intersection of two interval sets
intersection :: Ord r => IntervalSet r -> IntervalSet r -> IntervalSet r
intersection is1 is2 = difference is1 (complement is2)

-- | intersection of a list of interval sets
intersections :: Ord r => [IntervalSet r] -> IntervalSet r
intersections = foldl' intersection whole

-- | difference of two interval sets
difference :: Ord r => IntervalSet r -> IntervalSet r -> IntervalSet r
difference is1 is2 =
  foldl' (\is i -> delete i is) is1 (toIntervalList is2)

-- -----------------------------------------------------------------------

-- | Build a interval set from a single interval.
fromInterval :: Ord r => Interval r -> IntervalSet r
fromInterval i
  | Interval.null i = empty
  | otherwise = IntervalSet $ Map.singleton (Interval.lowerBound i) i

-- | Build a interval set from a list of intervals.
fromIntervalList :: Ord r => [Interval r] -> IntervalSet r
fromIntervalList = IntervalSet . fromIntervalAscList' . sortBy (compareLB `on` Interval.lowerBound')

fromIntervalAscList' :: Ord r => [Interval r] -> Map (Extended r) (Interval r)
fromIntervalAscList' = Map.fromDistinctAscList . map (\i -> (Interval.lowerBound i, i)) . f
  where
    f :: Ord r => [Interval r] -> [Interval r]
    f [] = []
    f (x : xs) = g x xs
    g x [] = [x | not (Interval.null x)]
    g x (y : ys)
      | Interval.null x = g y ys
      | isConnected x y = g (x `Interval.hull` y) ys
      | otherwise = x : g y ys

-- | Convert a interval set into a list of intervals.
toIntervalList :: Ord r => IntervalSet r -> [Interval r]
toIntervalList (IntervalSet m) = Map.elems m

-- -----------------------------------------------------------------------

splitLookupLE :: Ord k => k -> Map k v -> (Map k v, Maybe v, Map k v)
splitLookupLE k m =
  case Map.splitLookup k m of
    (smaller, Just v, larger) -> (smaller, Just v, larger)
    (smaller, Nothing, larger) ->
      case Map.maxView smaller of
        Just (v, smaller') -> (smaller', Just v, larger)
        Nothing -> (smaller, Nothing, larger)

{-
splitLookupGE :: Ord k => k -> Map k v -> (Map k v, Maybe v, Map k v)
splitLookupGE k m =
  case Map.splitLookup k m of
    (smaller, Just v, larger) -> (smaller, Just v, larger)
    (smaller, Nothing, larger) ->
      case Map.minView larger of
        Just (v, larger') -> (smaller, Just v, larger')
        Nothing -> (smaller, Nothing, larger)
-}

compareLB :: Ord r => (Extended r, Bool) -> (Extended r, Bool) -> Ordering
compareLB (lb1, lb1in) (lb2, lb2in) =
  -- inclusive lower endpoint shuold be considered smaller
  (lb1 `compare` lb2) `mappend` (lb2in `compare` lb1in)

upTo :: Ord r => Interval r -> Interval r
upTo i =
  case Interval.lowerBound' i of
    (NegInf, _) -> Interval.empty
    (PosInf, _) -> Interval.whole
    (Finite lb, incl) ->
      Interval.interval (NegInf,False) (Finite lb, not incl)

downTo :: Ord r => Interval r -> Interval r
downTo i =
  case Interval.upperBound' i of
    (PosInf, _) -> Interval.empty
    (NegInf, _) -> Interval.whole
    (Finite ub, incl) ->
      Interval.interval (Finite ub, not incl) (PosInf,False)

isConnected :: Ord r => Interval r -> Interval r -> Bool
isConnected x y = x Interval.==? y || (lb1==ub2 && (lb1in || ub2in)) || (ub1==lb2 && (ub1in || lb2in))
  where
    (lb1,lb1in) = Interval.lowerBound' x
    (lb2,lb2in) = Interval.lowerBound' y
    (ub1,ub1in) = Interval.upperBound' x
    (ub2,ub2in) = Interval.upperBound' y
