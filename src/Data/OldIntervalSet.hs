{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, LambdaCase, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable, MultiWayIf #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE RoleAnnotations #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.OldIntervalSet
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (CPP, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable, MultiWayIf)
--
-- Interval datatype and interval arithmetic.
--
-----------------------------------------------------------------------------
module Data.OldIntervalSet
  (
  -- * IntervalSet type
    IntervalSet(..)
  , module Data.ExtendedReal

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
  , span

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

  -- ** List
  , fromList
  , toList

  -- ** Ordered list
  , toAscList
  , toDescList
  , fromAscList
  )
  where

import Prelude hiding (null, span)
#ifdef MIN_VERSION_lattices
import Algebra.Lattice
#endif
import Control.DeepSeq
import Data.Data
import Data.ExtendedReal
import Data.Function
import Data.Hashable
import Data.List (sortBy, foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Semigroup as Semigroup
import Data.Interval (Interval, Boundary(..))
import qualified Data.Interval as Interval
#if __GLASGOW_HASKELL__ < 804
import Data.Monoid (Monoid(..))
#endif
import qualified GHC.Exts as GHCExts

-- | A set comprising zero or more non-empty, /disconnected/ intervals.
--
-- Any connected intervals are merged together, and empty intervals are ignored.
newtype IntervalSet r = IntervalSet (Map (Extended r) (Interval r))
  deriving
    ( Eq
    , Ord
      -- ^ Note that this Ord is derived and not semantically meaningful.
      -- The primary intended use case is to allow using 'IntervalSet'
      -- in maps and sets that require ordering.
    , Typeable
    )

type role IntervalSet nominal

instance (Ord r, Show r) => Show (IntervalSet r) where
  showsPrec p (IntervalSet m) = showParen (p > appPrec) $
    showString "fromList " .
    showsPrec (appPrec+1) (Map.elems m)

instance (Ord r, Read r) => Read (IntervalSet r) where
  readsPrec p =
    (readParen (p > appPrec) $ \s0 -> do
      ("fromList",s1) <- lex s0
      (xs,s2) <- readsPrec (appPrec+1) s1
      return (fromList xs, s2))

appPrec :: Int
appPrec = 10

-- This instance preserves data abstraction at the cost of inefficiency.
-- We provide limited reflection services for the sake of data abstraction.

instance (Ord r, Data r) => Data (IntervalSet r) where
  gfoldl k z x   = z fromList `k` toList x
  toConstr _     = fromListConstr
  gunfold k z c  = case constrIndex c of
    1 -> k (z fromList)
    _ -> error "gunfold"
  dataTypeOf _   = setDataType
  dataCast1 f    = gcast1 f

fromListConstr :: Constr
fromListConstr = mkConstr setDataType "fromList" [] Prefix

setDataType :: DataType
setDataType = mkDataType "Data.IntervalSet.IntervalSet" [fromListConstr]

instance NFData r => NFData (IntervalSet r) where
  rnf (IntervalSet m) = rnf m

instance Hashable r => Hashable (IntervalSet r) where
  hashWithSalt s (IntervalSet m) = hashWithSalt s (Map.toList m)

#ifdef MIN_VERSION_lattices
#if MIN_VERSION_lattices(2,0,0)

instance (Ord r) => Lattice (IntervalSet r) where
  (\/) = union
  (/\) = intersection

instance (Ord r) => BoundedJoinSemiLattice (IntervalSet r) where
  bottom = empty

instance (Ord r) => BoundedMeetSemiLattice (IntervalSet r) where
  top = whole

#else

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

#endif
#endif

instance Ord r => Monoid (IntervalSet r) where
  mempty = empty
  mappend = (Semigroup.<>)
  mconcat = unions

instance (Ord r) => Semigroup.Semigroup (IntervalSet r) where
  (<>)    = union
  stimes  = Semigroup.stimesIdempotentMonoid

lift1
  :: Ord r => (Interval r -> Interval r)
  -> IntervalSet r -> IntervalSet r
lift1 f as = fromList [f a | a <- toList as]

lift2
  :: Ord r => (Interval r -> Interval r -> Interval r)
  -> IntervalSet r -> IntervalSet r -> IntervalSet r
lift2 f as bs = fromList [f a b | a <- toList as, b <- toList bs]

instance (Num r, Ord r) => Num (IntervalSet r) where
  (+) = lift2 (+)

  (*) = lift2 (*)

  negate = lift1 negate

  abs = lift1 abs

  fromInteger i = singleton (fromInteger i)

  signum xs = fromList $ do
    x <- toList xs
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

-- | @recip (recip xs) == delete 0 xs@
instance forall r. (Real r, Fractional r) => Fractional (IntervalSet r) where
  fromRational r = singleton (fromRational r)
  recip xs = lift1 recip (delete (Interval.singleton 0) xs)

instance Ord r => GHCExts.IsList (IntervalSet r) where
  type Item (IntervalSet r) = Interval r
  fromList = fromList
  toList = toList

-- -----------------------------------------------------------------------

-- | whole real number line (-∞, ∞)
whole :: Ord r => IntervalSet r
whole = singleton $ Interval.whole

-- | empty interval set
empty :: Ord r => IntervalSet r
empty = IntervalSet Map.empty

-- | single interval
singleton :: Ord r => Interval r -> IntervalSet r
singleton i
  | Interval.null i = empty
  | otherwise = IntervalSet $ Map.singleton (Interval.lowerBound i) i

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
isSubsetOf is1 is2 = all (\i1 -> f i1 is2) (toList is1)
  where
    f i1 (IntervalSet m) =
      case Map.lookupLE (Interval.lowerBound i1) m of
        Nothing -> False
        Just (_,i2) -> Interval.isSubsetOf i1 i2

-- | Is this a proper subset? (/i.e./ a subset but not equal).
isProperSubsetOf :: Ord r => IntervalSet r -> IntervalSet r -> Bool
isProperSubsetOf is1 is2 = isSubsetOf is1 is2 && is1 /= is2

-- | convex hull of a set of intervals.
span :: Ord r => IntervalSet r -> Interval r
span (IntervalSet m) =
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
complement (IntervalSet m) = fromAscList $ f (NegInf,Open) (Map.elems m)
  where
    f prev [] = [ Interval.interval prev (PosInf,Open) ]
    f prev (i : is) =
      case (Interval.lowerBound' i, Interval.upperBound' i) of
        ((lb, in1), (ub, in2)) ->
          Interval.interval prev (lb, notB in1) : f (ub, notB in2) is

-- | Insert a new interval into the interval set.
insert :: Ord r => Interval r -> IntervalSet r -> IntervalSet r
insert i is | Interval.null i = is
insert i (IntervalSet is) = IntervalSet $ Map.unions
  [ smaller'
  , case fromList $ i : maybeToList m0 ++ maybeToList m1 ++ maybeToList m2 of
      IntervalSet m -> m
  , larger
  ]
  where
    (smaller, m1, xs) = splitLookupLE (Interval.lowerBound i) is
    (_, m2, larger) = splitLookupLE (Interval.upperBound i) xs

    -- A tricky case is when an interval @i@ connects two adjacent
    -- members of IntervalSet, e. g., inserting {0} into (whole \\ {0}).
    (smaller', m0) = case Map.maxView smaller of
      Nothing -> (smaller, Nothing)
      Just (v, rest)
        | Interval.isConnected v i -> (rest, Just v)
      _ -> (smaller, Nothing)

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
  then foldl' (\is i -> insert i is) is1 (toList is2)
  else foldl' (\is i -> insert i is) is2 (toList is1)

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
  foldl' (\is i -> delete i is) is1 (toList is2)

-- -----------------------------------------------------------------------

-- | Build a interval set from a list of intervals.
fromList :: Ord r => [Interval r] -> IntervalSet r
fromList = IntervalSet . fromAscList' . sortBy (compareLB `on` Interval.lowerBound')

-- | Build a map from an ascending list of intervals.
-- /The precondition is not checked./
fromAscList :: Ord r => [Interval r] -> IntervalSet r
fromAscList = IntervalSet . fromAscList'

fromAscList' :: Ord r => [Interval r] -> Map (Extended r) (Interval r)
fromAscList' = Map.fromDistinctAscList . map (\i -> (Interval.lowerBound i, i)) . f
  where
    f :: Ord r => [Interval r] -> [Interval r]
    f [] = []
    f (x : xs) = g x xs
    g x [] = [x | not (Interval.null x)]
    g x (y : ys)
      | Interval.null x = g y ys
      | Interval.isConnected x y = g (x `Interval.hull` y) ys
      | otherwise = x : g y ys

-- | Convert a interval set into a list of intervals.
toList :: Ord r => IntervalSet r -> [Interval r]
toList = toAscList

-- | Convert a interval set into a list of intervals in ascending order.
toAscList :: Ord r => IntervalSet r -> [Interval r]
toAscList (IntervalSet m) = Map.elems m

-- | Convert a interval set into a list of intervals in descending order.
toDescList :: Ord r => IntervalSet r -> [Interval r]
toDescList (IntervalSet m) = fmap snd $ Map.toDescList m

-- -----------------------------------------------------------------------

splitLookupLE :: Ord k => k -> Map k v -> (Map k v, Maybe v, Map k v)
splitLookupLE k m =
  case Map.spanAntitone (<= k) m of
    (lessOrEqual, greaterThan) ->
      case Map.maxView lessOrEqual of
        Just (v, lessOrEqual') -> (lessOrEqual', Just v, greaterThan)
        Nothing -> (lessOrEqual, Nothing, greaterThan)

compareLB :: Ord r => (Extended r, Boundary) -> (Extended r, Boundary) -> Ordering
compareLB (lb1, lb1in) (lb2, lb2in) =
  -- inclusive lower endpoint shuold be considered smaller
  (lb1 `compare` lb2) `mappend` (lb2in `compare` lb1in)

upTo :: Ord r => Interval r -> Interval r
upTo i =
  case Interval.lowerBound' i of
    (NegInf, _) -> Interval.empty
    (PosInf, _) -> Interval.whole
    (Finite lb, incl) ->
      Interval.interval (NegInf, Open) (Finite lb, notB incl)

downTo :: Ord r => Interval r -> Interval r
downTo i =
  case Interval.upperBound' i of
    (PosInf, _) -> Interval.empty
    (NegInf, _) -> Interval.whole
    (Finite ub, incl) ->
      Interval.interval (Finite ub, notB incl) (PosInf, Open)

notB :: Boundary -> Boundary
notB = \case
  Open   -> Closed
  Closed -> Open
