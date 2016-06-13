{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable, MultiWayIf, GeneralizedNewtypeDeriving #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.IntervalMap
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (CPP, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable, MultiWayIf, GeneralizedNewtypeDeriving)
--
-- Interval datatype and interval arithmetic.
--
-----------------------------------------------------------------------------
module Data.IntervalMap
  (
  -- * IntervalMap type
    IntervalMap
  , module Data.ExtendedReal
  , EndPoint

  -- * Operators
  , (!)
  , (\\)

  -- * Query
  , null
  , member
  , notMember
  , lookup
  , findWithDefault
{-
  , isSubsetOf
  , isProperSubsetOf
-}

  -- * Construction
  , whole
  , empty

  -- * Construction
  , insert
  , insertWith
  , delete
  , adjust
  , update
  , alter

  -- * Combine
  , union
  , unionWith
  , unions
  , unionsWith
  , intersection
  , difference

  -- * Traversal
  , map
  , mapKeysMonotonic

  -- * Conversion
  , elems
  , keys
  , assocs
  , keysSet
  , fromInterval
  , fromIntervalList
  , toIntervalList

  -- * Filter
  , split

  -- * Submap
  , isSubmapOf
  , isSubmapOfBy
  , isProperSubmapOf
  , isProperSubmapOfBy
  )
  where

import Prelude hiding (null, lookup, map)
import Control.Applicative hiding (empty)
import Control.DeepSeq
import Control.Monad
import Data.Data
import Data.Foldable hiding (null, foldl', and)
import Data.ExtendedReal
import Data.Hashable
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Traversable
import Data.Interval (Interval, EndPoint)
import qualified Data.Interval as Interval
import Data.IntervalSet (IntervalSet)
import qualified Data.IntervalSet as IntervalSet
#if __GLASGOW_HASKELL__ >= 708
import qualified GHC.Exts as GHCExts
#endif

-- ------------------------------------------------------------------------
-- The IntervalMap type
    
newtype IntervalMap r a = IntervalMap (Map (LB r) (Interval r, a))
  deriving (Eq, Typeable)

instance (Ord k, Show k, Show a) => Show (IntervalMap k a) where
  showsPrec p (IntervalMap m) = showParen (p > appPrec) $
    showString "fromIntervalList " .
    showsPrec (appPrec+1) (Map.elems m)

instance (Ord k, Read k, Read a) => Read (IntervalMap k a) where
  readsPrec p =
    (readParen (p > appPrec) $ \s0 -> do
      ("fromIntervalList",s1) <- lex s0
      (xs,s2) <- readsPrec (appPrec+1) s1
      return (fromIntervalList xs, s2))

appPrec :: Int
appPrec = 10

-- This instance preserves data abstraction at the cost of inefficiency.
-- We provide limited reflection services for the sake of data abstraction.

instance (Data k, Data a, Ord k) => Data (IntervalMap k a) where
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
mapDataType = mkDataType "Data.IntervalMap.IntervalMap" [fromIntervalListConstr]

instance (NFData k, NFData a) => NFData (IntervalMap k a) where
  rnf (IntervalMap m) = rnf m

instance (Hashable k, Hashable a) => Hashable (IntervalMap k a) where
  hashWithSalt s m = hashWithSalt s (toIntervalList m)

instance Ord k => Monoid (IntervalMap k a) where
  mempty = empty
  mappend = union
  mconcat = unions

#if __GLASGOW_HASKELL__ >= 708
instance Ord k => GHCExts.IsList (IntervalMap k a) where
  type Item (IntervalMap k a) = (Interval k, a)
  fromList = fromIntervalList
  toList = toIntervalList
#endif

-- ------------------------------------------------------------------------

newtype LB r = LB (Extended r, Bool)
  deriving (Eq, NFData, Typeable)

instance Ord r => Ord (LB r) where
  compare (LB (lb1, lb1in)) (LB (lb2, lb2in)) =
    -- inclusive lower endpoint shuold be considered smaller
    (lb1 `compare` lb2) `mappend` (lb2in `compare` lb1in)

-- ------------------------------------------------------------------------
-- Operators

infixl 9 !,\\ --

(!) :: Ord k => IntervalMap k a -> k -> a
IntervalMap m ! k =
  case Map.lookupLE (LB (Finite k, True)) m of
    Just (_, (i, a)) | k `Interval.member` i -> a
    _ -> error "IntervalMap.!: given key is not an element in the map"

(\\) :: Ord k => IntervalMap k a -> IntervalMap k b -> IntervalMap k a
m1 \\ m2 = difference m1 m2

-- ------------------------------------------------------------------------
-- Query

null :: Ord k => IntervalMap k a -> Bool
null (IntervalMap m) = Map.null m

member :: Ord k => k -> IntervalMap k a -> Bool
member k (IntervalMap m) =
  case Map.lookupLE (LB (Finite k, True)) m of
    Just (_, (i, _)) -> k `Interval.member` i
    Nothing -> False

notMember :: Ord k => k -> IntervalMap k a -> Bool
notMember k m = not $ member k m

lookup :: Ord k => k -> IntervalMap k a -> Maybe a
lookup k (IntervalMap m) =
  case Map.lookupLE (LB (Finite k, True)) m of
    Just (_, (i, a)) | k `Interval.member` i -> Just a
    _ -> Nothing

findWithDefault :: Ord k => a -> k -> IntervalMap k a -> a
findWithDefault def k (IntervalMap m) =
  case Map.lookupLE (LB (Finite k, True)) m of
    Just (_, (i, a)) | k `Interval.member` i -> a
    _ -> def

lookupInterval :: Ord k => Interval k -> IntervalMap k a -> Maybe a
lookupInterval i (IntervalMap m) =
  case Map.lookupLE (LB (Interval.lowerBound' i)) m of
    Just (_, (j, a)) | i `Interval.isSubsetOf` j -> Just a
    _ -> Nothing

-- ------------------------------------------------------------------------
-- Construction

empty :: Ord k => IntervalMap k a
empty = IntervalMap Map.empty

whole :: Ord k => a -> IntervalMap k a
whole a = IntervalMap $ Map.singleton (LB (Interval.lowerBound' i)) (i, a)
  where
    i = Interval.whole

-- ------------------------------------------------------------------------
-- Insertion

insert :: Ord k => Interval k -> a -> IntervalMap k a -> IntervalMap k a
insert i _ m | Interval.null i = m
insert i a m =
  case split i m of
    (IntervalMap m1, _, IntervalMap m2) ->
      IntervalMap $ Map.union m1 (Map.insert (LB (Interval.lowerBound' i)) (i,a) m2)

insertWith :: Ord k => (a -> a -> a) -> Interval k -> a -> IntervalMap k a -> IntervalMap k a
insertWith _ i _ m | Interval.null i = m
insertWith f i a m = alter g i m
  where
    g Nothing = Just a
    g (Just a') = Just $ f a a'

-- ------------------------------------------------------------------------
-- Delete/Update

delete :: Ord k => Interval k -> IntervalMap k a -> IntervalMap k a
delete i m | Interval.null i = m
delete i m =
  case split i m of
    (IntervalMap m1, _, IntervalMap m2) ->
      IntervalMap $ Map.union m1 m2

adjust :: Ord k => (a -> a) -> Interval k -> IntervalMap k a -> IntervalMap k a
adjust f = update (Just . f)  

update :: Ord k => (a -> Maybe a) -> Interval k -> IntervalMap k a -> IntervalMap k a
update _ i m | Interval.null i = m
update f i m =
  case split i m of
    (IntervalMap m1, IntervalMap m2, IntervalMap m3) ->
      IntervalMap $ Map.unions [m1, Map.mapMaybe (\(i,a) -> (\b -> (i,b)) <$> f a) m2, m3]

alter :: Ord k => (Maybe a -> Maybe a) -> Interval k -> IntervalMap k a -> IntervalMap k a
alter _ i m | Interval.null i = m
alter f i m =
  case split i m of
    (IntervalMap m1, IntervalMap m2, IntervalMap m3) ->
      let m2' = Map.mapMaybe (\(j,a) -> (\b -> (j,b)) <$> f (Just a)) m2
          js = IntervalSet.fromInterval i `IntervalSet.difference` keysSet (IntervalMap m2)
          IntervalMap m2'' =
            case f Nothing of
              Nothing -> empty
              Just a -> fromIntervalList [(j,a) | j <- IntervalSet.toIntervalList js]
      in IntervalMap $ Map.unions [m1, m2', m2'', m3]

-- ------------------------------------------------------------------------
-- Combine

union :: Ord k => IntervalMap k a -> IntervalMap k a -> IntervalMap k a
union m1 m2 = 
  foldl' (\m (i,a) -> insert i a m) m2 (toIntervalList m1)

unionWith :: Ord k => (a -> a -> a) -> IntervalMap k a -> IntervalMap k a -> IntervalMap k a
unionWith f m1 m2 = 
  foldl' (\m (i,a) -> insertWith f i a m) m2 (toIntervalList m1)

unions :: Ord k => [IntervalMap k a] -> IntervalMap k a
unions = foldl' union empty

unionsWith :: Ord k => (a -> a -> a) -> [IntervalMap k a] -> IntervalMap k a
unionsWith f = foldl' (unionWith f) empty

difference :: Ord k => IntervalMap k a -> IntervalMap k b -> IntervalMap k a
difference m1 m2 = foldl' (\m i -> delete i m) m1 (IntervalSet.toIntervalList (keysSet m2))

intersection :: Ord k => IntervalMap k a -> IntervalMap k a -> IntervalMap k a
intersection m1 m2 = foldl' (\m i -> delete i m) m1 (IntervalSet.toIntervalList (IntervalSet.complement (keysSet m2)))

-- ------------------------------------------------------------------------
-- Traversal

instance Ord k => Functor (IntervalMap k) where
  fmap = map

instance Ord k => Foldable (IntervalMap k) where
  foldMap f (IntervalMap m) = foldMap (\(_,a) -> f a) m

instance Ord k => Traversable (IntervalMap k) where
  traverse f (IntervalMap m) = IntervalMap <$> traverse (\(i,a) -> (\b -> (i,b)) <$> f a) m

map :: (a -> b) -> IntervalMap k a -> IntervalMap k b
map f (IntervalMap m) = IntervalMap $ Map.map (\(i, a) -> (i, f a)) m

-- TODO: add Interval.mapMonotonic
mapKeysMonotonic :: forall k1 k2 a. (Ord k1, Ord k2) => (k1 -> k2) -> IntervalMap k1 a -> IntervalMap k2 a
mapKeysMonotonic f = fromIntervalList . fmap g . toIntervalList
  where
    g :: (Interval k1, a) -> (Interval k2, a)
    g (i, a) = (Interval.interval (fmap f lb, in1) (fmap f ub, in2), a)
      where
        (lb, in1) = Interval.lowerBound' i
        (ub, in2) = Interval.upperBound' i

-- ------------------------------------------------------------------------

elems :: IntervalMap k a -> [a]
elems (IntervalMap m) = [a | (_,a) <- Map.elems m]

keys :: IntervalMap k a -> [Interval k]
keys (IntervalMap m) = [i | (i,_) <- Map.elems m]

assocs :: IntervalMap k a -> [(Interval k, a)]
assocs = toIntervalList

-- FIXME: create Interval.fromIntervalAscList and use it
keysSet :: Ord k => IntervalMap k a -> IntervalSet k
keysSet (IntervalMap m) = IntervalSet.fromIntervalList [i | (i,_) <- Map.elems m]

fromInterval :: Ord k => Interval k -> a -> IntervalMap k a
fromInterval i a
  | Interval.null i = empty
  | otherwise = IntervalMap $ Map.singleton (LB (Interval.lowerBound' i)) (i, a)

toIntervalList :: IntervalMap k a -> [(Interval k, a)]
toIntervalList (IntervalMap m) = Map.elems m

fromIntervalList :: Ord k => [(Interval k, a)] -> IntervalMap k a
fromIntervalList = foldl' (\m (i,a) -> insert i a m) empty

-- ------------------------------------------------------------------------
-- Filter

split :: Ord k => Interval k -> IntervalMap k a -> (IntervalMap k a, IntervalMap k a, IntervalMap k a)
split i (IntervalMap m) =
  case splitLookupLE (LB (Interval.lowerBound' i)) m of
    (smaller, m1, xs) -> 
      case splitLookupLE (LB (Interval.upperBound i, True)) xs of
        (middle, m2, larger) ->
          ( IntervalMap $
              case m1 of
                Nothing -> Map.empty
                Just (j,b) ->
                  let k = Interval.intersection (upTo i) j
                  in if Interval.null k
                     then smaller
                     else Map.insert (LB (Interval.lowerBound' k)) (k,b) smaller
          , IntervalMap $ Map.unions $ middle :
              [ Map.singleton (LB (Interval.lowerBound' k)) (k, b)
              | (j, b) <- maybeToList m1 ++ maybeToList m2
              , let k = Interval.intersection i j
              , not (Interval.null k)
              ]
          , IntervalMap $ Map.unions $ larger :
              [ Map.singleton (LB (Interval.lowerBound' k)) (k, b)
              | (j, b) <- maybeToList m1 ++ maybeToList m2
              , let k = Interval.intersection (downTo i) j
              , not (Interval.null k)
              ]
          ) 

-- ------------------------------------------------------------------------
-- Submap

isSubmapOf :: (Ord k, Eq a) => IntervalMap k a -> IntervalMap k a -> Bool
isSubmapOf = isSubmapOfBy (==)

isSubmapOfBy :: Ord k => (a -> b -> Bool) -> IntervalMap k a -> IntervalMap k b -> Bool
isSubmapOfBy f m1 m2 = and $
  [ case lookupInterval i m2 of
      Nothing -> False
      Just b -> f a b
  | (i,a) <- toIntervalList m1 ]

isProperSubmapOf :: (Ord k, Eq a) => IntervalMap k a -> IntervalMap k a -> Bool
isProperSubmapOf = isProperSubmapOfBy (==)

isProperSubmapOfBy :: Ord k => (a -> b -> Bool) -> IntervalMap k a -> IntervalMap k b -> Bool
isProperSubmapOfBy f m1 m2 =
  isSubmapOfBy f m1 m2 &&
  keysSet m1 `IntervalSet.isProperSubsetOf` keysSet m2

-- ------------------------------------------------------------------------

splitLookupLE :: Ord k => k -> Map k v -> (Map k v, Maybe v, Map k v)
splitLookupLE k m =
  case Map.splitLookup k m of
    (smaller, Just v, larger) -> (smaller, Just v, larger)
    (smaller, Nothing, larger) ->
      case Map.maxView smaller of
        Just (v, smaller') -> (smaller', Just v, larger)
        Nothing -> (smaller, Nothing, larger)

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
