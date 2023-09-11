{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP, LambdaCase, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable, MultiWayIf, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE RoleAnnotations #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.IntervalMap.Base
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
module Data.IntervalMap.Base
  (
  -- * IntervalMap type
    IntervalMap (..)
  , module Data.ExtendedReal

  -- * Operators
  , (!)
  , (\\)

  -- * Query
  , null
  , member
  , notMember
  , lookup
  , findWithDefault
  , span

  -- * Construction
  , whole
  , empty
  , singleton

  -- ** Insertion
  , insert
  , insertWith

  -- ** Delete\/Update
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
  , intersectionWith
  , difference

  -- * Traversal
  , map
  , mapKeysMonotonic

  -- * Conversion
  , elems
  , keys
  , assocs
  , keysSet

  -- ** List
  , fromList
  , fromListWith
  , toList

  -- ** Ordered List
  , toAscList
  , toDescList

  -- * Filter
  , filter
  , split

  -- * Submap
  , isSubmapOf
  , isSubmapOfBy
  , isProperSubmapOf
  , isProperSubmapOfBy
  )
  where

import Prelude hiding (null, lookup, map, filter, span, and)
import Control.DeepSeq
import Data.Data
import Data.ExtendedReal
import Data.Hashable
import Data.Foldable hiding (null, toList)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Semigroup as Semigroup
import Data.Interval (Interval)
import qualified Data.Interval as Interval
import Data.IntervalSet (IntervalSet)
import qualified Data.IntervalSet as IntervalSet
#if __GLASGOW_HASKELL__ < 804
import Data.Monoid (Monoid(..))
#endif
import qualified GHC.Exts as GHCExts

-- ------------------------------------------------------------------------
-- The IntervalMap type

-- | A Map from non-empty, disjoint intervals over k to values a.
--
-- Unlike 'IntervalSet', 'IntervalMap' never merge adjacent mappings,
-- even if adjacent intervals are connected and mapped to the same value.
newtype IntervalMap r a = IntervalMap (Map (LB r) (Interval r, a))
  deriving
    ( Eq
    , Ord
      -- ^ Note that this Ord is derived and not semantically meaningful.
      -- The primary intended use case is to allow using 'IntervalSet'
      -- in maps and sets that require ordering.
    , Typeable
    )

type role IntervalMap nominal representational

instance (Ord k, Show k, Show a) => Show (IntervalMap k a) where
  showsPrec p (IntervalMap m) = showParen (p > appPrec) $
    showString "fromList " .
    showsPrec (appPrec+1) (Map.elems m)

instance (Ord k, Read k, Read a) => Read (IntervalMap k a) where
  readsPrec p =
    (readParen (p > appPrec) $ \s0 -> do
      ("fromList",s1) <- lex s0
      (xs,s2) <- readsPrec (appPrec+1) s1
      return (fromList xs, s2))

appPrec :: Int
appPrec = 10

-- This instance preserves data abstraction at the cost of inefficiency.
-- We provide limited reflection services for the sake of data abstraction.

instance (Data k, Data a, Ord k) => Data (IntervalMap k a) where
  gfoldl k z x   = z fromList `k` toList x
  toConstr _     = fromListConstr
  gunfold k z c  = case constrIndex c of
    1 -> k (z fromList)
    _ -> error "gunfold"
  dataTypeOf _   = mapDataType
  dataCast1 f    = gcast1 f

fromListConstr :: Constr
fromListConstr = mkConstr mapDataType "fromList" [] Prefix

mapDataType :: DataType
mapDataType = mkDataType "Data.IntervalMap.Base.IntervalMap" [fromListConstr]

instance (NFData k, NFData a) => NFData (IntervalMap k a) where
  rnf (IntervalMap m) = rnf m

instance (Hashable k, Hashable a) => Hashable (IntervalMap k a) where
  hashWithSalt s m = hashWithSalt s (toList m)

instance Ord k => Monoid (IntervalMap k a) where
  mempty = empty
  mappend = (Semigroup.<>)
  mconcat = unions

instance Ord k => Semigroup.Semigroup (IntervalMap k a) where
  (<>)   = union
  stimes = Semigroup.stimesIdempotentMonoid

instance Ord k => GHCExts.IsList (IntervalMap k a) where
  type Item (IntervalMap k a) = (Interval k, a)
  fromList = fromList
  toList = toList

-- ------------------------------------------------------------------------

newtype LB r = LB (Extended r, Interval.Boundary)
  deriving (Eq, NFData, Typeable)

instance Ord r => Ord (LB r) where
  compare (LB (lb1, lb1in)) (LB (lb2, lb2in)) =
    -- inclusive lower endpoint shuold be considered smaller
    (lb1 `compare` lb2) `mappend` (lb2in `compare` lb1in)

-- ------------------------------------------------------------------------
-- Operators

infixl 9 !,\\ --

-- | Find the value at a key. Calls 'error' when the element can not be found.
(!) :: Ord k => IntervalMap k a -> k -> a
IntervalMap m ! k =
  case Map.lookupLE (LB (Finite k, Interval.Closed)) m of
    Just (_, (i, a)) | k `Interval.member` i -> a
    _ -> error "IntervalMap.!: given key is not an element in the map"

-- | Same as 'difference'.
(\\) :: Ord k => IntervalMap k a -> IntervalMap k b -> IntervalMap k a
m1 \\ m2 = difference m1 m2

-- ------------------------------------------------------------------------
-- Query

-- | Is the map empty?
null :: Ord k => IntervalMap k a -> Bool
null (IntervalMap m) = Map.null m

-- | Is the key a member of the map? See also 'notMember'.
member :: Ord k => k -> IntervalMap k a -> Bool
member k (IntervalMap m) =
  case Map.lookupLE (LB (Finite k, Interval.Closed)) m of
    Just (_, (i, _)) -> k `Interval.member` i
    Nothing -> False

-- | Is the key not a member of the map? See also 'member'.
notMember :: Ord k => k -> IntervalMap k a -> Bool
notMember k m = not $ member k m

-- | Lookup the value at a key in the map.
--
-- The function will return the corresponding value as @('Just' value)@,
-- or 'Nothing' if the key isn't in the map.
lookup :: Ord k => k -> IntervalMap k a -> Maybe a
lookup k (IntervalMap m) =
  case Map.lookupLE (LB (Finite k, Interval.Closed)) m of
    Just (_, (i, a)) | k `Interval.member` i -> Just a
    _ -> Nothing

-- | The expression @('findWithDefault' def k map)@ returns
-- the value at key @k@ or returns default value @def@
-- when the key is not in the map.
findWithDefault :: Ord k => a -> k -> IntervalMap k a -> a
findWithDefault def k (IntervalMap m) =
  case Map.lookupLE (LB (Finite k, Interval.Closed)) m of
    Just (_, (i, a)) | k `Interval.member` i -> a
    _ -> def

lookupInterval :: Ord k => Interval k -> IntervalMap k a -> Maybe a
lookupInterval i (IntervalMap m) =
  case Map.lookupLE (LB (Interval.lowerBound' i)) m of
    Just (_, (j, a)) | i `Interval.isSubsetOf` j -> Just a
    _ -> Nothing

-- | convex hull of key intervals.
span :: Ord k => IntervalMap k a -> Interval k
span = IntervalSet.span . keysSet

-- ------------------------------------------------------------------------
-- Construction

-- | The empty map.
empty :: Ord k => IntervalMap k a
empty = IntervalMap Map.empty

-- | The map that maps whole range of k to a.
whole :: Ord k => a -> IntervalMap k a
whole a = IntervalMap $ Map.singleton (LB (Interval.lowerBound' i)) (i, a)
  where
    i = Interval.whole

-- | A map with a single interval.
singleton :: Ord k => Interval k -> a -> IntervalMap k a
singleton i a
  | Interval.null i = empty
  | otherwise = IntervalMap $ Map.singleton (LB (Interval.lowerBound' i)) (i, a)

-- ------------------------------------------------------------------------
-- Insertion

-- | insert a new key and value in the map.
-- If the key is already present in the map, the associated value is
-- replaced with the supplied value.
insert :: Ord k => Interval k -> a -> IntervalMap k a -> IntervalMap k a
insert i _ m | Interval.null i = m
insert i a m =
  case split i m of
    (IntervalMap m1, _, IntervalMap m2) ->
      IntervalMap $ Map.union m1 (Map.insert (LB (Interval.lowerBound' i)) (i,a) m2)


-- | Insert with a function, combining new value and old value.
-- @'insertWith' f key value mp@ will insert the pair (interval, value) into @mp@.
-- If the interval overlaps with existing entries, the value for the entry is replace
-- with @(f new_value old_value)@.
insertWith :: Ord k => (a -> a -> a) -> Interval k -> a -> IntervalMap k a -> IntervalMap k a
insertWith _ i _ m | Interval.null i = m
insertWith f i a m = alter g i m
  where
    g Nothing = Just a
    g (Just a') = Just $ f a a'

-- ------------------------------------------------------------------------
-- Delete/Update

-- | Delete an interval and its value from the map.
-- When the interval does not overlap with the map, the original map is returned.
delete :: Ord k => Interval k -> IntervalMap k a -> IntervalMap k a
delete i m | Interval.null i = m
delete i m =
  case split i m of
    (IntervalMap m1, _, IntervalMap m2) ->
      IntervalMap $ Map.union m1 m2

-- | Update a value at a specific interval with the result of the provided function.
-- When the interval does not overlatp with the map, the original map is returned.
adjust :: Ord k => (a -> a) -> Interval k -> IntervalMap k a -> IntervalMap k a
adjust f = update (Just . f)

-- | The expression (@'update' f i map@) updates the value @x@
-- at @i@ (if it is in the map). If (@f x@) is 'Nothing', the element is
-- deleted. If it is (@'Just' y@), the key @i@ is bound to the new value @y@.
update :: Ord k => (a -> Maybe a) -> Interval k -> IntervalMap k a -> IntervalMap k a
update _ i m | Interval.null i = m
update f i m =
  case split i m of
    (IntervalMap m1, IntervalMap m2, IntervalMap m3) ->
      IntervalMap $ Map.unions [m1, Map.mapMaybe (\(j,a) -> (\b -> (j,b)) <$> f a) m2, m3]

-- | The expression (@'alter' f i map@) alters the value @x@ at @i@, or absence thereof.
-- 'alter' can be used to insert, delete, or update a value in a 'IntervalMap'.
alter :: Ord k => (Maybe a -> Maybe a) -> Interval k -> IntervalMap k a -> IntervalMap k a
alter _ i m | Interval.null i = m
alter f i m =
  case split i m of
    (IntervalMap m1, IntervalMap m2, IntervalMap m3) ->
      let m2' = Map.mapMaybe (\(j,a) -> (\b -> (j,b)) <$> f (Just a)) m2
          js = IntervalSet.singleton i `IntervalSet.difference` keysSet (IntervalMap m2)
          IntervalMap m2'' =
            case f Nothing of
              Nothing -> empty
              Just a -> fromList [(j,a) | j <- IntervalSet.toList js]
      in IntervalMap $ Map.unions [m1, m2', m2'', m3]

-- ------------------------------------------------------------------------
-- Combine

-- | The expression (@'union' t1 t2@) takes the left-biased union of @t1@ and @t2@.
-- It prefers @t1@ when overlapping keys are encountered,
union :: Ord k => IntervalMap k a -> IntervalMap k a -> IntervalMap k a
union m1 m2 =
  foldl' (\m (i,a) -> insert i a m) m2 (toList m1)

-- | Union with a combining function.
unionWith :: Ord k => (a -> a -> a) -> IntervalMap k a -> IntervalMap k a -> IntervalMap k a
unionWith f m1 m2 =
  foldl' (\m (i,a) -> insertWith f i a m) m2 (toList m1)

-- | The union of a list of maps:
--   (@'unions' == 'Prelude.foldl' 'union' 'empty'@).
unions :: Ord k => [IntervalMap k a] -> IntervalMap k a
unions = foldl' union empty

-- | The union of a list of maps, with a combining operation:
--   (@'unionsWith' f == 'Prelude.foldl' ('unionWith' f) 'empty'@).
unionsWith :: Ord k => (a -> a -> a) -> [IntervalMap k a] -> IntervalMap k a
unionsWith f = foldl' (unionWith f) empty

-- | Return elements of the first map not existing in the second map.
difference :: Ord k => IntervalMap k a -> IntervalMap k b -> IntervalMap k a
difference m1 m2 = foldl' (\m i -> delete i m) m1 (IntervalSet.toList (keysSet m2))

-- | Intersection of two maps.
-- Return data in the first map for the keys existing in both maps.
intersection :: Ord k => IntervalMap k a -> IntervalMap k a -> IntervalMap k a
intersection = intersectionWith const

-- | Intersection with a combining function.
intersectionWith :: Ord k => (a -> b -> c) -> IntervalMap k a -> IntervalMap k b -> IntervalMap k c
intersectionWith f im1@(IntervalMap m1) im2@(IntervalMap m2)
  | Map.size m1 >= Map.size m2 = g f im1 im2
  | otherwise = g (flip f) im2 im1
  where
    g :: Ord k => (a -> b -> c) -> IntervalMap k a -> IntervalMap k b -> IntervalMap k c
    g h jm1 (IntervalMap m3) = IntervalMap $ Map.unions $ go jm1 (Map.elems m3)
      where
        go _ [] = []
        go im ((i,b) : xs) =
          case split i im of
            (_, IntervalMap m, jm2) ->
              Map.map (\(j, a) -> (j, h a b)) m : go jm2 xs

-- ------------------------------------------------------------------------
-- Traversal

instance Ord k => Functor (IntervalMap k) where
  fmap = map

instance Ord k => Foldable (IntervalMap k) where
  foldMap f (IntervalMap m) = foldMap (\(_,a) -> f a) m

instance Ord k => Traversable (IntervalMap k) where
  traverse f (IntervalMap m) = IntervalMap <$> traverse (\(i,a) -> (\b -> (i,b)) <$> f a) m

-- | Map a function over all values in the map.
map :: (a -> b) -> IntervalMap k a -> IntervalMap k b
map f (IntervalMap m) = IntervalMap $ Map.map (\(i, a) -> (i, f a)) m

-- | @'mapKeysMonotonic' f s@ is the map obtained by applying @f@ to each key of @s@.
-- @f@ must be strictly monotonic.
-- That is, for any values @x@ and @y@, if @x@ < @y@ then @f x@ < @f y@.
mapKeysMonotonic :: forall k1 k2 a. (Ord k1, Ord k2) => (k1 -> k2) -> IntervalMap k1 a -> IntervalMap k2 a
mapKeysMonotonic f = fromList . fmap g . toList
  where
    g :: (Interval k1, a) -> (Interval k2, a)
    g (i, a) = (Interval.mapMonotonic f i, a)

-- ------------------------------------------------------------------------

-- | Return all elements of the map in the ascending order of their keys.
elems :: IntervalMap k a -> [a]
elems (IntervalMap m) = [a | (_,a) <- Map.elems m]

-- | Return all keys of the map in ascending order. Subject to list
keys :: IntervalMap k a -> [Interval k]
keys (IntervalMap m) = [i | (i,_) <- Map.elems m]

-- | An alias for 'toAscList'. Return all key\/value pairs in the map
-- in ascending key order.
assocs :: IntervalMap k a -> [(Interval k, a)]
assocs = toAscList

-- | The set of all keys of the map.
keysSet :: Ord k => IntervalMap k a -> IntervalSet k
keysSet (IntervalMap m) = IntervalSet.fromAscList [i | (i,_) <- Map.elems m]

-- | Convert the map to a list of key\/value pairs.
toList :: IntervalMap k a -> [(Interval k, a)]
toList = toAscList

-- | Convert the map to a list of key/value pairs where the keys are in ascending order.
toAscList :: IntervalMap k a -> [(Interval k, a)]
toAscList (IntervalMap m) = Map.elems m

-- | Convert the map to a list of key/value pairs where the keys are in descending order.
toDescList :: IntervalMap k a -> [(Interval k, a)]
toDescList (IntervalMap m) = fmap snd $ Map.toDescList m

-- | Build a map from a list of key\/value pairs.
-- If the list contains more than one value for the same key, the last value
-- for the key is retained.
fromList :: Ord k => [(Interval k, a)] -> IntervalMap k a
fromList = foldl' (\m (i,a) -> insert i a m) empty

-- | Build a map from a list of key\/value pairs with a combining function.
fromListWith :: Ord k => (a -> a -> a) -> [(Interval k, a)] -> IntervalMap k a
fromListWith f = foldl' (\m (i,a) -> insertWith f i a m) empty

-- ------------------------------------------------------------------------
-- Filter

-- | Filter all values that satisfy some predicate.
filter :: Ord k => (a -> Bool) -> IntervalMap k a -> IntervalMap k a
filter p (IntervalMap m) = IntervalMap $ Map.filter (\(_,a) -> p a) m

-- | The expression (@'split' i map@) is a triple @(map1,map2,map3)@ where
-- the keys in @map1@ are smaller than @i@, the keys in @map2@ are included in @i@, and the keys in @map3@ are larger than @i@.
split :: Ord k => Interval k -> IntervalMap k a -> (IntervalMap k a, IntervalMap k a, IntervalMap k a)
split i (IntervalMap m) =
  case splitLookupLE (LB (Interval.lowerBound' i)) m of
    (smaller, m1, xs) ->
      case splitLookupLE (LB (Interval.upperBound i, Interval.Closed)) xs of
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

-- | This function is defined as (@'isSubmapOf' = 'isSubmapOfBy' (==)@).
isSubmapOf :: (Ord k, Eq a) => IntervalMap k a -> IntervalMap k a -> Bool
isSubmapOf = isSubmapOfBy (==)

-- |  The expression (@'isSubmapOfBy' f t1 t2@) returns 'True' if
-- all keys in @t1@ are in tree @t2@, and when @f@ returns 'True' when
-- applied to their respective values.
isSubmapOfBy :: Ord k => (a -> b -> Bool) -> IntervalMap k a -> IntervalMap k b -> Bool
isSubmapOfBy f m1 m2 = and $
  [ case lookupInterval i m2 of
      Nothing -> False
      Just b -> f a b
  | (i,a) <- toList m1 ]

-- |  Is this a proper submap? (ie. a submap but not equal).
-- Defined as (@'isProperSubmapOf' = 'isProperSubmapOfBy' (==)@).
isProperSubmapOf :: (Ord k, Eq a) => IntervalMap k a -> IntervalMap k a -> Bool
isProperSubmapOf = isProperSubmapOfBy (==)

-- | Is this a proper submap? (ie. a submap but not equal).
-- The expression (@'isProperSubmapOfBy' f m1 m2@) returns 'True' when
-- @m1@ and @m2@ are not equal,
-- all keys in @m1@ are in @m2@, and when @f@ returns 'True' when
-- applied to their respective values.
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
      Interval.interval (NegInf, Interval.Open) (Finite lb, notB incl)

downTo :: Ord r => Interval r -> Interval r
downTo i =
  case Interval.upperBound' i of
    (PosInf, _) -> Interval.empty
    (NegInf, _) -> Interval.whole
    (Finite ub, incl) ->
      Interval.interval (Finite ub, notB incl) (PosInf, Interval.Open)

notB :: Interval.Boundary -> Interval.Boundary
notB = \case
  Interval.Open   -> Interval.Closed
  Interval.Closed -> Interval.Open
