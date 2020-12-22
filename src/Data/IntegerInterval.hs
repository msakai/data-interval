{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE CPP, ScopedTypeVariables, DeriveDataTypeable #-}
{-# LANGUAGE Safe #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.IntegerInterval
-- Copyright   :  (c) Masahiro Sakai 2011-2014
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, DeriveDataTypeable)
--
-- Interval datatype and interval arithmetic over integers.
--
-- Since 1.2.0
--
-- For the purpose of abstract interpretation, it might be convenient to use
-- 'Lattice' instance. See also lattices package
-- (<http://hackage.haskell.org/package/lattices>).
--
-----------------------------------------------------------------------------
module Data.IntegerInterval
  (
  -- * Interval type
    IntegerInterval
  , module Data.ExtendedReal
  , Boundary(..)

  -- * Construction
  , interval
  , (<=..<=)
  , (<..<=)
  , (<=..<)
  , (<..<)
  , whole
  , empty
  , singleton

  -- * Query
  , null
  , isSingleton
  , member
  , notMember
  , isSubsetOf
  , isProperSubsetOf
  , isConnected
  , lowerBound
  , upperBound
  , lowerBound'
  , upperBound'
  , width

  -- * Universal comparison operators
  , (<!), (<=!), (==!), (>=!), (>!), (/=!)

  -- * Existential comparison operators
  , (<?), (<=?), (==?), (>=?), (>?), (/=?)

  -- * Existential comparison operators that produce witnesses (experimental)
  , (<??), (<=??), (==??), (>=??), (>??), (/=??)

  -- * Combine
  , intersection
  , intersections
  , hull
  , hulls

  -- * Map
  , mapMonotonic

  -- * Operations
  , pickup
  , simplestIntegerWithin

  -- * Conversion
  , toInterval
  , fromInterval
  , fromIntervalOver
  , fromIntervalUnder

  -- * Intervals relation
  , relate
  ) where

#if MIN_VERSION_lattices
import Algebra.Lattice
#endif
import Control.Exception (assert)
import Control.Monad hiding (join)
import Data.ExtendedReal
import Data.List (foldl')
import Data.Maybe
import Prelude hiding (null)
import Data.IntegerInterval.Internal
import Data.Interval.Internal (Boundary(..))
import qualified Data.Interval.Internal as Interval
import Data.IntervalRelation

infix 5 <..<=
infix 5 <=..<
infix 5 <..<
infix 4 <!
infix 4 <=!
infix 4 ==!
infix 4 >=!
infix 4 >!
infix 4 /=!
infix 4 <?
infix 4 <=?
infix 4 ==?
infix 4 >=?
infix 4 >?
infix 4 /=?
infix 4 <??
infix 4 <=??
infix 4 ==??
infix 4 >=??
infix 4 >??
infix 4 /=??

-- | 'lowerBound' of the interval and whether it is included in the interval.
-- The result is convenient to use as an argument for 'interval'.
lowerBound' :: IntegerInterval -> (Extended Integer, Boundary)
lowerBound' x =
  case lowerBound x of
    lb@(Finite _) -> (lb, Closed)
    lb@_ -> (lb, Open)

-- | 'upperBound' of the interval and whether it is included in the interval.
-- The result is convenient to use as an argument for 'interval'.
upperBound' :: IntegerInterval -> (Extended Integer, Boundary)
upperBound' x =
  case upperBound x of
    ub@(Finite _) -> (ub, Closed)
    ub@_ -> (ub, Open)

#if MIN_VERSION_lattices
#if MIN_VERSION_lattices(2,0,0)

instance Lattice IntegerInterval where
  (\/) = hull
  (/\) = intersection

instance BoundedJoinSemiLattice IntegerInterval where
  bottom = empty

instance BoundedMeetSemiLattice IntegerInterval where
  top = whole

#else

instance JoinSemiLattice IntegerInterval where
  join = hull

instance MeetSemiLattice IntegerInterval where
  meet = intersection

instance Lattice IntegerInterval

instance BoundedJoinSemiLattice IntegerInterval where
  bottom = empty

instance BoundedMeetSemiLattice IntegerInterval where
  top = whole

instance BoundedLattice IntegerInterval

#endif
#endif

instance Show IntegerInterval where
  showsPrec _ x | null x = showString "empty"
  showsPrec p x =
    showParen (p > rangeOpPrec) $
      showsPrec (rangeOpPrec+1) (lowerBound x) .
      showString " <=..<= " .
      showsPrec (rangeOpPrec+1) (upperBound x)

instance Read IntegerInterval where
  readsPrec p r =
    (readParen (p > appPrec) $ \s0 -> do
      ("interval",s1) <- lex s0
      (lb,s2) <- readsPrec (appPrec+1) s1
      (ub,s3) <- readsPrec (appPrec+1) s2
      return (interval lb ub, s3)) r
    ++
    (readParen (p > rangeOpPrec) $ \s0 -> do
      (do (lb,s1) <- readsPrec (rangeOpPrec+1) s0
          ("<=..<=",s2) <- lex s1
          (ub,s3) <- readsPrec (rangeOpPrec+1) s2
          return (lb <=..<= ub, s3))) r
    ++
    (do ("empty", s) <- lex r
        return (empty, s))

-- | smart constructor for 'IntegerInterval'
interval
  :: (Extended Integer, Boundary) -- ^ lower bound and whether it is included
  -> (Extended Integer, Boundary) -- ^ upper bound and whether it is included
  -> IntegerInterval
interval (x1,in1) (x2,in2) =
  (if in1 == Closed then x1 else x1 + 1) <=..<= (if in2 == Closed then x2 else x2 - 1)

-- | left-open right-closed interval (@l@,@u@]
(<..<=)
  :: Extended Integer -- ^ lower bound @l@
  -> Extended Integer -- ^ upper bound @u@
  -> IntegerInterval
(<..<=) lb ub = (lb+1) <=..<= ub

-- | left-closed right-open interval [@l@, @u@)
(<=..<)
  :: Extended Integer -- ^ lower bound @l@
  -> Extended Integer -- ^ upper bound @u@
  -> IntegerInterval
(<=..<) lb ub = lb <=..<= ub-1

-- | open interval (@l@, @u@)
(<..<)
  :: Extended Integer -- ^ lower bound @l@
  -> Extended Integer -- ^ upper bound @u@
  -> IntegerInterval
(<..<) lb ub = lb+1 <=..<= ub-1

-- | whole real number line (-∞, ∞)
whole :: IntegerInterval
whole = NegInf <=..<= PosInf

-- | singleton set [x,x]
singleton :: Integer -> IntegerInterval
singleton x = Finite x <=..<= Finite x

-- | intersection of two intervals
intersection :: IntegerInterval -> IntegerInterval -> IntegerInterval
intersection x1 x2 =
  max (lowerBound x1) (lowerBound x2) <=..<= min (upperBound x1) (upperBound x2)

-- | intersection of a list of intervals.
intersections :: [IntegerInterval] -> IntegerInterval
intersections = foldl' intersection whole

-- | convex hull of two intervals
hull :: IntegerInterval -> IntegerInterval -> IntegerInterval
hull x1 x2
  | null x1 = x2
  | null x2 = x1
hull x1 x2 =
  min (lowerBound x1) (lowerBound x2) <=..<= max (upperBound x1) (upperBound x2)

-- | convex hull of a list of intervals.
hulls :: [IntegerInterval] -> IntegerInterval
hulls = foldl' hull empty

-- | @mapMonotonic f i@ is the image of @i@ under @f@, where @f@ must be a strict monotone function.
mapMonotonic :: (Integer -> Integer) -> IntegerInterval -> IntegerInterval
mapMonotonic f x = fmap f (lowerBound x) <=..<= fmap f (upperBound x)

-- | Is the interval empty?
null :: IntegerInterval -> Bool
null x = upperBound x < lowerBound x

-- | Is the interval single point?
--
-- @since 2.0.0
isSingleton :: IntegerInterval -> Bool
isSingleton x = lowerBound x == upperBound x

-- | Is the element in the interval?
member :: Integer -> IntegerInterval -> Bool
member x i = lowerBound i <= Finite x && Finite x <= upperBound i

-- | Is the element not in the interval?
notMember :: Integer -> IntegerInterval -> Bool
notMember a i = not $ member a i

-- | Is this a subset?
-- @(i1 \``isSubsetOf`\` i2)@ tells whether @i1@ is a subset of @i2@.
isSubsetOf :: IntegerInterval -> IntegerInterval -> Bool
isSubsetOf i1 i2 = lowerBound i2 <= lowerBound i1 && upperBound i1 <= upperBound i2

-- | Is this a proper subset? (/i.e./ a subset but not equal).
isProperSubsetOf :: IntegerInterval -> IntegerInterval -> Bool
isProperSubsetOf i1 i2 = i1 /= i2 && i1 `isSubsetOf` i2

-- | Does the union of two range form a set which is the intersection between the integers and a connected real interval?
isConnected :: IntegerInterval -> IntegerInterval -> Bool
isConnected x y = null x || null y || x ==? y || lb1nearUb2 || ub1nearLb2
  where
    lb1 = lowerBound x
    lb2 = lowerBound y
    ub1 = upperBound x
    ub2 = upperBound y

    lb1nearUb2 = case (lb1, ub2) of
      (Finite lb1Int, Finite ub2Int) -> lb1Int == ub2Int + 1
      _                              -> False

    ub1nearLb2 = case (ub1, lb2) of
      (Finite ub1Int, Finite lb2Int) -> ub1Int + 1 == lb2Int
      _                              -> False

-- | Width of a interval. Width of an unbounded interval is @undefined@.
width :: IntegerInterval -> Integer
width x
  | null x = 0
  | otherwise =
      case (upperBound x, lowerBound x) of
        (Finite lb, Finite ub) -> ub - lb
        _ -> error "Data.IntegerInterval.width: unbounded interval"

-- | pick up an element from the interval if the interval is not empty.
pickup :: IntegerInterval -> Maybe Integer
pickup x =
  case (lowerBound x, upperBound x) of
    (NegInf, PosInf) -> Just 0
    (Finite l, _) -> Just l
    (_, Finite u) -> Just u
    _ -> Nothing

-- | 'simplestIntegerWithin' returns the simplest rational number within the interval.
--
-- An integer @y@ is said to be /simpler/ than another @y'@ if
--
-- * @'abs' y <= 'abs' y'@
--
-- (see also 'Data.Ratio.approxRational' and 'Interval.simplestRationalWithin')
simplestIntegerWithin :: IntegerInterval -> Maybe Integer
simplestIntegerWithin i
  | null i    = Nothing
  | 0 <! i    = Just $ let Finite x = lowerBound i in x
  | i <! 0    = Just $ let Finite x = upperBound i in x
  | otherwise = assert (0 `member` i) $ Just 0

-- | For all @x@ in @X@, @y@ in @Y@. @x '<' y@?
(<!) :: IntegerInterval -> IntegerInterval -> Bool
--a <! b = upperBound a < lowerBound b
a <! b = a+1 <=! b

-- | For all @x@ in @X@, @y@ in @Y@. @x '<=' y@?
(<=!) :: IntegerInterval -> IntegerInterval -> Bool
a <=! b = upperBound a <= lowerBound b

-- | For all @x@ in @X@, @y@ in @Y@. @x '==' y@?
(==!) :: IntegerInterval -> IntegerInterval -> Bool
a ==! b = a <=! b && a >=! b

-- | For all @x@ in @X@, @y@ in @Y@. @x '/=' y@?
(/=!) :: IntegerInterval -> IntegerInterval -> Bool
a /=! b = null $ a `intersection` b

-- | For all @x@ in @X@, @y@ in @Y@. @x '>=' y@?
(>=!) :: IntegerInterval -> IntegerInterval -> Bool
(>=!) = flip (<=!)

-- | For all @x@ in @X@, @y@ in @Y@. @x '>' y@?
(>!) :: IntegerInterval -> IntegerInterval -> Bool
(>!) = flip (<!)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '<' y@?
(<?) :: IntegerInterval -> IntegerInterval -> Bool
a <? b = lowerBound a < upperBound b

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '<' y@?
(<??) :: IntegerInterval -> IntegerInterval -> Maybe (Integer, Integer)
a <?? b = do
  (x,y) <- a+1 <=?? b
  return (x-1,y)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '<=' y@?
(<=?) :: IntegerInterval -> IntegerInterval -> Bool
a <=? b =
  case lb_a `compare` ub_b of
    LT -> True
    GT -> False
    EQ ->
      case lb_a of
        NegInf -> False -- b is empty
        PosInf -> False -- a is empty
        Finite _ -> True
  where
    lb_a = lowerBound a
    ub_b = upperBound b

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '<=' y@?
(<=??) :: IntegerInterval -> IntegerInterval -> Maybe (Integer,Integer)
a <=?? b =
  case pickup (intersection a b) of
    Just x -> return (x,x)
    Nothing -> do
      guard $ upperBound a <= lowerBound b
      x <- pickup a
      y <- pickup b
      return (x,y)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '==' y@?
(==?) :: IntegerInterval -> IntegerInterval -> Bool
a ==? b = not $ null $ intersection a b

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '==' y@?
(==??) :: IntegerInterval -> IntegerInterval -> Maybe (Integer,Integer)
a ==?? b = do
  x <- pickup (intersection a b)
  return (x,x)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '/=' y@?
(/=?) :: IntegerInterval -> IntegerInterval -> Bool
a /=? b = not (null a) && not (null b) && not (a == b && isSingleton a)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '/=' y@?
(/=??) :: IntegerInterval -> IntegerInterval -> Maybe (Integer,Integer)
a /=?? b = do
  guard $ not $ null a
  guard $ not $ null b
  guard $ not $ a == b && isSingleton a
  if not (isSingleton b)
    then f a b
    else liftM (\(y,x) -> (x,y)) $ f b a
  where
    f i j = do
      x <- pickup i
      y <- msum [pickup (j `intersection` c) | c <- [-inf <..< Finite x, Finite x <..< inf]]
      return (x,y)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '>=' y@?
(>=?) :: IntegerInterval -> IntegerInterval -> Bool
(>=?) = flip (<=?)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '>' y@?
(>?) :: IntegerInterval -> IntegerInterval -> Bool
(>?) = flip (<?)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '>=' y@?
(>=??) :: IntegerInterval -> IntegerInterval -> Maybe (Integer, Integer)
(>=??) = flip (<=??)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '>' y@?
(>??) :: IntegerInterval -> IntegerInterval -> Maybe (Integer, Integer)
(>??) = flip (<??)

appPrec :: Int
appPrec = 10

rangeOpPrec :: Int
rangeOpPrec = 5

scaleInterval :: Integer -> IntegerInterval -> IntegerInterval
scaleInterval _ x | null x = empty
scaleInterval c x =
  case compare c 0 of
    EQ -> singleton 0
    LT -> Finite c * upperBound x <=..<= Finite c * lowerBound x
    GT -> Finite c * lowerBound x <=..<= Finite c * upperBound x

instance Num IntegerInterval where
  a + b
      | null a || null b = empty
      | otherwise = lowerBound a + lowerBound b <=..<= upperBound a + upperBound b

  negate = scaleInterval (-1)

  fromInteger i = singleton (fromInteger i)

  abs x = (x `intersection` nonneg) `hull` (negate x `intersection` nonneg)
    where
      nonneg = 0 <=..< inf

  signum x = zero `hull` pos `hull` neg
    where
      zero = if member 0 x then singleton 0 else empty
      pos = if null $ (0 <..< inf) `intersection` x
            then empty
            else singleton 1
      neg = if null $ (-inf <..< 0) `intersection` x
            then empty
            else singleton (-1)

  a * b
    | null a || null b = empty
    | otherwise = minimum xs <=..<= maximum xs
    where
      xs = [ mul x1 x2 | x1 <- [lowerBound a, upperBound a], x2 <- [lowerBound b, upperBound b] ]

      mul :: Extended Integer -> Extended Integer -> Extended Integer
      mul 0 _ = 0
      mul _ 0 = 0
      mul x1 x2 = x1*x2

-- | Convert the interval to 'Interval.Interval' data type.
toInterval :: Real r => IntegerInterval -> Interval.Interval r
toInterval x = Interval.interval
  (fmap fromInteger (lowerBound x), Closed)
  (fmap fromInteger (upperBound x), Closed)

-- | Conversion from 'Interval.Interval' data type.
fromInterval :: Interval.Interval Integer -> IntegerInterval
fromInterval i = x1' <=..<= x2'
  where
    (x1,in1) = Interval.lowerBound' i
    (x2,in2) = Interval.upperBound' i
    x1' = case in1 of
      Interval.Open   -> x1 + 1
      Interval.Closed -> x1
    x2' = case in2 of
      Interval.Open   -> x2 - 1
      Interval.Closed -> x2

-- | Given a 'Interval.Interval' @I@ over R, compute the smallest 'IntegerInterval' @J@ such that @I ⊆ J@.
fromIntervalOver :: RealFrac r => Interval.Interval r -> IntegerInterval
fromIntervalOver i = fmap floor lb <=..<= fmap ceiling ub
  where
    (lb, _) = Interval.lowerBound' i
    (ub, _) = Interval.upperBound' i

-- | Given a 'Interval.Interval' @I@ over R, compute the largest 'IntegerInterval' @J@ such that @J ⊆ I@.
fromIntervalUnder :: RealFrac r => Interval.Interval r -> IntegerInterval
fromIntervalUnder i = lb <=..<= ub
  where
    lb = case Interval.lowerBound' i of
      (Finite x, Open)
        | fromInteger (ceiling x) == x
        -> Finite (ceiling x + 1)
      (x, _) -> fmap ceiling x
    ub = case Interval.upperBound' i of
      (Finite x, Open)
        | fromInteger (floor x) == x
        -> Finite (floor x - 1)
      (x, _) -> fmap floor x

-- | Computes how two intervals are related according to the @`Data.IntervalRelation.Relation`@ classification
relate :: IntegerInterval -> IntegerInterval -> Relation
relate i1 i2 =
  case (i1 `isSubsetOf` i2, i2 `isSubsetOf` i1) of
    -- 'i1' ad 'i2' are equal
    (True , True ) -> Equal
    -- 'i1' is strictly contained in `i2`
    (True , False) | lowerBound i1 == lowerBound i2 -> Starts
                   | upperBound i1 == upperBound i2 -> Finishes
                   | otherwise                      -> During
    -- 'i2' is strictly contained in `i1`
    (False, True ) | lowerBound i1 == lowerBound i2 -> StartedBy
                   | upperBound i1 == upperBound i2 -> FinishedBy
                   | otherwise                      -> Contains
    -- neither `i1` nor `i2` is contained in the other
    (False, False) -> case ( null (i1 `intersection` i2)
                           , lowerBound i1 <= lowerBound i2
                           , i1 `isConnected` i2
                           ) of
      (True , True , True ) -> JustBefore
      (True , True , False) -> Before
      (True , False, True ) -> JustAfter
      (True , False, False) -> After
      (False, True , _    ) -> Overlaps
      (False, False, _    ) -> OverlappedBy
