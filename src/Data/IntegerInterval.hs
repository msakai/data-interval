{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables, DeriveDataTypeable #-}
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
  , member
  , notMember
  , isSubsetOf
  , isProperSubsetOf
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
  ) where

import Algebra.Lattice
import Control.DeepSeq
import Control.Exception (assert)
import Control.Monad hiding (join)
import Data.Data
import Data.ExtendedReal
import Data.Hashable
import Data.List hiding (null)
import Data.Maybe
import Prelude hiding (null)
import qualified Data.Interval as Interval

infix 5 <=..<=
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

-- | The intervals (/i.e./ connected and convex subsets) over integers (__Z__).
data IntegerInterval = Interval !(Extended Integer) !(Extended Integer)
  deriving (Eq, Typeable)

-- | Lower endpoint (/i.e./ greatest lower bound)  of the interval.
--
-- * 'lowerBound' of the empty interval is 'PosInf'.
--
-- * 'lowerBound' of a left unbounded interval is 'NegInf'.
--
-- * 'lowerBound' of an interval may or may not be a member of the interval.
lowerBound :: IntegerInterval -> Extended Integer
lowerBound (Interval lb _) = lb

-- | Upper endpoint (/i.e./ least upper bound) of the interval.
--
-- * 'upperBound' of the empty interval is 'NegInf'.
--
-- * 'upperBound' of a right unbounded interval is 'PosInf'.
--
-- * 'upperBound' of an interval is a member of the interval.
upperBound :: IntegerInterval -> Extended Integer
upperBound (Interval _ ub) = ub

-- | 'lowerBound' of the interval and whether it is included in the interval.
-- The result is convenient to use as an argument for 'interval'.
lowerBound' :: IntegerInterval -> (Extended Integer, Bool)
lowerBound' (Interval lb@(Finite _)  _) = (lb, True)
lowerBound' (Interval lb  _) = (lb, False)

-- | 'upperBound' of the interval and whether it is included in the interval.
-- The result is convenient to use as an argument for 'interval'.
upperBound' :: IntegerInterval -> (Extended Integer, Bool)
upperBound' (Interval _ ub@(Finite _)) = (ub, True)
upperBound' (Interval _ ub) = (ub, False)

instance NFData IntegerInterval where
  rnf (Interval lb ub) = rnf lb `seq` rnf ub

instance Hashable IntegerInterval where
  hashWithSalt s (Interval lb ub) = s `hashWithSalt` lb `hashWithSalt` ub

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

-- This instance preserves data abstraction at the cost of inefficiency.
-- We provide limited reflection services for the sake of data abstraction.

instance Data IntegerInterval where
  gfoldl k z x   = z (<=..<=) `k` lowerBound x `k` upperBound x
  toConstr _     = intervalConstr
  gunfold k z c  = case constrIndex c of
    1 -> k (k (z (<=..<=)))
    _ -> error "gunfold"
  dataTypeOf _   = intervalDataType

intervalConstr :: Constr
intervalConstr = mkConstr intervalDataType "<=..<=" [] Infix

intervalDataType :: DataType
intervalDataType = mkDataType "Data.IntegerInterval.IntegerInterval" [intervalConstr]

-- | smart constructor for 'IntegerInterval'
interval
  :: (Extended Integer, Bool) -- ^ lower bound and whether it is included
  -> (Extended Integer, Bool) -- ^ upper bound and whether it is included
  -> IntegerInterval
interval (x1,in1) (x2,in2) =
  (if in1 then x1 else x1 + 1) <=..<= (if in2 then x2 else x2 - 1)

-- | closed interval [@l@,@u@]
(<=..<=)
  :: Extended Integer -- ^ lower bound @l@
  -> Extended Integer -- ^ upper bound @u@
  -> IntegerInterval
(<=..<=) PosInf _ = empty
(<=..<=) _ NegInf = empty
(<=..<=) lb ub
  | lb <= ub  = Interval lb ub
  | otherwise = empty

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
whole = Interval NegInf PosInf

-- | empty (contradicting) interval
empty :: IntegerInterval
empty = Interval PosInf NegInf

-- | singleton set \[x,x\]
singleton :: Integer -> IntegerInterval
singleton x = Finite x <=..<= Finite x

-- | intersection of two intervals
intersection :: IntegerInterval -> IntegerInterval -> IntegerInterval
intersection (Interval l1 u1) (Interval l2 u2) = max l1 l2 <=..<= min u1 u2

-- | intersection of a list of intervals.
intersections :: [IntegerInterval] -> IntegerInterval
intersections = foldl' intersection whole

-- | convex hull of two intervals
hull :: IntegerInterval -> IntegerInterval -> IntegerInterval
hull x1 x2
  | null x1 = x2
  | null x2 = x1
hull (Interval l1 u1) (Interval l2 u2) = min l1 l2 <=..<= max u1 u2

-- | convex hull of a list of intervals.
hulls :: [IntegerInterval] -> IntegerInterval
hulls = foldl' hull empty

-- | @mapMonotonic f i@ is the image of @i@ under @f@, where @f@ must be a strict monotone function.
mapMonotonic :: (Integer -> Integer) -> IntegerInterval -> IntegerInterval
mapMonotonic f (Interval l u) = Interval (fmap f l) (fmap f u)

-- | Is the interval empty?
null :: IntegerInterval -> Bool
null (Interval l u) = u < l

isSingleton :: IntegerInterval -> Bool
isSingleton (Interval l u) = l==u

-- | Is the element in the interval?
member :: Integer -> IntegerInterval -> Bool
member x (Interval l u) = l <= Finite x && Finite x <= u

-- | Is the element not in the interval?
notMember :: Integer -> IntegerInterval -> Bool
notMember a i = not $ member a i

-- | Is this a subset?
-- @(i1 \``isSubsetOf`\` i2)@ tells whether @i1@ is a subset of @i2@.
isSubsetOf :: IntegerInterval -> IntegerInterval -> Bool
isSubsetOf (Interval lb1 ub1) (Interval lb2 ub2) = lb2 <= lb1 && ub1 <= ub2

-- | Is this a proper subset? (/i.e./ a subset but not equal).
isProperSubsetOf :: IntegerInterval -> IntegerInterval -> Bool
isProperSubsetOf i1 i2 = i1 /= i2 && i1 `isSubsetOf` i2

-- | Width of a interval. Width of an unbounded interval is @undefined@.
width :: IntegerInterval -> Integer
width x | null x = 0
width (Interval (Finite l) (Finite u)) = u - l
width _ = error "Data.IntegerInterval.width: unbounded interval"

-- | pick up an element from the interval if the interval is not empty.
pickup :: IntegerInterval -> Maybe Integer
pickup (Interval NegInf PosInf) = Just 0
pickup (Interval (Finite l) _) = Just l
pickup (Interval _ (Finite u)) = Just u
pickup _ = Nothing

-- | 'simplestIntegerWithin' returns the simplest rational number within the interval.
--
-- An integer @y@ is said to be /simpler/ than another @y'@ if
--
-- * @'abs' y <= 'abs' y'@
--
-- (see also 'approxRational' and 'Interval.simplestRationalWithin')
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
    f a b = do
      x <- pickup a
      y <- msum [pickup (b `intersection` c) | c <- [-inf <..< Finite x, Finite x <..< inf]]
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
scaleInterval c (Interval lb ub) =
  case compare c 0 of
    EQ -> singleton 0
    LT -> Finite c * ub <=..<= Finite c * lb
    GT -> Finite c * lb <=..<= Finite c * ub

instance Num IntegerInterval where
  a + b | null a || null b = empty
  Interval lb1 ub1 + Interval lb2 ub2 = lb1 + lb2 <=..<= ub1 + ub2

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

  a * b | null a || null b = empty
  Interval lb1 ub1 * Interval lb2 ub2 = minimum xs <=..<= maximum xs
    where
      xs = [ mul x1 x2 | x1 <- [lb1, ub1], x2 <- [lb2, ub2] ]

      mul :: Extended Integer -> Extended Integer -> Extended Integer
      mul 0 _ = 0
      mul _ 0 = 0
      mul x1 x2 = x1*x2

-- | Convert the interval to 'Interval.Interval' data type.
toInterval :: Real r => IntegerInterval -> Interval.Interval r
toInterval (Interval l u) = fmap fromInteger l Interval.<=..<= fmap fromInteger u

-- | Conversion from 'Interval.Interval' data type.
fromInterval :: Interval.Interval Integer -> IntegerInterval
fromInterval i = (if in1 then x1 else x1 + 1) <=..<= (if in2 then x2 else x2 - 1)
  where
    (x1,in1) = Interval.lowerBound' i
    (x2,in2) = Interval.upperBound' i

-- | Given a 'Interval.Interval' @I@ over R, compute the smallest 'IntegerInterval' @J@ such that @I ⊆ J@.
fromIntervalOver :: RealFrac r => Interval.Interval r -> IntegerInterval
fromIntervalOver i = fmap floor lb <=..<= fmap ceiling ub
  where
    lb = Interval.lowerBound i
    ub = Interval.upperBound i

-- | Given a 'Interval.Interval' @I@ over R, compute the largest 'IntegerInterval' @J@ such that @J ⊆ I@.
fromIntervalUnder :: RealFrac r => Interval.Interval r -> IntegerInterval
fromIntervalUnder i = fmap f lb <=..<= fmap g ub
  where
    lb = Interval.lowerBound i
    ub = Interval.upperBound i
    f x = if fromIntegral y `Interval.member` i then y else y+1
      where
        y = ceiling x
    g x = if fromIntegral y `Interval.member` i then y else y-1
      where
        y = floor x
