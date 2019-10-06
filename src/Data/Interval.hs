{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE CPP, LambdaCase, ScopedTypeVariables #-}
{-# LANGUAGE Safe #-}
#if __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE RoleAnnotations #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Interval
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (CPP, ScopedTypeVariables, DeriveDataTypeable)
--
-- Interval datatype and interval arithmetic.
--
-- Unlike the intervals package (<http://hackage.haskell.org/package/intervals>),
-- this module provides both open and closed intervals and is intended to be used
-- with 'Rational'.
--
-- For the purpose of abstract interpretation, it might be convenient to use
-- 'Lattice' instance. See also lattices package
-- (<http://hackage.haskell.org/package/lattices>).
--
-----------------------------------------------------------------------------
module Data.Interval
  (
  -- * Interval type
    Interval
  , module Data.ExtendedReal
  , EndPoint
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
  , simplestRationalWithin
  ) where

import Algebra.Lattice
import Control.Exception (assert)
import Control.Monad hiding (join)
import Data.ExtendedReal
import Data.Interval.Internal
import Data.List hiding (null)
import Data.Maybe
import Data.Monoid
import Data.Ratio
import Prelude hiding (null)

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

#if MIN_VERSION_lattices(2,0,0)

instance (Ord r) => Lattice (Interval r) where
  (\/) = hull
  (/\) = intersection

instance (Ord r) => BoundedJoinSemiLattice (Interval r) where
  bottom = empty

instance (Ord r) => BoundedMeetSemiLattice (Interval r) where
  top = whole

#else

instance (Ord r) => JoinSemiLattice (Interval r) where
  join = hull

instance (Ord r) => MeetSemiLattice (Interval r) where
  meet = intersection

instance (Ord r) => Lattice (Interval r)

instance (Ord r) => BoundedJoinSemiLattice (Interval r) where
  bottom = empty

instance (Ord r) => BoundedMeetSemiLattice (Interval r) where
  top = whole

instance (Ord r) => BoundedLattice (Interval r)

#endif

instance (Ord r, Show r) => Show (Interval r) where
  showsPrec _ x | null x = showString "empty"
  showsPrec p i =
    showParen (p > rangeOpPrec) $
      showsPrec (rangeOpPrec+1) lb .
      showChar ' ' . showString op . showChar ' ' .
      showsPrec (rangeOpPrec+1) ub
    where
      (lb, in1) = lowerBound' i
      (ub, in2) = upperBound' i
      op = sign in1 ++ ".." ++ sign in2
      sign = \case
        Open   -> "<"
        Closed -> "<="

instance (Ord r, Read r) => Read (Interval r) where
  readsPrec p r =
    (readParen (p > appPrec) $ \s0 -> do
      ("interval",s1) <- lex s0
      (lb,s2) <- readsPrec (appPrec+1) s1
      (ub,s3) <- readsPrec (appPrec+1) s2
      return (interval lb ub, s3)) r
    ++
    (readParen (p > rangeOpPrec) $ \s0 -> do
      (do (l,s1) <- readsPrec (rangeOpPrec+1) s0
          (op',s2) <- lex s1
          op <-
            case op' of
              "<=..<=" -> return (<=..<=)
              "<..<="  -> return (<..<=)
              "<=..<"  -> return (<=..<)
              "<..<"   -> return (<..<)
              _ -> []
          (u,s3) <- readsPrec (rangeOpPrec+1) s2
          return (op l u, s3))) r
    ++
    (do ("empty", s) <- lex r
        return (empty, s))

-- | Lower endpoint (/i.e./ greatest lower bound)  of the interval.
--
-- * 'lowerBound' of the empty interval is 'PosInf'.
--
-- * 'lowerBound' of a left unbounded interval is 'NegInf'.
--
-- * 'lowerBound' of an interval may or may not be a member of the interval.
lowerBound :: Interval r -> Extended r
lowerBound = fst . lowerBound'

-- | Upper endpoint (/i.e./ least upper bound) of the interval.
--
-- * 'upperBound' of the empty interval is 'NegInf'.
--
-- * 'upperBound' of a right unbounded interval is 'PosInf'.
--
-- * 'upperBound' of an interval may or may not be a member of the interval.
upperBound :: Interval r -> Extended r
upperBound = fst . upperBound'

-- | closed interval [@l@,@u@]
(<=..<=)
  :: (Ord r)
  => Extended r -- ^ lower bound @l@
  -> Extended r -- ^ upper bound @u@
  -> Interval r
(<=..<=) lb ub = interval (lb, Closed) (ub, Closed)

-- | left-open right-closed interval (@l@,@u@]
(<..<=)
  :: (Ord r)
  => Extended r -- ^ lower bound @l@
  -> Extended r -- ^ upper bound @u@
  -> Interval r
(<..<=) lb ub = interval (lb, Open) (ub, Closed)

-- | left-closed right-open interval [@l@, @u@)
(<=..<)
  :: (Ord r)
  => Extended r -- ^ lower bound @l@
  -> Extended r -- ^ upper bound @u@
  -> Interval r
(<=..<) lb ub = interval (lb, Closed) (ub, Open)

-- | open interval (@l@, @u@)
(<..<)
  :: (Ord r)
  => Extended r -- ^ lower bound @l@
  -> Extended r -- ^ upper bound @u@
  -> Interval r
(<..<) lb ub = interval (lb, Open) (ub, Open)

-- | whole real number line (-∞, ∞)
whole :: Ord r => Interval r
whole = interval (NegInf, Open) (PosInf, Open)

-- | singleton set \[x,x\]
singleton :: Ord r => r -> Interval r
singleton x = interval (Finite x, Closed) (Finite x, Closed)

-- | intersection of two intervals
intersection :: forall r. Ord r => Interval r -> Interval r -> Interval r
intersection i1 i2 = interval
  (maxLB (lowerBound' i1) (lowerBound' i2))
  (minUB (upperBound' i1) (upperBound' i2))
  where
    maxLB :: (Extended r, Boundary) -> (Extended r, Boundary) -> (Extended r, Boundary)
    maxLB (x1,in1) (x2,in2) =
      ( max x1 x2
      , case x1 `compare` x2 of
          EQ -> in1 `min` in2
          LT -> in2
          GT -> in1
      )
    minUB :: (Extended r, Boundary) -> (Extended r, Boundary) -> (Extended r, Boundary)
    minUB (x1,in1) (x2,in2) =
      ( min x1 x2
      , case x1 `compare` x2 of
          EQ -> in1 `min` in2
          LT -> in1
          GT -> in2
      )

-- | intersection of a list of intervals.
--
-- Since 0.6.0
intersections :: Ord r => [Interval r] -> Interval r
intersections = foldl' intersection whole

-- | convex hull of two intervals
hull :: forall r. Ord r => Interval r -> Interval r -> Interval r
hull x1 x2
  | null x1 = x2
  | null x2 = x1
hull i1 i2 = interval
  (minLB (lowerBound' i1) (lowerBound' i2))
  (maxUB (upperBound' i1) (upperBound' i2))
  where
    maxUB :: (Extended r, Boundary) -> (Extended r, Boundary) -> (Extended r, Boundary)
    maxUB (x1,in1) (x2,in2) =
      ( max x1 x2
      , case x1 `compare` x2 of
          EQ -> in1 `max` in2
          LT -> in2
          GT -> in1
      )
    minLB :: (Extended r, Boundary) -> (Extended r, Boundary) -> (Extended r, Boundary)
    minLB (x1,in1) (x2,in2) =
      ( min x1 x2
      , case x1 `compare` x2 of
          EQ -> in1 `max` in2
          LT -> in1
          GT -> in2
      )

-- | convex hull of a list of intervals.
--
-- Since 0.6.0
hulls :: Ord r => [Interval r] -> Interval r
hulls = foldl' hull empty

-- | Is the interval empty?
null :: Ord r => Interval r -> Bool
null i =
  case x1 `compare` x2 of
    EQ -> assert (in1 == Closed && in2 == Closed) False
    LT -> False
    GT -> True
  where
    (x1, in1) = lowerBound' i
    (x2, in2) = upperBound' i

isSingleton :: Ord r => Interval r -> Bool
isSingleton i = case (lowerBound' i, upperBound' i) of
  ((Finite l, Closed), (Finite u, Closed)) -> l==u
  _ -> False

-- | Is the element in the interval?
member :: Ord r => r -> Interval r -> Bool
member x i = condLB && condUB
  where
    (x1, in1) = lowerBound' i
    (x2, in2) = upperBound' i
    condLB = case in1 of
      Open   -> x1 <  Finite x
      Closed -> x1 <= Finite x
    condUB = case in2 of
      Open   -> Finite x <  x2
      Closed -> Finite x <= x2

-- | Is the element not in the interval?
notMember :: Ord r => r -> Interval r -> Bool
notMember a i = not $ member a i

-- | Is this a subset?
-- @(i1 \``isSubsetOf`\` i2)@ tells whether @i1@ is a subset of @i2@.
isSubsetOf :: Ord r => Interval r -> Interval r -> Bool
isSubsetOf i1 i2 = testLB (lowerBound' i1) (lowerBound' i2) && testUB (upperBound' i1) (upperBound' i2)
  where
    testLB (x1,in1) (x2,in2) =
      case x1 `compare` x2 of
        GT -> True
        LT -> False
        EQ -> in1 <= in2
    testUB (x1,in1) (x2,in2) =
      case x1 `compare` x2 of
        LT -> True
        GT -> False
        EQ -> in1 <= in2

-- | Is this a proper subset? (/i.e./ a subset but not equal).
isProperSubsetOf :: Ord r => Interval r -> Interval r -> Bool
isProperSubsetOf i1 i2 = i1 /= i2 && i1 `isSubsetOf` i2

-- | Does the union of two range form a connected set?
--
-- Since 1.3.0
isConnected :: Ord r => Interval r -> Interval r -> Bool
isConnected x y
  | null x = True
  | null y = True
  | otherwise = x ==? y || (lb1==ub2 && (lb1in == Closed || ub2in == Closed)) || (ub1==lb2 && (ub1in == Closed || lb2in == Closed))
  where
    (lb1,lb1in) = lowerBound' x
    (lb2,lb2in) = lowerBound' y
    (ub1,ub1in) = upperBound' x
    (ub2,ub2in) = upperBound' y

-- | Width of a interval. Width of an unbounded interval is @undefined@.
width :: (Num r, Ord r) => Interval r -> r
width x
  | null x = 0
  | otherwise = case (fst (lowerBound' x), fst (upperBound' x)) of
    (Finite l, Finite u) -> u - l
    _ -> error "Data.Interval.width: unbounded interval"

-- | pick up an element from the interval if the interval is not empty.
pickup :: (Real r, Fractional r) => Interval r -> Maybe r
pickup i = case (lowerBound' i, upperBound' i) of
  ((NegInf,_), (PosInf,_))             -> Just 0
  ((Finite x1, in1), (PosInf,_))       -> Just $ case in1 of
    Open   -> x1 + 1
    Closed -> x1
  ((NegInf,_), (Finite x2, in2))       -> Just $ case in2 of
    Open   -> x2 - 1
    Closed -> x2
  ((Finite x1, in1), (Finite x2, in2)) ->
    case x1 `compare` x2 of
      GT -> Nothing
      LT -> Just $ (x1+x2) / 2
      EQ -> if in1 == Closed && in2 == Closed then Just x1 else Nothing
  _ -> Nothing

-- | 'simplestRationalWithin' returns the simplest rational number within the interval.
--
-- A rational number @y@ is said to be /simpler/ than another @y'@ if
--
-- * @'abs' ('numerator' y) <= 'abs' ('numerator' y')@, and
--
-- * @'denominator' y <= 'denominator' y'@.
--
-- (see also 'approxRational')
--
-- Since 0.4.0
simplestRationalWithin :: RealFrac r => Interval r -> Maybe Rational
simplestRationalWithin i | null i = Nothing
simplestRationalWithin i
  | 0 <! i    = Just $ go i
  | i <! 0    = Just $ - go (- i)
  | otherwise = assert (0 `member` i) $ Just 0
  where
    go j
      | fromInteger lb_floor       `member` j = fromInteger lb_floor
      | fromInteger (lb_floor + 1) `member` j = fromInteger (lb_floor + 1)
      | otherwise = fromInteger lb_floor + recip (go (recip (j - singleton (fromInteger lb_floor))))
      where
        Finite lb = lowerBound j
        lb_floor  = floor lb

-- | @mapMonotonic f i@ is the image of @i@ under @f@, where @f@ must be a strict monotone function.
mapMonotonic :: (Ord a, Ord b) => (a -> b) -> Interval a -> Interval b
mapMonotonic f i = interval (fmap f lb, in1) (fmap f ub, in2)
  where
    (lb, in1) = lowerBound' i
    (ub, in2) = upperBound' i

-- | For all @x@ in @X@, @y@ in @Y@. @x '<' y@?
(<!) :: Ord r => Interval r -> Interval r -> Bool
a <! b =
  case ub_a `compare` lb_b of
    LT -> True
    GT -> False
    EQ ->
      case ub_a of
        NegInf   -> True -- a is empty, so it holds vacuously
        PosInf   -> True -- b is empty, so it holds vacuously
        Finite _ -> in1 == Open || in2 == Open
  where
    (ub_a, in1) = upperBound' a
    (lb_b, in2) = lowerBound' b

-- | For all @x@ in @X@, @y@ in @Y@. @x '<=' y@?
(<=!) :: Ord r => Interval r -> Interval r -> Bool
a <=! b = upperBound a <= lowerBound b

-- | For all @x@ in @X@, @y@ in @Y@. @x '==' y@?
(==!) :: Ord r => Interval r -> Interval r -> Bool
a ==! b = a <=! b && a >=! b

-- | For all @x@ in @X@, @y@ in @Y@. @x '/=' y@?
--
-- Since 1.0.1
(/=!) :: Ord r => Interval r -> Interval r -> Bool
a /=! b = null $ a `intersection` b

-- | For all @x@ in @X@, @y@ in @Y@. @x '>=' y@?
(>=!) :: Ord r => Interval r -> Interval r -> Bool
(>=!) = flip (<=!)

-- | For all @x@ in @X@, @y@ in @Y@. @x '>' y@?
(>!) :: Ord r => Interval r -> Interval r -> Bool
(>!) = flip (<!)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '<' y@?
(<?) :: Ord r => Interval r -> Interval r -> Bool
a <? b = lb_a < ub_b
  where
    lb_a = lowerBound a
    ub_b = upperBound b

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '<' y@?
--
-- Since 1.0.0
(<??) :: (Real r, Fractional r) => Interval r -> Interval r -> Maybe (r,r)
a <?? b = do
  guard $ lowerBound a < upperBound b
  let c = intersection a b
  case pickup c of
    Nothing -> do
      x <- pickup a
      y <- pickup b
      return (x,y)
    Just z -> do
      let x:y:_ = take 2 $
                    maybeToList (pickup (intersection a (-inf <..< Finite z))) ++
                    [z] ++
                    maybeToList (pickup (intersection b (Finite z <..< inf)))
      return (x,y)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '<=' y@?
(<=?) :: Ord r => Interval r -> Interval r -> Bool
a <=? b =
  case lb_a `compare` ub_b of
    LT -> True
    GT -> False
    EQ ->
      case lb_a of
        NegInf -> False -- b is empty
        PosInf -> False -- a is empty
        Finite _ -> in1 == Closed && in2 == Closed
  where
    (lb_a, in1) = lowerBound' a
    (ub_b, in2) = upperBound' b

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '<=' y@?
--
-- Since 1.0.0
(<=??) :: (Real r, Fractional r) => Interval r -> Interval r -> Maybe (r,r)
a <=?? b =
  case pickup (intersection a b) of
    Just x -> return (x,x)
    Nothing -> do
      guard $ upperBound a <= lowerBound b
      x <- pickup a
      y <- pickup b
      return (x,y)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '==' y@?
--
-- Since 1.0.0
(==?) :: Ord r => Interval r -> Interval r -> Bool
a ==? b = not $ null $ intersection a b

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '==' y@?
--
-- Since 1.0.0
(==??) :: (Real r, Fractional r) => Interval r -> Interval r -> Maybe (r,r)
a ==?? b = do
  x <- pickup (intersection a b)
  return (x,x)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '/=' y@?
--
-- Since 1.0.1
(/=?) :: Ord r => Interval r -> Interval r -> Bool
a /=? b = not (null a) && not (null b) && not (a == b && isSingleton a)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '/=' y@?
--
-- Since 1.0.1
(/=??) :: (Real r, Fractional r) => Interval r -> Interval r -> Maybe (r,r)
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
(>=?) :: Ord r => Interval r -> Interval r -> Bool
(>=?) = flip (<=?)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '>' y@?
(>?) :: Ord r => Interval r -> Interval r -> Bool
(>?) = flip (<?)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '>=' y@?
--
-- Since 1.0.0
(>=??) :: (Real r, Fractional r) => Interval r -> Interval r -> Maybe (r,r)
(>=??) = flip (<=??)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '>' y@?
--
-- Since 1.0.0
(>??) :: (Real r, Fractional r) => Interval r -> Interval r -> Maybe (r,r)
(>??) = flip (<??)

appPrec :: Int
appPrec = 10

rangeOpPrec :: Int
rangeOpPrec = 5

scaleInterval :: (Num r, Ord r) => r -> Interval r -> Interval r
scaleInterval c x
  | null x = empty
  | otherwise = case compare c 0 of
    EQ -> singleton 0
    LT -> interval (scaleInf' c ub) (scaleInf' c lb)
    GT -> interval (scaleInf' c lb) (scaleInf' c ub)
  where
    lb = lowerBound' x
    ub = upperBound' x

instance (Num r, Ord r) => Num (Interval r) where
  a + b
    | null a || null b = empty
    | otherwise = interval (f (lowerBound' a) (lowerBound' b)) (g (upperBound' a) (upperBound' b))
    where
      f (Finite x1, in1) (Finite x2, in2) = (Finite (x1+x2), in1 `min` in2)
      f (NegInf,_) _ = (-inf, Open)
      f _ (NegInf,_) = (-inf, Open)
      f _ _ = error "Interval.(+) should not happen"

      g (Finite x1, in1) (Finite x2, in2) = (Finite (x1+x2), in1 `min` in2)
      g (PosInf,_) _ = (inf, Open)
      g _ (PosInf,_) = (inf, Open)
      g _ _ = error "Interval.(+) should not happen"

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
    | otherwise = interval lb3 ub3
    where
      xs = [ mulInf' x1 x2 | x1 <- [lowerBound' a, upperBound' a], x2 <- [lowerBound' b, upperBound' b] ]
      ub3 = maximumBy cmpUB xs
      lb3 = minimumBy cmpLB xs

instance forall r. (Real r, Fractional r) => Fractional (Interval r) where
  fromRational r = singleton (fromRational r)
  recip a
    | null a = empty
    | 0 `member` a = whole -- should be error?
    | otherwise = interval lb3 ub3
    where
      ub3 = maximumBy cmpUB xs
      lb3 = minimumBy cmpLB xs
      xs = [recipLB (lowerBound' a), recipUB (upperBound' a)]

cmpUB, cmpLB :: Ord r => (Extended r, Boundary) -> (Extended r, Boundary) -> Ordering
cmpUB (x1,in1) (x2,in2) = compare x1 x2 `mappend` compare in1 in2
cmpLB (x1,in1) (x2,in2) = compare x1 x2 `mappend` compare in2 in1

{-# DEPRECATED EndPoint "EndPoint is deprecated. Please use Extended instead." #-}
-- | Endpoints of intervals
type EndPoint r = Extended r

scaleInf' :: (Num r, Ord r) => r -> (Extended r, Boundary) -> (Extended r, Boundary)
scaleInf' a (x1, in1) = (scaleEndPoint a x1, in1)

scaleEndPoint :: (Num r, Ord r) => r -> Extended r -> Extended r
scaleEndPoint a e =
  case a `compare` 0 of
    EQ -> 0
    GT ->
      case e of
        NegInf   -> NegInf
        Finite b -> Finite (a*b)
        PosInf   -> PosInf
    LT ->
      case e of
        NegInf   -> PosInf
        Finite b -> Finite (a*b)
        PosInf   -> NegInf

mulInf' :: (Num r, Ord r) => (Extended r, Boundary) -> (Extended r, Boundary) -> (Extended r, Boundary)
mulInf' (0, Closed) _ = (0, Closed)
mulInf' _ (0, Closed) = (0, Closed)
mulInf' (x1,in1) (x2,in2) = (x1*x2, in1 `min` in2)

recipLB :: (Fractional r, Ord r) => (Extended r, Boundary) -> (Extended r, Boundary)
recipLB (0, _) = (PosInf, Open)
recipLB (x1, in1) = (recip x1, in1)

recipUB :: (Fractional r, Ord r) => (Extended r, Boundary) -> (Extended r, Boundary)
recipUB (0, _) = (NegInf, Open)
recipUB (x1, in1) = (recip x1, in1)
