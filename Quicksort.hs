{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FunctionalDependencies #-}
module Quicksort where

import Prelude hiding ( length, read, Read )
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Data.Functor.Identity
import Data.Proxy
import Data.Kind
import Unsafe.Coerce
import System.IO.Unsafe
import GHC.Exts
import Control.Monad (void)
import Data.List (sort)

newtype UArray a n = MkUArray (V.Vector a)
  deriving newtype IsList

class Read n
class Write n
type RW n = (Read n, Write n)
class Slices n l r | l r -> n

newtype Ur a = Ur a
  deriving Show

data a <= c where
  Pack :: c => a -> a <= c

instance Show a => Show (a <= c) where
  show (Pack x) = show x

freshVar :: (forall a. Proxy a -> r) -> r
freshVar k = k Proxy

assume :: forall (c :: Constraint) r. (c => r) -> r
assume k = (unsafeCoerce @(c => r) @(() -> r) k) ()

require :: forall (c :: Constraint) a. c => a -> a
require x = x

length :: UArray a n -> Int
length (MkUArray v) = V.length v

read :: Read n => UArray a n -> Int -> Ur a <= Read n
read (MkUArray v) index = Pack (Ur (v V.! index))

lendMut :: RW n => UArray a n -> Int -> (forall p. RW p => Proxy p -> a -> r <= RW p) -> r <= RW n
lendMut = undefined

exchange :: (RW n, RW p) => Proxy p -> a -> Proxy n -> a -> () <= (RW n, RW p)
exchange = undefined

data SplitResult a n where
  MkSR :: (RW l, RW r, Slices n l r) => Ur (UArray a l, UArray a r) -> SplitResult a n

split :: forall n a. RW n => UArray a n -> Int -> SplitResult a n
split (MkUArray v) index = require @(RW n) $
                           freshVar $ \ (_ :: Proxy l) ->
                           freshVar $ \ (_ :: Proxy r) ->
                           assume @(RW l) $
                           assume @(RW r) $
                           assume @(Slices n l r) $
                           MkSR (Ur (MkUArray @_ @l l, MkUArray @_ @r r))
  where
    (l, r) = V.splitAt index v

join :: forall n l r a. (RW r, RW l, Slices n l r) => UArray a l -> UArray a r -> Ur (UArray a n) <= RW n
join (MkUArray l) (MkUArray r) = require @(RW l) $
                                 require @(RW r) $
                                 assume @(RW n) $
                                 Pack (Ur (MkUArray (l V.++ r)))

swap :: forall n a. RW n => UArray a n -> Int -> Int -> () <= RW n
swap arr i j
  | i == j = Pack ()
  | i > j  = swap arr j i
  | otherwise = runIdentity $ do MkSR (Ur (l, r)) <- return (split arr (i + 1))
                                 Pack () <- return $
                                            lendMut l i $ \ pi ai ->
                                              runIdentity $ do Pack () <- return $
                                                                          lendMut r (j - (i + 1)) $ \ pj aj ->
                                                                            runIdentity $ do Pack () <- return (exchange pi ai pj aj)
                                                                                             return (Pack ())
                                                               return (Pack ())
                                 Pack (Ur _) <- return (join l r)
                                 return (Pack ())

realswap :: Show a => RW n => UArray a n -> Int -> Int -> () <= RW n
realswap (MkUArray v) index1 index2 = Pack $ unsafePerformIO $ do mv <- V.unsafeThaw v  -- black magic and dark rituals here
                                                                  MV.swap mv index1 index2
                                                                {-  v' <- V.unsafeFreeze mv
                                                                  putStrLn $ "realswap " ++ show index1 ++ " " ++ show index2
                                                                  print v' -}

newUArray :: forall r a. Show a => [a] -> (forall n. RW n => UArray a n -> r <= RW n) -> r
newUArray elts k = freshVar $ \ (_ :: Proxy n) ->
                   assume @(RW n) $
                   let v = V.fromList elts
                       !(Pack !r) = k (MkUArray @_ @n v)
                   in unsafePerformIO (print v) `seq` r

-- >>> quicksort []
-- No instance for (Read n0) arising from a use of ‘it’

quicksort :: RW n => UArray Int n -> () <= RW n
quicksort arr =
  if length arr <= 1 then Pack ()
  else runIdentity $ do Pack pivotIdx <- return (partition arr)
                        MkSR (Ur (l, r)) <- return (split arr pivotIdx)
                        (Pack (), Pack ()) <- return (quicksort l, quicksort r)
                        Pack (Ur _) <- return (join l r)
                        return (Pack ())

partition :: forall n. RW n => UArray Int n -> Int <= RW n
partition arr =
  let   last = length arr - 1
        Pack (Ur pivot) = read arr last
        go :: (Int <= RW n) -> [Int] -> Int <= RW n
        go i [] = i
        go (Pack i) (j : js) =
          let   Pack (Ur a_j)    = read arr j
                i'     = if a_j <= pivot
                        then   runIdentity $ do Pack () <- return (realswap arr i j)
                                                return (Pack (i + 1))
                        else Pack i
          in go i' js
        !(Pack i) = go (Pack 0) [0..last-1]
        !(Pack !()) = realswap arr i last
  in Pack i

mypartition :: RW n => UArray Int n -> Int <= RW n
mypartition arr | length arr > 1 =
  let last = length arr - 1
      Pack (Ur pivot) = read arr last
      go :: Int -> Int -> Int
      go l_index r_index
        | l_index > r_index = let !(Pack ()) = realswap arr last l_index in l_index
        | otherwise
        = let Pack (Ur l_val) = read arr l_index in
          if l_val > pivot then let !(Pack ()) = realswap arr l_index r_index in go l_index (r_index - 1)
                           else go (l_index + 1) r_index
  in
  Pack $ go 0 (last - 1)
  | otherwise = error "too short to partition"

prop :: [Int] -> Bool
prop nums = sort nums == newUArray nums (\v@(MkUArray vv) -> quicksort v `seq` Pack (V.toList vv))
