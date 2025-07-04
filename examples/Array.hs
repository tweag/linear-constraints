-- | This file is written in token-passing style as GHC doesn't support linear
-- constraints yet. This is verbose, though demonstrates that linearity does
-- indeed works as intended. This is used as a source to ground our examples in
-- the paper.

{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Array where

import GHC.IOArray
import Control.Monad
import GHC.Types
import System.IO.Unsafe (unsafePerformIO)
import Prelude hiding (Read, ($))
import Data.Functor.Const

-------------------------------------------------------------------------------
--
-- Linear types preliminaries for self-containedness
--
-------------------------------------------------------------------------------

data Ur a where {Ur :: a %Many -> Ur a}

($) :: (a %p -> b) %1 -> a %p -> b
f $ x = f x

(&) :: a %p -> (a %p -> b) %1 -> b
x & f = f x

(>>=) :: a %1 -> (a %1 -> b) %1 -> b
x >>= f = f x

fail :: a
fail = error "Incomplete pattern-matching in do notation"


-------------------------------------------------------------------------------
--
-- Quantified functors
--
-------------------------------------------------------------------------------

type Exists :: (i -> Type) -> Type
data Exists f where { Ex :: f i %1 -> Exists f }

type (:*:) :: (i -> Type) -> (i -> Type) -> i -> Type
data (f :*: g) i = P (f i) (g i)

type Id :: (i -> Type) -> i -> Type
newtype Id f i = I (f i)

-- type (:**:) :: (i -> Type) -> (j -> Type) -> (i, j) -> Type
-- data (f :**:g) i = PP (f (Fst i)) (g (Snd i))

type Par :: (i -> Type) -> (i,i) -> Type
data Par f i = PP (f (Fst i)) (f (Snd i))

type (:->) :: (i -> Type) -> Type -> i -> Type
newtype (f :-> a) i = A (f i %1 -> a)

type Fst :: (a, b) -> a
type family Fst ab where
  Fst '(a, _) = a

type Snd :: (a, b) -> b
type family Snd ab where
  Snd '(_, b) = b

-------------------------------------------------------------------------------
--
-- Abstract linearly interface
--
-------------------------------------------------------------------------------

data Linearly = UnsafeMkLinearly

linearly :: (Linearly %1 -> Ur r) %1 -> Ur r
linearly scope = scope UnsafeMkLinearly

consumel :: Linearly %1 -> ()
consumel UnsafeMkLinearly = ()

dupl :: Linearly %1 -> (Linearly, Linearly)
dupl = dupl2

dupl2 :: Linearly %1 -> (Linearly, Linearly)
dupl2 UnsafeMkLinearly = (UnsafeMkLinearly, UnsafeMkLinearly)

dupl3 :: Linearly %1 -> (Linearly, Linearly, Linearly)
dupl3 UnsafeMkLinearly = (UnsafeMkLinearly, UnsafeMkLinearly, UnsafeMkLinearly)

dupl4 :: Linearly %1 -> (Linearly, Linearly, Linearly, Linearly)
dupl4 UnsafeMkLinearly = (UnsafeMkLinearly, UnsafeMkLinearly, UnsafeMkLinearly, UnsafeMkLinearly)

dupl5 :: Linearly %1 -> (Linearly, Linearly, Linearly, Linearly, Linearly)
dupl5 UnsafeMkLinearly = (UnsafeMkLinearly, UnsafeMkLinearly, UnsafeMkLinearly, UnsafeMkLinearly, UnsafeMkLinearly)

-------------------------------------------------------------------------------
--
-- Abstract array interface
--
-------------------------------------------------------------------------------

type Reg = Type
type UArray :: (Reg -> Type) -> Reg -> Type
newtype UArray a n = UnsafeMkUArray (IOArray Int (Exists a))

data Read n = UnsafeMkRead
data Write n = UnsafeMkWrite
type RW n = (Read n, Write n)
unsafeMkRW = (UnsafeMkRead, UnsafeMkWrite)

type Val :: Type -> Reg -> Type
newtype Val a n = MkVal a
-- | Unrestricted!
rwVal :: RW (Val a n)
rwVal = (UnsafeMkRead, UnsafeMkWrite)

-- | `SomeRW a = ∃n. RW n ⊗ a n`
type RW' :: (Reg -> Type) -> Reg -> Type
data RW' a n where
  RW' :: RW n %1 -> a n %Many -> RW' a n

newtype RW'' n = RW (RW n)

data Read' a n where
  Read' :: Read n %1 -> a n %Many -> Read' a n

newUArray :: Linearly %1 -> Int -> (Linearly %1 -> Int -> Exists (RW' a)) -> Exists (RW' (UArray a))
newUArray UnsafeMkLinearly lgth mk = unsafePerformIO $ do
  r <- newIOArray (0, lgth - 1) (error "uninitialised array element")
  forM_ [0 .. lgth - 1] $ \ i ->
    case mk UnsafeMkLinearly i of
      (Ex (RW' _rw a)) -> writeIOArray r i (Ex a)
  return $ Ex (RW' unsafeMkRW (UnsafeMkUArray r))
{-# NOINLINE newUArray #-}

-- Can presumably be changed to
-- :: RW n %1 -> UArray a n -> Int -> RW' a n
-- or even
-- :: Read n %1 -> UArray a n -> Int -> (Read n, Ur a)
-- Everything's garbage collected, so we don't need (or have) an ownership
-- permission to drop when we consider parts of the structures.
borrowUA :: RW n %1 -> UArray a n -> Int -> Exists (RW' a :*: (RW'' :-> RW n))
borrowUA (UnsafeMkRead, UnsafeMkWrite) (UnsafeMkUArray as) i = unsafePerformIO $ do
  Ex a <- readIOArray as i
  return $ Ex (P (RW' unsafeMkRW a) (A (\ !(RW (UnsafeMkRead, UnsafeMkWrite)) -> unsafeMkRW)))
{-# NOINLINE borrowUA #-}

writeUA :: RW n %1 -> RW p %1 -> UArray a n -> Int -> a p -> RW n
writeUA (UnsafeMkRead, UnsafeMkWrite) (UnsafeMkRead, UnsafeMkWrite) (UnsafeMkUArray as) i a = unsafePerformIO $ do
  writeIOArray as i (Ex a)
  return $ unsafeMkRW
{-# NOINLINE writeUA #-}

type Slice :: (Reg -> Type) -> Reg -> Type
data Slice a n = UnsafeMkSlice
  { borrow_method :: RW n %1 -> Int -> Exists (RW' a :*: (RW'' :-> RW n))
  , write_method :: forall p. RW n %1 -> RW p %1 -> Int -> a p -> RW n }

writeSlice :: RW n %1 -> RW p %1 -> Slice a n -> Int -> a p -> RW n
writeSlice rwn rwp as i a = write_method as rwn rwp i a

borrowSlice :: RW n %1 -> Slice a n -> Int -> Exists (RW' a :*: (RW'' :-> RW n))
borrowSlice rwn as i = borrow_method as rwn i

fullSlice :: forall n a. RW n %1 -> UArray a n -> Exists (RW' (Slice a) :*: (RW'' :-> RW n))
fullSlice rwn as = Ex $ P (RW' rwn (UnsafeMkSlice { borrow_method, write_method })) (A (\(RW rw) -> rw))
  where
    borrow_method rwn' i = borrowUA rwn' as i
    write_method :: forall p. RW n %1 -> RW p %1 -> Int -> a p -> RW n
    write_method rwn' rwp i v = writeUA rwn' rwp as i v

-- TODO: bound checking, both of `i`, and in the derived methods.
-- TODO: a version for read-only
slice :: forall n a. RW n %1 -> Slice a n -> Int -> Exists (Par (RW' (Slice a)) :*: (Par RW'' :-> RW n))
slice rwn as i = Ex @_ @'(n,n) $ P
    (PP
     (RW' unsafeMkRW (UnsafeMkSlice { borrow_method = borrow_method as, write_method = write_method as }))
     (RW' unsafeMkRW (UnsafeMkSlice { borrow_method = (\r j -> borrow_method as r (i+j)), write_method = (\r r' j v -> write_method as r r' (i+j) v) })))
    (A $ \(PP (RW (UnsafeMkRead,UnsafeMkWrite)) (RW (UnsafeMkRead,UnsafeMkWrite))) -> rwn)

-- TODO: a version for read-only
sliceDeep :: forall n a. RW n %1 -> Slice a n -> (forall p. RW p %1 -> a p -> Exists (Par (RW' a) :*: (Par RW'' :-> RW p))) -> Exists (Par (RW' (Slice a)) :*: (Par RW'' :-> RW n))
sliceDeep rwn as slc = Ex @_ @' (n,n) $ P
  (PP
    (RW' unsafeMkRW (UnsafeMkSlice
                     { borrow_method = \rwn' i -> Array.do
                          (Ex (P (RW' rwa a) (A release_a))) <- borrow_method as rwn' i
                          (Ex (P (PP l (RW' rwr _)) (A release_rl))) <- slc rwa a
                          Ex (P l (A (\(RW rwl') -> release_a (RW (release_rl (PP (RW rwl') (RW rwr)))))))
                     , write_method = error "I don't think it makes sense to write directly in a deep slice. Is there a way to prevent this statically?" }))
    (RW' unsafeMkRW (UnsafeMkSlice
                     { borrow_method = \rwn' i -> Array.do
                          (Ex (P (RW' rwa a) (A release_a))) <- borrow_method as rwn' i
                          (Ex (P (PP (RW' rwl _) r) (A release_rl))) <- slc rwa a
                          Ex (P r (A (\(RW rwr') -> release_a (RW (release_rl (PP (RW rwl) (RW rwr')))))))
                     , write_method = error "I don't think it makes sense to write directly in a deep slice. Is there a way to prevent this statically?" }))
  )
  (A $ \(PP (RW (UnsafeMkRead,UnsafeMkWrite)) (RW (UnsafeMkRead,UnsafeMkWrite))) -> rwn)

borrowDeep :: forall n a b. RW n %1 -> Slice a n -> (forall p. RW p %1 -> a p -> Exists (RW' b :*: (RW'' :-> RW p))) -> Exists (RW' (Slice b) :*: (RW'' :-> RW n))
borrowDeep rwn as brw = Ex @_ @_ $ P
  (RW' unsafeMkRW (UnsafeMkSlice
                  { borrow_method = \rwn' i -> Array.do
                    (Ex (P (RW' rwa a) (A release_a))) <- borrow_method as rwn' i
                    (Ex (P (RW' rwb b) (A release_b))) <- brw rwa a
                    Ex (P (RW' rwb b) (A $ \(RW rwb') -> release_a (RW (release_b (RW rwb')))))
                  , write_method = error "It doesn't even make sens to write when the inner arrays have been sliced"
                  }))
  (A $ \(RW (UnsafeMkRead, UnsafeMkWrite)) -> rwn)

-------------------------------------------------------------------------------
--
-- Matrices
--
-------------------------------------------------------------------------------

-- | Let's assume that a matrix is an array of columns
newtype Matrix a n = MkMatrix (UArray (UArray (Val a)) n)

blockify :: RW n %1 -> Matrix a n -> Exists (RW' (BMatrix a) :*: (RW'' :-> RW n))
blockify rwm (MkMatrix m) = Array.do
  (Ex (P (RW' rwm' m') (A release_m'))) <- fullSlice rwm m
  (Ex (P (RW' rwm'' m'') (A release_m''))) <- borrowDeep rwm' m' fullSlice
  Ex (P (RW' rwm'' (MkBMatrix m'')) (A (\rwm''' -> release_m' (RW (release_m'' rwm''')))))

-- | `B` stands for “block”. A 'BMatrix' can be sliced, but in exchange a
-- 'BMatrix' has a lifetime.
newtype BMatrix a n = MkBMatrix (Slice (Slice (Val a)) n)

num_col :: Read n %1 -> BMatrix a n -> (Read n , Ur Int)
num_col = error "TODO"

num_row :: Read n %1 -> BMatrix a n -> (Read n , Ur Int)
num_row = error "TODO"

-- | Slice a matrix into two set of columns, splitting rows in two.
sliceHMatrix :: RW n %1 -> BMatrix a n -> Int -> Exists ((Par (RW' (BMatrix a))):*: ((Par RW'') :-> RW n))
sliceHMatrix rwm (MkBMatrix m) col_num = Array.do
  (Ex (P (PP (RW' rwl l) (RW' rwr r)) (A release))) <- slice rwm m col_num
  Ex (P (PP (RW' rwl (MkBMatrix l)) (RW' rwr (MkBMatrix r))) (A release))

-- | Slice a matrix into two set of rows, splitting columns in two.
sliceVMatrix :: RW n %1 -> BMatrix a n -> Int -> Exists ((Par (RW' (BMatrix a))):*: ((Par RW'') :-> RW n))
sliceVMatrix rwm (MkBMatrix m) row_num = Array.do
  (Ex (P (PP (RW' rwl l) (RW' rwr r)) (A release))) <- sliceDeep rwm m (\rw col -> slice rw col row_num)
  Ex (P (PP (RW' rwl (MkBMatrix l)) (RW' rwr (MkBMatrix r))) (A release))

-- sliceHMatrixR :: Read n %1 -> Matrix a n -> Int -> Exists ((Par (Read' (Matrix a))):*: ((Par Read) :-> Read n))
-- sliceHMatrixR = error "TODO"

-- sliceVMatrixR :: Read n %1 -> Matrix a n -> Int -> Exists ((Par (Read' (Matrix a))):*: ((Par Read) :-> Read n))
-- sliceVMatrixR = error "TODO"

writeBMatrix :: RW n %1 -> BMatrix a n -> Int -> Int -> a -> RW n
writeBMatrix rwm (MkBMatrix m) row_num col_num a = Array.do
  (Ex (P (RW' rwc c) (A release_c))) <- borrowSlice rwm m col_num
  rwc <- writeSlice rwc rwVal c row_num (MkVal a)
  release_c (RW rwc)

readBMatrix :: Read n %1 -> BMatrix a n -> Int -> Int -> (Read n, Ur a)
readBMatrix = error "TODO"
  -- sketch: borrow -> borrow -> read the Val

-- | X = X+A
writePlusBMatrix :: Num a => RW n %1 -> BMatrix a n -> Int -> Int -> a -> RW n
writePlusBMatrix (rx, wx) x i j a = Array.do
  (rx, Ur b) <- readBMatrix rx x i j
  writeBMatrix (rx, wx) x i j (b+a)

-- -- | X = X*A
-- mulMatrixWith :: RW n %1 -> Read p %1 -> Matrix a n -> Matrix a p -> (RW n, Read p)
-- mulMatrixWith = error "TODO"

-- -- | X = X+YZ
addMulMatrixWith :: forall n p q a. Num a => RW n %1 -> Read p %1 -> Read q %1 -> BMatrix a n -> BMatrix a p -> BMatrix a q -> (RW n, Read p, Read q)
addMulMatrixWith rwx ry rz x y z = Array.do
  (ry, Ur n) <- num_row ry y
  (ry, Ur p) <- num_col ry y
  (rz, Ur m) <- num_col rz z -- A better implementation would check that p == num_row z0
  let
    -- It could all be done by blocks too, if it's better.
    rows :: RW n %1 -> Read p %1 -> Read q %1 -> Int -> (RW n, Read p, Read q)
    rows rwx' ry' rz' i =
      if i == n then (rwx', ry', rz')
      else Array.do
        let
          cols :: RW n %1 -> Read p %1 -> Read q %1 -> Int -> (RW n, Read p, Read q)
          cols rwx'' ry'' rz'' j =
            if j == m then (rwx'', ry'', rz'')
            else Array.do
              let
                go :: RW n %1 -> Read p %1 -> Read q %1 -> Int -> (RW n, Read p, Read q)
                go rwx''' ry''' rz''' k =
                  if k == p then (rwx''', ry''', rz''')
                  else Array.do
                    (ry''', Ur a) <- readBMatrix ry''' y i k
                    (rz''', Ur b) <- readBMatrix rz''' z k j
                    rwx''' <- writePlusBMatrix rwx''' x i j (a * b)
                    go rwx''' ry''' rz''' (k+1)
              (rwx'', ry'', rz'') <- go rwx'' ry'' rz'' 0
              cols rwx'' ry'' rz'' (j+1)
        (rwx', ry', rz') <- cols rwx' ry' rz' 0
        rows rwx' ry' rz' (i+1)
  rows rwx ry rz 0
