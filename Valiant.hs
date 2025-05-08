{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Valiant where

import GHC.IOArray
import Control.Monad
import GHC.Types
import System.IO.Unsafe (unsafePerformIO)
import Prelude hiding (Read)
import Data.Functor.Const

-------------------------------------------------------------------------------
--
-- Linear types preliminaries for self-containedness
--
-------------------------------------------------------------------------------

data Ur a where {Ur :: a %Many -> Ur a}

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

newtype Ref a n = MkRef a
newtype UArray a n = UnsafeMkUArray (IOArray Int (Exists a))

data Read n = UnsafeMkRead
data Write n = UnsafeMkWrite
type RW n = (Read n, Write n)
unsafeMkRW = (UnsafeMkRead, UnsafeMkWrite)

-- | `SomeRW a = ∃n. RW n ⊗ a n`
data RW' a n where
  RW' :: RW n %1 -> a n %Many -> RW' a n

newtype RW'' n = RW (RW n)

newUArray :: Linearly %1 -> Int -> (Linearly %1 -> Int -> Exists (RW' a)) -> Exists (RW' (UArray a))
newUArray UnsafeMkLinearly lgth mk = unsafePerformIO $ do
  r <- newIOArray (0, lgth - 1) (error "uninitialised array element")
  forM_ [0 .. lgth - 1] $ \ i -> 
    case mk UnsafeMkLinearly i of
      (Ex (RW' _rw a)) -> writeIOArray r i (Ex a)
  return $ Ex (RW' unsafeMkRW (UnsafeMkUArray r))
{-# NOINLINE newUArray #-}

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

-- -- | Split out of Sliceable because GHC refuses to use it in kinds of associated
-- -- types otherwise. Unfortunate.
-- type SliceShapeIndex :: (Type -> Type) -> Type
-- type family SliceShapeIndex a :: Type

type Sliceable :: (Type -> Type) -> Constraint
class Sliceable a where
  type SliceIndex a :: Type
  type SliceArg a :: Type
  type SliceShape a :: Type -> Type

  fullSlice :: SliceIndex a
  sliceSlice :: SliceIndex a -> SliceArg a -> SliceShape a (SliceArg a)

-- type instance SliceShapeIndex (Ref a) = ()

instance Sliceable (Ref a) where
--   type SliceIndex (Ref a) = ()
--   type SliceArg (Ref a) = ()
--   type SliceShape (Ref a) = Id

--   fullSlice = ()
--   sliceSlice () = I $ MkRef ()

-- type instance SliceShapeIndex (UArray a) = (SliceShapeIndex a, SliceShapeIndex a)

instance Sliceable a => Sliceable (UArray a) where
  type SliceIndex (UArray a) = ((Int, Int), SliceIndex a)
  -- type SliceArg (UArray a) = (Int, SliceIndex a)
--   type SliceShape (UArray a) = Par (SliceShape a) (SliceShape a)

type Container :: forall (f :: Type -> Type) -> (i -> Type) -> f i -> Type
data family Container f

data instance Container (Const ()) a i = MkNone
data V2 a = V2 a a
type Fst2 :: V2 a -> a
type family Fst2 ab where
  Fst2 ('V2 a _) = a

type Snd2 :: V2 a -> a
type family Snd2 ab where
  Snd2 ('V2 _ b) = b
data instance Container V2 a i = MkP (a (Fst2 i)) (a (Snd2 i))

data Slice a n
  = UnsafeMkSlice (SliceIndex a) (a n)

mkSlice :: forall n a. Sliceable a => RW n %1 -> a n -> Exists (RW' (Slice a))
mkSlice (UnsafeMkRead, UnsafeMkWrite) a =
  Ex (RW' unsafeMkRW (UnsafeMkSlice (fullSlice @a) a))

borrowS :: forall n a. Sliceable a => RW n %1 -> Slice (UArray a) n -> Int -> Exists (RW' (Slice a) :*: (RW'' :-> RW n))
borrowS (UnsafeMkRead, UnsafeMkWrite) (UnsafeMkSlice ((l,h),bounds) as) i =
  if 0 <= i && i < h then
    case borrowUA unsafeMkRW as (i+l) of
      Ex (P (RW' (UnsafeMkRead, UnsafeMkWrite) a) (A release)) ->
        Ex (P (RW' unsafeMkRW (UnsafeMkSlice bounds a)) (A $ \cases (RW (UnsafeMkRead, UnsafeMkWrite)) -> release (RW unsafeMkRW)))
  else
    error "borrowS: index out of bounds"

sliceS :: forall n a. Sliceable a => RW n %1 -> Slice a n -> SliceArg a -> Exists (Container (SliceShape a) (RW' (Slice a)) :*: ((Container (SliceShape a) RW'') :-> RW n))
sliceS = _
