%if style == newcode
module LinearConstraints where

\begin{code}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

import Data.Kind (Constraint)
--import GHC.IO.Unsafe
import GHC.Base
\end{code}
%endif

% -*- latex -*-

\documentclass{article}

\usepackage[backend=biber,citestyle=authoryear,style=alphabetic]{biblatex}
\bibliography{bibliography}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{amssymb}
\usepackage{xcolor}
\usepackage{hyperref}
\hypersetup{
    colorlinks,
    linkcolor={red!50!black},
    citecolor={blue!50!black},
    urlcolor={blue!80!black}
  }
\usepackage{unicode-math}
\usepackage[plain]{fancyref}

%% Lhs2tex

%include polycode.fmt
%format ->. = "⊸"
%format =>. = "\mathop{=\!\!\!\circ}"
%format .<= = "\mathop{\circ\!\!\!=}"
%format IOL = "IO_L"

%% /lhs2tex

\begin{document}

\title{Linear Constraints}

\author{Krzysztof Gogolewski, Csongor Kiss, and Arnaud Spiwack}
\date{}

\maketitle

\section{Preamble from Csongor}

\begin{spec}
data a .<= c where
  Pack :: c =>. a -> a .<= c

data IOL c a = IOL {runIOL :: RealWorld -> (RealWorld, a .<= c)}
\end{spec}

If we bake the constraint into |IOL|, then we need to change \emph{both} |c| and |a|:
\begin{spec}
(>>=) :: IOL c a -> (c =>. a -> IOL d b) -> IOL d b
io_a >>= f = IOL $ \rw -> case runIOL io_a rw of
                            (rw', Pack a) -> runIOL (f a) rw'
\end{spec}


\section{Arnaud's motivating examples}

\subsection{Linear IO without the hassle (file handles)}

In Linear Haskell~\cite{LinearHaskell}

\begin{spec}
readTwoLines path = do
  h0 <- openFile path
  (h1, line1) <- readLine h0
  (h2, line2) <- readLine h1
  close h2
\end{spec}
API:
\begin{spec}
openFile  :: FilePath -> IOL Handle
close     :: Handle ⊸ IOL ()
readLine  :: Handle ⊸ IOL (Handle, String)
\end{spec}
With linear constraints, API:
\begin{spec}
openFile  :: FilePath -> IOL (Handle h .<= Open h)
close     :: Open h =>. Handle h -> IOL ()
readLine  :: Open h =>. Handle h -> IOL (String .<= Open h)
\end{spec}
The example become (remark: not the do-notation for the |IO| monad):
\begin{spec}
readTwoLines path = do
  h <- openFile path
  line1 <- readLine h
  line2 <- readLine h
  close h
\end{spec}

It looks exactly the same as without linear types. But you still get
an error for double-free and use-after-free usages.

\subsection{Ownership and so on…}

From the linear types paper:

\begin{spec}
  newMArray    :: (MArray a ⊸ Unrestricted b) ⊸ Unrestricted b
  writeMArray  :: MArray a ⊸ Int -> a -> MArray a
  freeze       :: MArray a ⊸ Unrestricted (Array a)
  readArray    :: Array a -> Int -> a
\end{spec}

In |writeArray|: we insert an unrestricted element |a ->|. Otherwise
we could do a linear type taboo:

\begin{spec}
unrestrict :: a ⊸ Unrestricted a
unrestrict x = case unrestrictArray x of
  Unrestricted arr -> readArray 0

unrestrictArray :: a ⊸ Unrestricted (Array a)
unrestrictArray x = newArray $ \marr ->
  freeze $
  writeMArray 0 x marr
\end{spec} % $ <- syntax highlighting bug

This is not ok if I want to make a multidimensional array (say an
|MArray (MArray a)|), which I would later freeze.

How could freeze look like for that use-case?

Something like

\begin{spec}
  freeze :: MArray a ⊸ (a ⊸ Unrestricted b) -> Unrestricted (Array b)
\end{spec}

But this is no longer $O(1)$ unless the compiler has special support
(like |Coercible|~\cite{citation_needed}).

The crux of the issue is that mutable arrays and immutable arrays have
distinct types, which me must convert.

Contrast with Rust, where there is a single type \verb+Vector+, and
freezing is simply
\verb+fn (vect : Vector<a>) : Rc<Vector<a>> -> { Rc<vect> }+ (check
syntax).

With linear constraints:

\begin{spec}
class Read n
class Write n
class Own n
type RW n = (Read n, Write n)
type O n = ()

data PArray (a :: * -> *) n -- Permission Array
type Array a = Frozen (PArray a)
data Frozen a where
  Freeze :: Read n => a n -> Frozen a
data Reading a where
  Read :: Read n =>. a n -> Reading a
data Borrowed a where
  Borrow :: RW n =>. a n -> Borrowed a
data Owned (a :: * -> *) where
  Move :: O n =>. a n -> Owned a

newPArray    :: (forall n. O n =>. PArray a n -> Unrestricted b) ⊸ Unrestricted b
  -- Alternatively: |(Owned (Parray a) ⊸ Unrestricted b) ⊸ Unrestricted b|
writePArray  :: (RW n, O p) =>. PArray a n -> Int -> a p -> Owned a .<= RW n
  -- Relinquishes the ownership of the |a p| arguments. Returns
  -- ownership of the old value
readPArray   :: Read n =>. PArray a n -> Int -> a n .<= Read n
borrowPArray
  :: RW n =>. Parray a n -> Int -> (Borrowed a ⊸ Unrestricted b) ⊸ Unrestricted b .<= RW n
freeze       :: O n =>. PArray a n -> Array a

readArray :: Array a -> Int -> Frozen a
readArray (Freeze arr) i = Freeze (readPArray arr i)
\end{spec}

\printbibliography

\end{document}
