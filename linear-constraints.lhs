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
\usepackage{mathpartir}

%%%%%%%%%%%%%%%%% lhs2tex %%%%%%%%%%%%%%%%%


%include polycode.fmt
%format ->. = "⊸"
%format =>. = "\Lolly"
%format .<= = "\mathop{\circ\!\!\!=}"
%format IOL = "IO_L"

%%%%%%%%%%%%%%%%% /lhs2tex %%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%% Editing marks %%%%%%%%%%%%%%%%%

  \usepackage{xargs}
  \usepackage[colorinlistoftodos,prependcaption,textsize=tiny]{todonotes}
  % ^^ Need for pgfsyspdfmark apparently?
  \ifx\noeditingmarks\undefined
      \setlength{\marginparwidth}{1.2cm} % Here's a size that matches the new PACMPL format -RRN
      \newcommand{\Red}[1]{{\color{red}{#1}}}
      \newcommand{\newaudit}[1]{{\color{blue}{#1}}}
      \newcommand{\note}[1]{{\color{blue}{\begin{itemize} \item {#1} \end{itemize}}}}
      \newenvironment{alt}{\color{red}}{}

      \newcommandx{\unsure}[2][1=]{\todo[linecolor=red,backgroundcolor=red!25,bordercolor=red,#1]{#2}}
      \newcommandx{\info}[2][1=]{\todo[linecolor=green,backgroundcolor=green!25,bordercolor=green,#1]{#2}}
      \newcommandx{\change}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=blue,#1]{#2}}
      \newcommandx{\inconsistent}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=red,#1]{#2}}
      \newcommandx{\critical}[2][1=]{\todo[linecolor=blue,backgroundcolor=blue!25,bordercolor=red,#1]{#2}}
      \newcommand{\improvement}[1]{\todo[linecolor=pink,backgroundcolor=pink!25,bordercolor=pink]{#1}}
      \newcommandx{\resolved}[2][1=]{\todo[linecolor=OliveGreen,backgroundcolor=OliveGreen!25,bordercolor=OliveGreen,#1]{#2}} % use this to mark a resolved question
  \else
  %    \newcommand{\Red}[1]{#1}
      \newcommand{\Red}[1]{{\color{red}{#1}}}
      \newcommand{\newaudit}[1]{#1}
      \newcommand{\note}[1]{}
      \newenvironment{alt}{}{}
  %    \renewcommand\todo[2]{}
      \newcommand{\unsure}[2]{}
      \newcommand{\info}[2]{}
      \newcommand{\change}[2]{}
      \newcommand{\inconsistent}[2]{}
      \newcommand{\critical}[2]{}
      \newcommand{\improvement}[1]{}
      \newcommand{\resolved}[2]{}
  \fi

%%%%%%%%%%%%%%%%% /Editing marks %%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%% Domain-specific macros %%%%%%%%%%%%%%%%%

  \newcommand{\cscheme}[1]{\mathcal{#1}}
  \newcommand{\with}{\&}
  \newcommand{\Lolly}{\mathop{=\!\!\!\circ}}
  \newcommand{\subst}[2]{[#1]#2}
  \newcommand{\sby}[2]{#1 ↦ #2}

%%%%%%%%%%%%%%%%% /Domain-specific macros %%%%%%%%%%%%%%%%%

\begin{document}

\title{Linear Constraints}

\author{Jean-Philippe Bernardy, Richard Eisenberg, Csongor Kiss, Arnaud Spiwack}
\date{}

\maketitle

\section*{Introduction}
\info{There is an Appendix section with unorganised thoughts and
  examples.}

\newpage

\section{Constraint entailment relation}
\info{I'm assuming that we will need a $\with$ connective. It's probably
  best in the declarative part of the system anyway, even if the
  algorithmic parts decides to do away with them. Though it's worth
  noting that the declarative system may not need the $\with$
  connective at all. So maybe we can get rid if it. I suppose it's
  similar to how there is no implicational constraints in the
  declarative system except those coming from axioms.}

See Fig 3, p14 of OutsideIn\cite{OutsideIn}.

\unsure{It's a tad trivial, but I wonder why the calligraphic-font Q is different here than in the OutsideIn paper}

\begin{displaymath}
  \begin{array}{l}
    Q ⊩ Q \\
    \cscheme{Q_1} ⊩ Q_2 \quad\mathrm{and}\quad \cscheme{Q}_2 ⊗ Q_2 ⊩ Q_3 \quad\mathrm{then}\quad \cscheme{Q_1} ⊗ \cscheme{Q_2} ⊩ Q_3 \\
    \cscheme{Q_1} ⊩ Q_1 \quad\mathrm{and}\quad \cscheme{Q}_2 ⊩ Q_2 \quad\mathrm{then}\quad \cscheme{Q_1} ⊗ \cscheme{Q_2} ⊩ Q_1 ⊗ Q_2 \\
    \cscheme{Q} \with Q ⊩ Q \\
    \cscheme{Q} ⊩ Q_1 \quad\mathrm{and}\quad \cscheme{Q} ⊩ Q_2 \quad\mathrm{then}\quad \cscheme{Q} \with \cscheme{Q_2} ⊩ Q_1 ⊗ Q_2 \\
  \end{array}
\end{displaymath}

There are 3 rules about conjunction in OutsideIn, which translate to only 5 rules here. I think these are exhaustive.

\newpage

\section{The declarative system}
\change{Based on
  \href{https://github.com/tweag/linear-constraints/issues/13}{\#13}.}
\info{We will probably need a linear (thin) arrow in the system:
  when generating a packed existential with linear constraints inside,
  the pack needs to be treated linearly.}

See Fig 10, p25 of OutsideIn\cite{OutsideIn}.

\begin{mathpar}
  \inferrule
    {(x : ∀\overline{a}. Q_1 \Lolly υ) ∈ Γ\\
     Q ⊩ \subst{\overline{\sby{a}{τ}}}{Q_1}}
    { Q;Γ ⊢  x : \subst{\overline{\sby{a}{τ}}}{υ}}\text{var}
\end{mathpar}

\newpage

\appendix

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
