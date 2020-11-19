% -*- latex -*-

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
%format .<= = "\RLolly"
%format IOL = "IO_L"

%%%%%%%%%%%%%%%%% /lhs2tex %%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%% Editing marks %%%%%%%%%%%%%%%%%

  \usepackage{xargs}
  \usepackage[colorinlistoftodos,prependcaption,textsize=tiny]{todonotes}
  % ^^ Need for pgfsyspdfmark apparently?
  \ifx\noeditingmarks\undefined
      %\setlength{\marginparwidth}{1.2cm} % A size that matches the new PACMPL format
      \newcommand{\Red}[1]{{\color{red}{#1}}}
      \newcommand{\newaudit}[1]{{\color{blue}{#1}}}
      \newcommand{\note}[1]{{\color{blue}{\begin{itemize} \item {#1} \end{itemize}}}}
      \newenvironment{alt}{\color{red}}{}

      \newcommandx{\jp}[2][1=]{\todo[linecolor=purple,backgroundcolor=purple!25,bordercolor=purple,#1]{#2}}
      
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
  \newcommand{\aand}{\&}
  \DeclareMathOperator*{\bigaand}{\vcenter{\hbox{\Large\&}}}
  \newcommand{\lollycirc}{\raisebox{-0.2ex}{\scalebox{1.4}{$\circ$}}}
  \newcommand{\Lolly}{\mathop{=\!\!\!{\lollycirc}}}
  \newcommand{\RLolly}{\mathop{\lollycirc\!\!\!=}}
  \newcommand{\subst}[2]{[#1]#2}
  \newcommand{\sby}[2]{#1 ↦ #2}
  \newcommand{\vdashi}{⊢_{\mathsf{i}}}

  % language keywords
  \newcommand{\keyword}[1]{\mathbf{#1}}
  \newcommand{\klet}{\keyword{let}}
  \newcommand{\kcase}{\keyword{case}}
  \newcommand{\kwith}{\keyword{with}}
  \newcommand{\kunpack}{\keyword{unpack}}
  \newcommand{\kin}{\keyword{in}}
  \newcommand{\kof}{\keyword{of}}

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
\info{I'm assuming that we will need a $\aand$ connective. It's probably
  best in the declarative part of the system anyway, even if the
  algorithmic parts decides to do away with them. Though it's worth
  noting that the declarative system may not need the $\aand$
  connective at all. So maybe we can get rid if it. I suppose it's
  similar to how there is no implicational constraints in the
  declarative system except those coming from axioms.}

See Fig 3, p14 of OutsideIn\cite{OutsideIn}.

\unsure{It's a tad trivial, but I wonder why the calligraphic-font Q is different here than in the OutsideIn paper}

The calligraphic $\cscheme{Q}$ is like $Q$ but it has type-class axioms (instances from the top-level).
(Possibly we will drop these altogether.)
\begin{displaymath}
  \begin{array}{l}
    Q ⊩ Q \\
    \cscheme{Q_1} ⊩ Q_2 \quad\mathrm{and}\quad \cscheme{Q}_2 ⊗ Q_2 ⊩ Q_3 \quad\mathrm{then}\quad \cscheme{Q_1} ⊗ \cscheme{Q_2} ⊩ Q_3 \\
    \cscheme{Q_1} ⊩ Q_1 \quad\mathrm{and}\quad \cscheme{Q}_2 ⊩ Q_2 \quad\mathrm{then}\quad \cscheme{Q_1} ⊗ \cscheme{Q_2} ⊩ Q_1 ⊗ Q_2 \\
    \cscheme{Q} \aand Q ⊩ Q \\
    \cscheme{Q} ⊩ Q_1 \quad\mathrm{and}\quad \cscheme{Q} ⊩ Q_2 \quad\mathrm{then}\quad \cscheme{Q} \aand \cscheme{Q_2} ⊩ Q_1 ⊗ Q_2 \\
  \end{array}
\end{displaymath}

There are 3 rules about conjunction in OutsideIn, which translate to only 5 rules here. I think these are exhaustive.

\inconsistent{Last rule is bogus, but
Maybe $\&$-conjunctions can be C-constraints, and be eliminated before
they are given to the simplifier (therefore may not need to be
specified in the subsumption relation)}

\newpage

\section{The declarative system}
\change{Based on
  \href{https://github.com/tweag/linear-constraints/issues/13}{\#13}.}
\info{We will probably need a linear (thin) arrow in the system:
  when generating a packed existential with linear constraints inside,
  the pack needs to be treated linearly. This implies handling $Γ$
  linearly, but I(Arnaud) haven't done so yet, for the sake of simplicity.}
\unsure{I think $\kunpack$ should pack both existential variables and
  linear constraint: they go well together. This is not how Csongor
  designed it, originally, but it probably makes more sense.}

See Fig 10, p25 of OutsideIn\cite{OutsideIn}.

Main differences:
\begin{itemize}
\item $\kcase$ doesn't have GADTs
\item $\klet$ is generalised over all linear constraints.
\item $\kwith$ forces the consumption of constraints. It behaves like
  the let of InsideOut
\item Existential packs are our only GADT. They have a single
  constructor, pattern-matched over by $\kunpack$.
\end{itemize}
\improvement{We also want let with a signature. For the sake of completeness}
\begin{mathpar}
  \inferrule
    {(x : ∀\overline{a}. Q_1 \Lolly υ) ∈ Γ\\
     Q ⊩ \subst{\overline{\sby{a}{τ}}}{Q_1}}
   { Q;Γ ⊢  x : \subst{\overline{\sby{a}{τ}}}{υ}}\text{var}

   \inferrule
   {Q;Γ, (x{:}τ₁) ⊢ e : τ₂}
   {Q;Γ ⊢ λx.e : τ₁ ⟶ τ₂}\text{abs}

   \inferrule
   {Q₁;Γ ⊢ e₁ : τ₁ ⟶ τ \\ Q₂;Γ ⊢ e₂ : τ₁ \\ Q ⊩ Q₁ ⊗ Q₂ }
   {Q;Γ ⊢ e₁\,e₂ : τ}\text{app}

   \inferrule
   {Q'₁;Γ ⊢ e₁ : ∃\overline{a}. 𝜏₁ \RLolly Q₁ \\
     \textrm{freshness condition on }\overline{a}\\
     Q'₂⊗Q₁; Γ, x{:}τ₁ ⊩ e₂ : τ\\
     Q ⊩ Q'₁⊗Q'₂}
   {Q;Γ ⊢ \kunpack~x = e₁~\kin~e₂ : 𝜏}\text{unpack}

   \inferrule
   {Q'₁;Γ ⊢ e₁ : 𝜏₁ \\
     Q'₂; Γ, x{:}τ₁ ⊩ e₂ : τ\\
     Q ⊩ Q'₁⊗Q'₂}
   {Q;Γ ⊢ \kwith~x = e₁~\kin~e₂ : 𝜏}\text{with}

   \inferrule
   {Q'₁,Q₁; Γ ⊢ e₁ : 𝜏₁ \\
     Q'₂; Γ, x{:}Q₁ \Lolly τ₁ ⊩ e₂ : τ\\
     Q ⊩ Q'₁⊗Q'₂}
   {Q;Γ ⊢ \klet~x = e₁~\kin~e₂ : 𝜏}\text{let}

   \inferrule
   { Q;Γ ⊢ e : T\,\overline{τ} \\
     Kᵢ : ∀\overline{a}. \overline{υᵢ} ⟶ T\,\overline{a}\\
     Q; Γ, \overline{xᵢ:\subst{\overline{\sby{a}{τ}}}{υᵢ}} ⊢ uᵢ : τᵢ
   }
   {Q;Γ ⊢ \kcase~e~\kof \{ \overline{Kᵢ\,\overline{xᵢ} ⟶ eᵢ} \}}\text{case}
\end{mathpar}

\info{No substitution on $Q_1$ in the $\kunpack$ rule, because there is
  only existential quantification.}

\newpage

\section{The algorithmic system}



See Fig.13, p39 of OutsideIn~\cite{OutsideIn} \unsure{In this section,
  again, $Γ$ is treated intuitionistically where it should probably be
  linear.}  \unsure{For simplicity, I(Arnaud) assume that the data
  types are only constructors. That is, the entire GADTiness of the
  system is in $∃\overline{a}. τ \RLolly Q$ and deconstructed with
  $\kunpack$. I think that we don't need to drop this assumption. It
  does generalise straightforwardly to a full GADT system}

\unsure{It's actually not terribly easy to write the abstraction rule
  without equality constraint generation. I've just written it wrong
  for now, we can fix later, it's not particularly urgent. In fact,
  the whole treatment of unification is a bit sloppy (in particular
  unification should affect emitted constraints).}
\unsure{Todo: the rule for a constraint-generalising signatureless
  let}
\improvement{Rule for with}
\improvement{We also want let with a signature. There are two rules in
  OutsideIn: when the signature is monomorphic, and when it's
  polymorphic. Maybe we don't care about this distinction all that
  much.}
\improvement{In the unpack rule, we want $e₁$'s type to only unify
  with an existential type, not necessarily be inferred as such.}
\unsure{What variables must be existentially quantified over in the
  unpack rules? This is probably affected by the fact that we don't
  have equality constraints in this system.}
\begin{mathpar}
  \inferrule
  { \overline{α}\textrm{ fresh} \\
    (x{:}∀\overline{a}.\, Q₁ \Lolly τ₁) ∈ Γ }
  {Γ \vdashi x : \subst{\overline{\sby{a}{α}}}{τ₁} \leadsto
    \subst{\overline{\sby{a}{α}}}{Q₁}}\text{var}

  \inferrule
  { α\textrm{ fresh} \\
    Γ, x{:}a \vdashi e : τ \leadsto C}
  { Γ \vdashi λx.\,e : α ⟶ τ \leadsto C }\text{abs}

  \inferrule
  { Γ \vdashi e₁ : τ₁ \leadsto C₁ \\
    Γ \vdashi e₂ : τ₂ \leadsto C₂ \\
    τ₁\textrm{ unifies with }τ₂⟶α\textrm{ and yield } α≔τ
  }
  {Γ \vdashi e₁\,e₂ : τ \leadsto C₁⊗C₂ }\text{app}

  \inferrule
  { Γ \vdashi e : σ \leadsto C \\ \overline{γ}\textrm{ fresh}\\
    K_i : ∀\overline{a}. \overline{υᵢ} ⟶ T\,\overline{a} \\
    Γ,\overline{xᵢ{:}\subst{\overline{\sby{a}{γ}}}{υᵢ}} \vdashi e_i : τᵢ \leadsto Cᵢ\\
    \textrm{unification of the }τᵢ\textrm{ yields }τ }
  {Γ \vdashi \kcase~e~\kof \{ \overline{Kᵢ\,\overline{xᵢ} ⟶ eᵢ} \} : τ
    \leadsto C⊗\bigaand Cᵢ}\text{case}

  \inferrule
  { Γ \vdashi e₁ : ∃\overline{a}.\,τ₁\RLolly Q₁ \leadsto C₁ \\
    \overline{a}\textrm{ fresh}\\
    Γ, x{:}τ₁ \vdashi e₂ : τ \leadsto C₂}
  {Γ \vdashi \kunpack~x = e₁~\kin~e₂ : τ
    \leadsto C₁⊗∃….\,Q₁ ⊃ C₂}\text{unpack}
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
