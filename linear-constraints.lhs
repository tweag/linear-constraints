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

\documentclass[natbib=false]{acmart}

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
%if style == poly
%format ->. = "⊸"
%format =>. = "\Lolly"
%format .<= = "\RLolly"
%format IOL = "IO_L"
%format . = "."
%format exists = "\exists"
%format forall = "\forall"
%endif

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
  \newcommand{\kpack}{\keyword{pack}}
  \newcommand{\kunpack}{\keyword{unpack}}
  \newcommand{\kin}{\keyword{in}}
  \newcommand{\kof}{\keyword{of}}

%%%%%%%%%%%%%%%%% /Domain-specific macros %%%%%%%%%%%%%%%%%
\acmConference[WOODSTOCK'97]{ACM Woodstock conference}{July 1997}{El
  Paso, Texas USA} 
\acmYear{1997}
\copyrightyear{2016}

\acmPrice{15.00}

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
    \cscheme{Q} ⊩ Q_1 \quad\mathrm{and}\quad \cscheme{Q} ⊩ Q_2 \quad\mathrm{then}\quad \cscheme{Q} ⊩ Q_1 \aand Q_2 \\
  \end{array}
\end{displaymath}

There are 3 rules about conjunction in OutsideIn, which translate to only 5 rules here. I think these are exhaustive.

\unsure{Maybe $\&$-conjunctions can be C-constraints, and be eliminated before
they are given to the simplifier (therefore may not need to be
specified in the subsumption relation)

[Arnaud]: I think we may be able to take a cue from focusing here: if
a combinator is ``asynchronous'' then it need not appear in the
subsumption rule (at least not in the simplifier) whereas if the
combinator is ``synchronous'', then it does}

\newpage

\section{The declarative system}
\change{Based on
  \href{https://github.com/tweag/linear-constraints/issues/13}{\#13}.}
\info{We will certainly need a linear (thin) arrow in the system:
  when generating a packed existential with linear constraints inside,
  the pack needs to be treated linearly. This implies handling $Γ$
  linearly, but I(Arnaud) haven't done so yet, for the sake of
  simplicity. An interesting feature of linearity is that promotion
  can only happens when both the variables and the constraints are
  unrestricted. This will cause $\kpack$ to return a linear quantity. }
%
\jp{It's very important to explain in detail that linear constraints
  (as linear values) can never escape to omega contexts.

  But then, don't we have to give linear types to composition
  combinators? I am confused here.  }

%
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
   {Q'₁;Γ ⊢ e₁ : ∃\overline{a}. τ₁ \RLolly Q₁ \\
     \textrm{freshness condition on }\overline{a}\\
     Q'₂⊗Q₁; Γ, x{:}τ₁ ⊩ e₂ : τ\\
     Q ⊩ Q'₁⊗Q'₂}
   {Q;Γ ⊢ \kunpack~x = e₁~\kin~e₂ : τ}\text{unpack}

   \inferrule
   { Q₁; Γ ⊢ e₁ : τ₁ \\
     Q; Γ, x{:}Q₁ \Lolly τ₁ ⊩ e₂ : τ }
   {Q;Γ ⊢ \klet~x = e₁~\kin~e₂ : τ}\text{let}

   \inferrule
   { Q₁;Γ ⊢ e : T\,\overline{τ} \\
     Kᵢ : ∀\overline{a}. \overline{υᵢ} ⟶ T\,\overline{a}\\
     Q₂; Γ, \overline{xᵢ:\subst{\overline{\sby{a}{τ}}}{υᵢ}} ⊢ uᵢ : τᵢ\\
     Q⊩Q₁⊗Q₂
   }
   {Q;Γ ⊢ \kcase~e~\kof \{ \overline{Kᵢ\,\overline{xᵢ} ⟶ eᵢ} \}}\text{case}
\end{mathpar}

\info{No substitution on $Q_1$ in the $\kunpack$ rule, because there is
  only existential quantification.}

\jp{Regarding pack/unpack. Treating them as primitive implies that we will define linear constraints inside data types as Pack/Unpack.}

\section{$\klet$ should be generalised}

The let rule infers a qualified type for the bound variable, by generalising
over all the linear constraints appearing in the bound expression. This is in
stark contrast with OutsideIn's strategy of inferring fully monomorphic types
for let expressions. So why not follow the established tradition and also infer
monomorphic types when linear constraints are involved? Since the let binder is
unrestricted, the variable $x$ may be used multiple times (or none at all). This
means that the let \emph{must not consume any linear constraints}. \change{which
means that if we also add linear lets to the language, then those can consume
linear constraints. But I (Csongor) don't think linear lets will be necessary?}

To illustrate the practical necessity of the let generalisation strategy,
consider the following file handling API:

\begin{code}
newFile :: exists f. IO (File f .<= Open f)
writeFile :: Open f =>. File f -> String -> IO (() .<= Open f)
closeFile :: Open f =>. File f -> IO ()
\end{code}

The |newFile| function creates a file and returns a file handle |File f|,
together with a linear constraint witnessing that the file |f| is open (note
that |f| is existentially quantified). |writeFile| writes a string to an open
file and keeps it open. Finally, |closeFile| closes the file and consumes the
|Open f| constraint.

Now consider the following program:

\begin{code}
readBad :: IO ()
readBad = do
  file <- newFile
  writeFile file "hello"
  let x = closeFile file
  return ()
\end{code}

This program creates a new file, writes the string |"hello"| to it, then
returns. Even though the |closeFile file| action is assigned to a variable, the
action itself is never invoked, and the file remains open. The fixed version
follows:

\begin{code}
readGood :: IO ()
readGood = do
  file <- newFile
  writeFile file "hello"
  let x = closeFile file
  x
\end{code}

Here, |x| is actually executed, thus the file is closed before the function
returns. The type of |x| in both cases is |Open f0 =>. IO ()| (with |f0| the
existential variable created by |newFile|). Happily, |readBad| gets rejected
because the |Open f0| constraint doesn't get consumed before the function returns.

Unlike traditional let-generalisation, this behaviour can not be overridden with
a signature, so writing |x :: IO ()| is rejected. \change{We don't have a rule
for let with a signature yet, but it will have to be this way.}

\subsection{Comparison with OutsideIn}

So far we have argued that linear constraints should be quantified over in let
bindings. But how does this fit into the OutsideIn constraint solver, the type
inference framework employed by GHC?  In~\cite{OutsideIn}, the authors carefully
consider various different generalisation strategies, each with different
tradeoffs, before reaching the conclusion that no generalisation is the most
ergonomic option.

Here is a summary of the different criteria:

\begin{description}
  \item[Equalities]
        OutsideIn never generalises over equality constraints. Doing
        so would result in very large constraints, resulting in ergonomic and
        performance penalties. In our system, equality constraints are always
        unrestricted, so the issues around consumption explained above do not
        apply to them. Thus, there is no need to generalise over equality
        constraints in our system.
  \item[Class constraints]
        OutsideIn never generalises over class constraints. A downside of
        generalising is that type errors are delayed to call sites when a
        constraint can not be solved. In the case of linear constraints, this is
        the desired behaviour, since whether the constraint can be solved depends
        on whether it is available at the call site, which might differ from
        whether it is available at the definition site.
  \item[Type variables]
        OutsideIn makes the observation that if a type variable is generalised,
        then so must be all the constraints that mention that variable (otherwise
        principal types are lost). Because constraints are not generalised, the
        algorithm opts to also not generalise type variables. A possibility not
        considered in~\cite{OutsideIn} is generalising only the constraint, but
        not the type variables mentioned in it. This is the path we take: type
        variables are not quantified over, but (linear) constraints are. This is
        a sensible option in our setting because it still allows deferring
        constraint solving to use sites, without deviating too much from GHC's
        existing strategy.
\end{description}

To summarise, the generalisation strategy in let bindings is to always
generalise over linear constraints, but keep type variables monomorphic and never
quantify over nonlinear constraints (which includes all equality constraints).
This is a conservative extension of OutsideIn.

\subsection{Maybe we need to be more careful?}

As I (Csongor) wrote the above example, I realised that the example API might
not be sufficient. For example,

\begin{code}
readBad2 = do
  file <- newFile
  writeFile file "hello"
  const (return ()) (closeFile file)
\end{code}

here the file handle is not closed, but according to the App rule, the |Open f0|
constrant is consumed by the application to |const|. The issue here is that we
want to actually ensure that |closeFile| gets \emph{executed}, so maybe a better
interface would be

\begin{code}
newFile :: exists f. IO (File f .<= Open f)
writeFile :: File f -> String -> IO (Open f =>. () .<= Open f)
closeFile :: File f -> IO (Open f =>. ())
\end{code}

is there any other way to fix it? Maybe a linear constraint is only consumed in
an application to a linear function?\info{Arnaud: yes! consuming a
  linear constraints in a non-linear operation should be a type error,
  otherwise linear constraints would be unsound.}

\newpage

\section{Constraint generation}

See Fig.13, p39 of OutsideIn~\cite{OutsideIn} \unsure{In this section,
  again, $Γ$ is treated intuitionistically where it should probably be
  linear.}

In a full blown Haskell with linear constraints, there wouldn't be
linear equality constraints.\jp{Seems to suggest that we have linear
  equality constraints here? [Arnaud]: my poor phrasing, I meant to
  imply that we didn't have any equality constraints at all.}
That is, $a \sim b$\unsure{this notation
  hasn't been introduced, so if it makes the cut explain where it
  comes from} wouldn't appear to the left of a linear fat arrow. It's
not that linear equalities don't make sense, see for
instance~\cite{shulman2018linear} for a system which takes linear
equality seriously. However, the usual unification algorithms are
unsound for linear equalities, because they will gladly use the same
equality many times (or none-at-all). Haskell could, by some arbitrary
mean, reject equality constraints to the left of a linear fat arrow,
or it could simply refuse to do any solving with such equalities.

While it is possible that a future version of Haskell includes linear
equality constraints, automatic resolution of linear equality
constraints is beyond the scope of this article. Nor is it needed,
or even useful, for our use cases.
%
Thus, in general, no linear constraint can be used in, or influence in
any way, the unification of type meta variables to types.  As a
consequence, linear
%
constraints are fully orthogonal to type inference. Therefore, the
syntax-directed constraint generation system presented in this section
can legitimately assume that type inference is solved elsewhere;
contrary to~\cite{OutsideIn}, where type inference is mixed with
constraint generation. This separation of concern simplifies the
presentation significantly.\unsure{This paragraph is more wordy than
  it is clear, so let's not take it as an actual proposal for the
  explanation, I [Arnaud] merely wanted to record my thoughts}

\unsure{For simplicity, I(Arnaud) assume that the data
  types are only constructors. That is, the entire GADTiness of the
  system is in $∃\overline{a}. τ \RLolly Q$ and deconstructed with
  $\kunpack$. I think that we don't need to drop this assumption. It
  does generalise straightforwardly to a full GADT system}

\unsure{Todo: the rule for $\kpack$}
\unsure{Todo: the rule for a constraint-generalising signatureless
  let}
\improvement{We also want let with a signature. There are two rules in
  OutsideIn: when the signature is monomorphic, and when it's
  polymorphic. Maybe we don't care about this distinction all that
  much.}
\unsure{What variables must be existentially quantified over in the
  unpack rules? This is probably affected by the fact that we don't
  have equality constraints in this system. Maybe none? if we remove
  unification from our framework altogether.}
\unsure{The case rule, for an empty case, implies the existence of the
  typically annoying $⊤$. We will have to confront this.}
\unsure{We probably want the freshness condition on the $\kunpack$
  rule, though these variables are universal variables, not
  existentials.}
\begin{mathpar}
  \inferrule
  { (x{:}∀\overline{a}.\, Q₁ \Lolly τ₁) ∈ Γ }
  {Γ \vdashi x : \subst{\overline{\sby{a}{τ}}}{τ₁} \leadsto
    \subst{\overline{\sby{a}{τ}}}{Q₁}}\text{var}

  \inferrule
  { Γ, x{:}τ₀ \vdashi e : τ \leadsto C}
  { Γ \vdashi λx.\,e : α ⟶ τ \leadsto C }\text{abs}

  \inferrule
  { Γ \vdashi e₁ : τ₂⟶τ \leadsto C₁ \\
    Γ \vdashi e₂ : τ₂ \leadsto C₂
  }
  {Γ \vdashi e₁\,e₂ : τ \leadsto C₁⊗C₂ }\text{app}

  \inferrule
  { Γ \vdashi e : T\,\overline{σ} \leadsto C \\
    K_i : ∀\overline{a}. \overline{υᵢ} ⟶ T\,\overline{a} \\
    Γ,\overline{xᵢ{:}\subst{\overline{\sby{a}{σ}}}{υᵢ}} \vdashi e_i : τ \leadsto Cᵢ}
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

\section{Constraint solver}
\label{sec:constraint-solver}

Various recipes are given
by~\cite{resource-management-for-ll-proof-search}.
\info{The first presentation of returning output context that I could
  find is~\cite{hh-ll}, but I
  find~\cite{resource-management-for-ll-proof-search} more
  informative.}
These recipes are phrased in a way which implies goal oriented
proof search, but they can be adapted \emph{mutatis mutandis} to GHC's
backtrackingless rewrite-based search.

The key points are
\begin{itemize}
\item Each rule return the remaining, unused (linear) hypotheses: the
  \emph{leftovers}.
\item To deal with $⊤$, remember that you've encountered a $⊤$ in a
  different branch. And let you spend any leftover back into a
  previous $⊤$
\item In~\cite{resource-management-for-ll-proof-search}, there is a
  third input context ($Ξ$), which represents a context which need to
  be used, and cannot be returned as leftovers. However, this is used
  to fail earlier in backtracking branches which are doomed to
  fail. It doesn't apply to our backtrackingless
  setting\unsure{[Arnaud]: I think.}
\end{itemize}

We can do pretty much like in OutsideIn: split the constraint between
flat constraints and non-flat constraints if we wish (but, this time,
non-flat constraint include $\aand$! so there will be significantly
more of them). Apply synchronous rules on non-flat constraint to retrieve flat
constraint, call the simplifier on them.

To be honest, we can even do one atomic constraint at a time, given
that we have no equality, hence our wanted can't interact (I [Arnaud]
think) but the details don't matter terribly.

\newpage

\section{Desugaring}
\label{sec:desugaring}

\jp{We must say something about operational semantics (especially for
  the Array example to make sense.). The linear constraint carries a
  token for ordering of operations. How is this token manipulated with the surface syntax?
  How it is represented in the operational semantics (presumably the
  linear constraints are translated to linear values)?

  [Arnaud]: My plan is to give the operational semantics in the form
  of a desugaring to the core calculus of the Linear Haskell paper.

}

Goal: describe transformations
\begin{enumerate}
\item Constraint generator + solver $\leadsto$ declarative system
\item declarative system $\leadsto$ $λ^q$
\end{enumerate}

\newpage

\section{Extensions}
\begin{itemize}
\item Like there are implicational and universally-quantified
  constraints in the left-hand side of fat arrows, we may want to have
  $\aand$ constraints on the left hand side of (linear) fat
  arrows. This falls in the Linear Hereditary Harrop fragment
  described, for instance, in~\cite{hh-ll}
  and~\cite{resource-management-for-ll-proof-search}. Hereditary
  Harrop is a natural extension of Horn clauses in proof search
  algorithms.
\end{itemize}

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

\jp{IMO the Rust terminology is more confusing than anything. (what is borrowPArray even doing?)

  I'd
  rather say that the RW capability is threaded using a linear token
  which is (semi-)implicitly passed around.

  Also, why is the |Own| class used nowhere?

}

\printbibliography

\end{document}
