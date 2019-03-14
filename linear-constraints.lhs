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
%format IOL = "IO_L"

%% /lhs2tex

\begin{document}

\title{Linear Constraints}

\author{Krzysztof Gogolewski, Csongor Kiss, and Arnaud Spiwack}
\date{}

\maketitle

\section{Arnaud's motivating examples}

\subsection{Linear IO without the hassle (file handles)}

In Linear Haskell~\cite{LinearHaskell}

\begin{code}
  readTwoLines path = do
    h0 <- openFile path
    (h1, line1) <- readLine h1
    (h2, line2) <- readLine h2
    close h2
\end{code}
API:
\begin{code}
  openFile  :: FilePath -> IOL Handle
  close     :: Handle ⊸ IOL ()
  readLine  :: Handle ⊸ IOL (Handle, String)
\end{code}
With linear constraints, API:
\begin{code}
  openFile  :: FilePath -> IOL (Handle h .<= Open h)
  close     :: Open h =>. Handle h -> IOL ()
  readLine  :: Open h =>. Handle h -> IOL (String .<= Open h)
\end{code}
The example become (remark: not the do-notation for the |IO| monad):
\begin{code}
  readTwoLines path = do
  h <- openFile path
  line1 <- readLine h
  line2 <- readLine h
  close h
\end{code}

It looks exactly the same as without linear types. But you still get
an error for double-free and use-after-free usages.

\subsection{Ownership and so on…}

TODO

\begin{itemize}
\item Array mutation \& freeze. But the arrays contain unrestricted
  data.
\item Array mutation. The arrays contain linear data. But what about
  freeze? Does seem possible in $O(1)$ without some special magic
  support.
\item Encoding ownership.
\end{itemize}

Remark: could also have a look at Mezzo and see if we can encode one
of their examples.

\printbibliography

\end{document}