%if False
\begin{code}
{-# OPTIONS --prop --allow-unsolved-metas #-}

import Agda.Builtin.Equality.Rewrite

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool renaming (true to tt; false to ff)
open import Agda.Builtin.Nat using () 
  renaming (Nat to ℕ; suc to su; zero to ze)
open import Agda.Primitive

module Presentation-TYPES.presentation where 

module _ where
  infix 4 _≡[_]≡_

  private variable
    ℓ   : Level
    A B : Set _
    x y z : A

  sym : x ≡ y → y ≡ x
  sym refl = refl

  _∙_ : x ≡ y → y ≡ z → x ≡ z
  refl ∙ q = q

  transp : (P : A → Set ℓ) → x ≡ y → P x → P y
  transp P refl d = d

  ap : (f : A → B) → x ≡ y → f x ≡ f y
  ap f refl = refl

  _≡[_]≡_ : A → A ≡ B → B → Set _
  x ≡[ refl ]≡ y = x ≡ y

  data Singleton {a} {A : Set a} (x : A) : Set a where
    _with≡_ : (y : A) → x ≡ y → Singleton x

  inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
  inspect x = x with≡ refl

  data ⊥ : Set where

  ⊥-elim : ⊥ → A
  ⊥-elim ()

  not : Bool → Bool
  not tt = ff
  not ff = tt

variable
  A B : Set
\end{code}
%endif

%let intrinsic_style = True

\documentclass[usenames,dvipsnames]{beamer}

\usepackage[style=authoryear,backend=biber]{biblatex}
\addbibresource{main.bib}

\usepackage{xpatch}
\xapptobibmacro{cite}{\setunit{\nametitledelim}\printfield[emph]{title}}{}{}
% TODO: I would like to also put the year in parens, but this is tricky
% There doesn't appear to be a way to just overwrite a bibmacro completely
%\xpatchbibmacro{cite}{\printfield{author} (\printfield{year}), \printfield[emph]{title}}{}{}


% Remove some unwanted entries from the bibliography
\AtEveryBibitem{
	\clearfield{issn}
	\clearfield{isbn}
	\clearfield{archivePrefix}
	\clearfield{arxivId}
	\clearfield{pmid}
	\clearfield{eprint}
	% I want URLs!
	% \ifentrytype{online}{}{\ifentrytype{misc}{}{\clearfield{url}}}
	% But not if there is a doi!
	\iffieldundef{doi}{}{\clearfield{url}}
	% I also want DOIs!
	% \ifentrytype{book}{\clearfield{doi}}{}

}

\usepackage[conor]{agda}

\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}

\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{latexsym}

% \usepackage[theoremfont,libertinus,smallerops,vvarbb]{newtx}
\usepackage{libertinus}

\usepackage[scaled=.85]{beramono}
\usepackage[scr=rsfso,cal=boondoxo]{mathalfa}
\usepackage{morewrites}

\usefonttheme[onlymath]{serif}

\usepackage[only,llbracket,rrbracket]{stmaryrd}

\let\refeq\relax
\usepackage{mathtools}

\usepackage{dsfont}
\newcommand\hmmax{0}
\newcommand\bmmax{0}
\usepackage{bm}

\usepackage{graphicx}
% \fontfamily{DejaVuSans-TLF}
% \selectfont

\usepackage{xspace}

% From https://tex.stackexchange.com/questions/262878/how-to-horizontal-vertical-combine-two-math-symbols
\providecommand*\colonequiv{\vcentcolon\mspace{-1.2mu}\equiv}

%include lhs2TeX.fmt
%%include polycode.fmt
%include agda_tweaked.fmt
%include lib.fmt

\setbeamertemplate{itemize subitem}{|∙|}
\setbeamertemplate{footline}[frame number]
\setbeamertemplate{navigation symbols}{}

% \newcommand{\smart}{\textsf{\textbf{smart}}\xspace}
% \newcommand{\SC}{\textsf{\textbf{smart case}}\xspace}
% \newcommand{\SIF}{\textsf{\textbf{smart if}}\xspace}
% \newcommand{\SCBool}{$\textsf{SC}^{\textsc{Bool}}$\xspace}
% \newcommand{\SCDef}{$\textsf{SC}^{\textsc{Def}}$\xspace}

\newcommand{\nocodeindent}{\setlength\mathindent{0em}}
\newcommand{\resetcodeindent}{\setlength\mathindent{1em}}
\newcommand{\nobarfrac}{\gendfrac{}{}{0pt}{}}

\newcommand{\with}{\AgdaKeyword{with}\xspace}
\newcommand{\rewrite}{\AgdaKeyword{rewrite}\xspace}
\newcommand{\swith}{smart \AgdaKeyword{with}\xspace}
\newcommand{\SWITH}{Smart \AgdaKeyword{with}\xspace}
\newcommand{\scase}{smart \AgdaKeyword{case}\xspace}
\newcommand{\SCASE}{Smart \AgdaKeyword{case}\xspace}
\newcommand{\reflect}{\AgdaKeyword{reflect}\xspace}
\newcommand{\AgdaIn}{\AgdaKeyword{in}\xspace}

\newcommand{\filter}{\AgdaFunction{filter}\xspace}
\newcommand{\filterTwice}{\AgdaFunction{filter-twice}\xspace}
\newcommand{\AgdaDefEq}{\AgdaSymbol{=}\xspace}
\newcommand{\AddZe}{\AgdaFunction{+ze}\xspace}
\newcommand{\InvXor}{\AgdaFunction{inv-xor}\xspace}
\newcommand{\xor}{\AgdaFunction{xor}\xspace}
\newcommand{\inv}{\AgdaFunction{inv}\xspace}
\newcommand{\even}{\AgdaInductiveConstructor{even}\xspace}
\newcommand{\odd}{\AgdaInductiveConstructor{odd}\xspace}
\newcommand{\refl}{\AgdaInductiveConstructor{refl}\xspace}
\newcommand{\ze}{\AgdaInductiveConstructor{ze}\xspace}
\newcommand{\su}{\AgdaInductiveConstructor{su}\xspace}
\newcommand{\Nat}{\AgdaDatatype{Nat}\xspace}
\newcommand{\AgdaVec}{\AgdaDatatype{Vec}\xspace}
\newcommand{\Fin}{\AgdaDatatype{Fin}\xspace}
\newcommand{\Tm}{\AgdaDatatype{Tm}\xspace}
\newcommand{\AgdaParens}[1]{\AgdaSymbol{(}#1\AgdaSymbol{)}}
\newcommand{\cons}{\AgdaOperator{\AgdaInductiveConstructor{,-}}\xspace}
\newcommand{\nil}{\AgdaInductiveConstructor{[]}\xspace}
\newcommand{\true}{\AgdaInductiveConstructor{tt}\xspace}
\newcommand{\false}{\AgdaInductiveConstructor{ff}\xspace}

\newcommand{\AgdaBar}{\AgdaOperator{\AgdaKeyword{||}}\xspace}
\newcommand{\AgdaColon}{\AgdaOperator{\AgdaKeyword{:}}\xspace}
\newcommand{\AgdaCloseBrace}{\AgdaSymbol{\}}}
\newcommand{\AgdaBraces}[1]{\AgdaSymbol{\{}#1\AgdaCloseBrace}
\xspaceaddexceptions{\AgdaCloseBrace}

\newcommand{\AgdaEq}{\AgdaOperator{\AgdaDatatype{≡}}\xspace}
\newcommand{\AgdaDepEq}[1]{%
\AgdaOperator{\AgdaFunction{≡[}}%
\AgdaSpace{}#1\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{]≡}}%
\xspace}
\newcommand{\AgdaAdd}{\AgdaOperator{\AgdaFunction{+}}\xspace}
\newcommand{\AgdaAddDef}{\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}+\AgdaUnderscore{}}}\xspace}
\newcommand{\AgdaAp}{\AgdaFunction{ap}\xspace}
\newcommand{\xorEven}{\AgdaFunction{xor-even}\xspace}
\newcommand{\invXor}{\AgdaFunction{inv-xor}\xspace}



% Snippets (code that either has a type error or requires '--smart-with' to 
% check)

% \begin{code}
%   filter-twice : filter f (filter f xs) ≡ filter f xs
%   filter-twice {f = f} {xs = []}       = refl
%   filter-twice {f = f} {xs = x ,- xs}  with f x
%   ... | tt = ap (x ,-_) (filter-twice {xs = xs})
%   ... | ff = filter-twice {xs = xs}
% \end{code}
\newcommand{\SnipASmartFilter}{
\begin{myagda}%
%
\>[2]\AgdaFunction{filter-twice}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaFunction{filter}\AgdaSpace{}%
\AgdaGeneralizable{f}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaFunction{filter}\AgdaSpace{}%
\AgdaGeneralizable{f}\AgdaSpace{}%
\AgdaGeneralizable{xs}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaOperator{\AgdaDatatype{≡}}\AgdaSpace{}%
\AgdaFunction{filter}\AgdaSpace{}%
\AgdaGeneralizable{f}\AgdaSpace{}%
\AgdaGeneralizable{xs}\<%
\\
%
\>[2]\AgdaFunction{filter-twice}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{f}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{f}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{xs}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{[]}\AgdaSymbol{\}}%
\>[39]\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{refl}\<%
\\
%
\>[2]\AgdaFunction{filter-twice}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{f}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{f}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{xs}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{x}\AgdaSpace{}%
\AgdaOperator{\AgdaInductiveConstructor{,-}}\AgdaSpace{}%
\AgdaBound{xs}\AgdaSymbol{\}}%
\>[39]\AgdaKeyword{with}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaBound{x}\<%
\\
%
\>[2]\AgdaSymbol{...}\AgdaSpace{}%
\AgdaSymbol{|}\AgdaSpace{}%
\AgdaInductiveConstructor{tt}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaFunction{ap}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{x}\AgdaSpace{}%
\AgdaOperator{\AgdaInductiveConstructor{,-\AgdaUnderscore{}}}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaFunction{filter-twice}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{xs}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{xs}\AgdaSymbol{\})}\<%
\\
%
\>[2]\AgdaSymbol{...}\AgdaSpace{}%
\AgdaSymbol{|}\AgdaSpace{}%
\AgdaInductiveConstructor{ff}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaFunction{filter-twice}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{xs}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{xs}\AgdaSymbol{\}}\<%
\end{myagda}
}


% _+_ : Nat p → Nat q → Nat (p xor q)
% _+_ {p} {q} ze      m = m
% _+_ {p} {q} (su n)  m with n+m ← n + m rewrite inv-xor {p} {q}
%   = su n+m

% +ze : n + ze ≡[ ap Nat xor-even ]≡ n
% +ze {n = ze} = refl
% +ze {n = su {p} n} with n′ ← n + ze in eq rewrite inv-xor {p} {even}
%   = {!0!}
\newcommand{\SnipBAddZeIllTyped}{
\begin{myagda}%
\>[0][@{}l@{\AgdaIndent{1}}]%
\>[2]\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}+\AgdaUnderscore{}}}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaDatatype{Nat}\AgdaSpace{}%
\AgdaGeneralizable{p}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaDatatype{Nat}\AgdaSpace{}%
\AgdaGeneralizable{q}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaDatatype{Nat}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaGeneralizable{p}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{xor}}\AgdaSpace{}%
\AgdaGeneralizable{q}\AgdaSymbol{)}\<%
\\
%
\>[2]\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}+\AgdaUnderscore{}}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{q}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaInductiveConstructor{ze}%
\>[22]\AgdaBound{m}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{m}\<%
\\
%
\>[2]\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}+\AgdaUnderscore{}}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{q}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaInductiveConstructor{su}\AgdaSpace{}%
\AgdaBound{n}\AgdaSymbol{)}%
\>[22]\AgdaBound{m}\AgdaSpace{}%
\AgdaKeyword{with}\AgdaSpace{}%
\AgdaBound{n+m}\ ←\ \AgdaBound{n}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{+}}\AgdaSpace{}%
\AgdaBound{m}\AgdaSpace{}%
\AgdaKeyword{rewrite}\AgdaSpace{}%
\AgdaFunction{inv-xor}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{q}\AgdaSymbol{\}}\<%
\\
\>[2][@{}l@{\AgdaIndent{0}}]%
\>[4]\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{su}\AgdaSpace{}%
\AgdaBound{n+m}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
%
\>[2]\AgdaFunction{+ze}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaGeneralizable{n}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{+}}\AgdaSpace{}%
\AgdaInductiveConstructor{ze}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{≡[}}\AgdaSpace{}%
\AgdaFunction{ap}\AgdaSpace{}%
\AgdaDatatype{Nat}\AgdaSpace{}%
\AgdaFunction{xor-even}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{]≡}}\AgdaSpace{}%
\AgdaGeneralizable{n}\<%
\\
%
\>[2]\AgdaFunction{+ze}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{n}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{ze}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{refl}\<%
\\
%
\>[2]\AgdaFunction{+ze}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{n}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{su}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaBound{n}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaKeyword{with}\AgdaSpace{}%
\AgdaBound{n′}\ ←\ \AgdaBound{n}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{+}}\AgdaSpace{}%
\AgdaInductiveConstructor{ze}\AgdaSpace{}%
\AgdaKeyword{in}\AgdaSpace{}%
\AgdaArgument{eq}
\AgdaKeyword{rewrite}\AgdaSpace{}%
\AgdaFunction{inv-xor}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaInductiveConstructor{even}\AgdaSymbol{\}}\<%
\\
\>[2][@{}l@{\AgdaIndent{0}}]%
\>[4]\AgdaSymbol{=}\AgdaSpace{}%
\AgdaHole{\{!0!\}}\<%
\end{myagda}
}


\def\email#1{{\tt#1}}

\title{\SWITH}
\author{Nathaniel Burke}
\institute{TU Delft}
\date{TYPES 2026}

\begin{document}

\nocodeindent

\newcommand{\footnocite}[1]{\phantom{\footcite{#1}}}

% From https://tex.stackexchange.com/questions/13793/beamer-alt-command-like-visible-instead-of-like-only
% \newcommand<>\Alt[2]{{%
%     \sbox0{#1}%
%     \sbox1{#2}%
%     \alt#3%
%         {\rlap{\usebox0}\vphantom{\usebox1}\hphantom{\ifnum\wd0>\wd1 \usebox0\else\usebox1\fi}}%
%         {\rlap{\usebox1}\vphantom{\usebox0}\hphantom{\ifnum\wd0>\wd1 \usebox0\else\usebox1\fi}}%
% }}

\newcommand<>{\altvphantom}[2]{\alt#3{#1}{#2}\vphantom{#1}\vphantom{#2}}


\frame{\titlepage}

\begin{frame}
\frametitle{Plan}
\begin{itemize}
\item \textbf{Motivation and background}
\\\phantom{a}\\\phantom{a}\\
\item \textbf{Examples}
\\\phantom{a}\\\phantom{a}\\
\item \textbf{Theory and implementation}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Motivation}
\begin{itemize}
\item<1-3> Scrutinising the results of intermediary computations is useful!
  \vspace{-1.5ex}
  \begin{myagda}
\>[0]\AgdaKeyword{case}\AgdaSpace\AgdaFunction{norm}\AgdaSpace%
\AgdaBound{t}\AgdaSpace%
\AgdaKeyword{of}\AgdaSpace%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[2]\AgdaInductiveConstructor{lam}\AgdaSpace\AgdaBound{x}%
\AgdaSpace\AgdaBound{t'}\AgdaSpace%
\AgdaSymbol{→}\AgdaSpace\AgdaFunction{norm}\AgdaSpace%
\AgdaSymbol{(}\AgdaFunction{substitute}\AgdaSpace%
\AgdaBound{x}\AgdaSpace\AgdaBound{u}\AgdaSpace%
\AgdaBound{t'}\AgdaSymbol{)}%
\\
  \end{myagda}
% Example of a case expression - not on variable?
\item<2-3> \vspace{-1.5ex} In dependently-typed languages, we expect
  pattern matching to support dependent elimination:
  \vspace{-1.5ex}
  \begin{code}
not-not : (b : Bool) → not (not b) ≡ b
not-not tt  = refl
not-not ff  = refl
  \end{code}
\item<3-3> \vspace{-1.5ex} How to combine the two?
\end{itemize}
\end{frame}


\begin{frame}
\frametitle{\with-abstractions}
\begin{itemize}
\item<1-2> Proposed by McBride and McKinna in 2004.\footcite{mcbride2004view}
\item<2-2> Implemented in Agda
    \vspace{-1.5ex}
    \begin{code}[hide]
data List (A : Set) : Set where
  []   : List A
  _,-_ : A → List A → List A

open import Agda.Builtin.Sigma
_×_ : Set → Set → Set
A × B = Σ A λ _ → B
    \end{code}
    \begin{code}
unzip : List (A × B) → List A × List B
unzip []        = [] , []
unzip ((x , y) ,- xys) with  unzip xys
unzip ((x , y) ,- xys) |     xs , ys
  = (x ,- xs) , (y ,- ys)
  \end{code}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{\with-abstractions (2)}
\begin{itemize}
\item<1-6> To support dependent elimination, \with-abstractions generalise
  the context.
  \vspace{-1.5ex}
  \begin{code}[hide]
data _＋_ (A B : Set) : Set where
  inl : A → A ＋ B
  inr : B → A ＋ B
  \end{code}
  \begin{code}
decide : (f : A → Bool) (x : A) → (f x ≡ tt) ＋ (f x ≡ ff)
decide f x with  f x
decide f x | tt = inl refl
decide f x | ff = inr refl
  \end{code}
\item<2-6> \vspace{-1.5ex} Multi-step procedure:
  \begin{itemize}
  \item<3-6> Normalise the context \includegraphics{Emojis/Sad}
  \item<4-6> Replace scrutinee occurences with the fresh argument
    \includegraphics{Emojis/Think}
  \item<5-6> Must check the context is still well-typed 
    \includegraphics{Emojis/AAA}
  \end{itemize}
\item<6> This is a real problem! Users keep hitting problems with 
  \with-abstractions\footnote{\url{https://github.com/NathanielB123/TYPES-2026/tree/main/InTheWild}} 
  and are warned away from the feature.
\end{itemize}
\end{frame}

\begin{frame}
  \centering \Large
  Examples
\end{frame}

\begin{frame}[t]
\frametitle{Generalisation is ``one-off''}
\begin{code}[hide]
module FilterExample where
  variable
    f  : A → B
    xs : List A
\end{code}
% Top aligned
\only<1>{
\begin{code}[hide]
  module FilterExampleA where
\end{code}
\begin{code}
    filter : (A → Bool) → List A → List A
    filter f [] = []
    filter f (x ,- xs) with f x
    ... | tt = x ,- filter f xs
    ... | ff = filter f xs

    filter-twice : filter f (filter f xs) ≡ filter f xs
    filter-twice {f = f} {xs = []}       = refl
    filter-twice {f = f} {xs = x ,- xs}  = {!0!}
\end{code}
}
\only<2>{
\begin{code}[hide]
  module FilterExampleB where
\end{code}
\begin{code}
    filter : (A → Bool) → List A → List A
    filter f [] = []
    filter f (x ,- xs) with f x
    ... | tt = x ,- filter f xs
    ... | ff = filter f xs

    filter-twice : filter f (filter f xs) ≡ filter f xs
    filter-twice {f = f} {xs = []}       = refl
    filter-twice {f = f} {xs = x ,- xs}  with f x
    ... | w = {!0!}
\end{code}
}
\only<3>{
\begin{code}[hide]
  module FilterExampleC where
\end{code}
\begin{code}
    filter : (A → Bool) → List A → List A
    filter f [] = []
    filter f (x ,- xs) with f x
    ... | tt = x ,- filter f xs
    ... | ff = filter f xs

    filter-twice : filter f (filter f xs) ≡ filter f xs
    filter-twice {f = f} {xs = []}       = refl
    filter-twice {f = f} {xs = x ,- xs}  with f x
    ... | tt = {!0!}
    ... | ff = {!1!}
\end{code}
}
\only<4>{
\begin{code}[hide]
  module FilterExampleD where
\end{code}
\begin{code}
    filter : (A → Bool) → List A → List A
    filter f [] = []
    filter f (x ,- xs) with f x
    ... | tt = x ,- filter f xs
    ... | ff = filter f xs

    filter-twice : filter f (filter f xs) ≡ filter f xs
    filter-twice {f = f} {xs = []}       = refl
    filter-twice {f = f} {xs = x ,- xs}  with f x
    ... | tt = {!0!}
    ... | ff = filter-twice {xs = xs}
\end{code}
}
\only<5>{
\begin{code}[hide]
  module FilterExampleE where
\end{code}
\begin{code}
    filter : (A → Bool) → List A → List A
    filter f [] = []
    filter f (x ,- xs) with f x
    ... | tt = x ,- filter f xs
    ... | ff = filter f xs

    filter-twice : filter f (filter f xs) ≡ filter f xs
    filter-twice {f = f} {xs = []}       = refl
    filter-twice {f = f} {xs = x ,- xs}  with f x in eq
    ... | tt rewrite eq = {!0!}
    ... | ff = filter-twice {xs = xs}
\end{code}
}
\only<6>{
\begin{code}[hide]
  module FilterExampleF where
\end{code}
\begin{code}
    filter : (A → Bool) → List A → List A
    filter f [] = []
    filter f (x ,- xs) with f x
    ... | tt = x ,- filter f xs
    ... | ff = filter f xs

    filter-twice : filter f (filter f xs) ≡ filter f xs
    filter-twice {f = f} {xs = []}       = refl
    filter-twice {f = f} {xs = x ,- xs}  with f x in eq
    ... | tt rewrite eq = ap (x ,-_) (filter-twice {xs = xs})
    ... | ff = filter-twice {xs = xs}
\end{code}
}
% Magical vspace hacks
\vspace{-2ex}
\vskip0pt plus 1filll
% Bottom aligned
\only<1-5>{Goal type(s):\\}
\only<1>{
\AgdaHole{\{!0!\}} \AgdaOperator{:} 
\filter \AgdaBound{f} \AgdaParens{\filter \AgdaBound{f} 
\AgdaParens{\AgdaBound{x} \cons \AgdaBound{xs}}
\AgdaBar \AgdaBound{f} \AgdaBound{x}}
\AgdaEq
\filter \AgdaBound{f} \AgdaParens{\AgdaBound{x} \cons \AgdaBound{xs}}
\AgdaBar \AgdaBound{f} \AgdaBound{x}
\\\phantom{\AgdaHole{\{!1!\}}}
}
\only<2>{
\AgdaHole{\{!0!\}} \AgdaOperator{:} 
\filter \AgdaBound{f} \AgdaParens{\filter \AgdaBound{f} 
\AgdaParens{\AgdaBound{x} \cons \AgdaBound{xs}}
\AgdaBar \AgdaBound{w}}
\AgdaEq
\filter \AgdaBound{f} \AgdaParens{\AgdaBound{x} \cons \AgdaBound{xs}}
\AgdaBar \AgdaBound{w}
\\\phantom{\AgdaHole{\{!1!\}}}
}
\only<3>{
\AgdaHole{\{!0!\}} \AgdaOperator{:} 
\filter \AgdaBound{f} \AgdaParens{\AgdaBound{x} \cons 
\filter \AgdaBound{f} \AgdaBound{xs}}
\AgdaBar \AgdaBound{f} \AgdaBound{x}
\AgdaEq
\AgdaBound{x} \cons \filter \AgdaBound{f} \AgdaBound{xs}\\
\AgdaHole{\{!1!\}} \AgdaOperator{:} 
\filter \AgdaBound{f} \AgdaParens{\filter \AgdaBound{f} 
\AgdaBound{xs}}
\AgdaEq
\filter \AgdaBound{f} \AgdaBound{xs}
}
\only<4>{
\AgdaHole{\{!0!\}} \AgdaOperator{:} 
\filter \AgdaBound{f} \AgdaParens{\AgdaBound{x} \cons 
\filter \AgdaBound{f} \AgdaBound{xs}}
\AgdaBar \AgdaBound{f} \AgdaBound{x}
\AgdaEq
\AgdaBound{x} \cons \filter \AgdaBound{f} \AgdaBound{xs}
\\\phantom{\AgdaHole{\{!1!\}}}
}
\only<5>{
\AgdaHole{\{!0!\}} \AgdaOperator{:} 
\AgdaBound{x} \cons
\filter \AgdaBound{f} \AgdaParens{\filter \AgdaBound{f} \AgdaBound{xs}}
\AgdaEq
\AgdaBound{x} \cons \filter \AgdaBound{f} \AgdaBound{xs}
\\\phantom{\AgdaHole{\{!1!\}}}
}
\only<6>{
\AgdaDatatype{*All Done*}
\\\phantom{\AgdaHole{\{!1!\}}}
\\\phantom{\AgdaHole{\{!1!\}}}
}
% The goals are bottom aligned, but we don't want it to be placed at the actual
% bottom of the slide!
\\\phantom{a}
\end{frame}

% New plan for this slide: Start with the dream "smart with" solution",
% then replace with a hole and reveal the context...
\begin{frame}[t]
\frametitle{\SWITH}
\begin{code}[hide]
  filter : (A → Bool) → List A → List A
  filter f []           = []
  filter f (x ,- xs) with f x
  ... | tt = x ,- filter f xs
  ... | ff = filter f xs 
\end{code}
\only<1>{\SnipASmartFilter}
\only<2>{
\begin{code}
  filter-twice : filter f (filter f xs) ≡ filter f xs
  filter-twice {f = f} {xs = []}       = refl
  filter-twice {f = f} {xs = x ,- xs}  with f x
  ... | tt = {!0!}
  ... | ff = filter-twice {xs = xs}
\end{code}
}
% Magical vspace hacks
\vspace{-2ex}
\vskip0pt plus 1filll
% Bottom aligned
\only<2>{
Goal type (and context):\\
\vspace{-2ex}
\begin{myagda}
\>[1]\AgdaBound{A}
\>[2]\AgdaOperator{:} \AgdaPrimitive{Set}\\
\>[1]\AgdaBound{f}
\>[2]\AgdaOperator{:} \AgdaBound{A} \AgdaOperator{→} \AgdaDatatype{Bool}\\
\>[1]\AgdaBound{x}
\>[2]\AgdaOperator{:} \AgdaBound{A}\\
\>[1]\AgdaBound{xs}
\>[2]\AgdaOperator{:} \AgdaDatatype{List} \AgdaBound{A}\\
\>[0]\AgdaSymbol{@}\AgdaKeyword{rewrite}
\>[1]\AgdaBound{with-eq}
\>[2]\AgdaOperator{:}
\AgdaBound{f} \AgdaBound{x} \AgdaEq \AgdaInductiveConstructor{tt}\\
\>[0]\AgdaOperator{⊢}
\AgdaHole{\{!0!\}} \AgdaOperator{:} 
\AgdaBound{x} \cons
\filter \AgdaBound{f} \AgdaParens{\filter \AgdaBound{f} \AgdaBound{xs}}
\AgdaEq
\AgdaBound{x} \cons \filter \AgdaBound{f} \AgdaBound{xs}\\
\end{myagda}

% The goals are bottom aligned, but we don't want it to be placed at the actual
% bottom of the slide!
\phantom{a}
}
\end{frame}

\begin{frame}
\frametitle{The \rewrite construct}
\begin{itemize}
\item<1-3> Agda's \emph{\rewrite} desugars to \with-abstraction.
\item<2-3> We would like to use \emph{\rewrite} as an alternative to 
  manual transports, e.g. when working with indexed types.
\item<3> The one-off nature of generalisation causes problems...
  \vspace{-1.5ex}
  \begin{code}[hide]
data Parity : Set where
  odd  : Parity
  even : Parity

variable
  p q : Parity

inv : Parity → Parity
inv odd  = even
inv even = odd

_xor_ : Parity → Parity → Parity
even xor q = q
odd  xor q = inv q

inv-inv : inv (inv p) ≡ p
inv-inv {p = even} = refl
inv-inv {p = odd}  = refl

inv-xor : inv p xor q ≡ inv (p xor q)
inv-xor {p = even} = refl
inv-xor {p = odd}  = sym inv-inv

xor-even : p xor even ≡ p
xor-even {p = even} = refl
xor-even {p = odd}  = refl
module ParityExampleSigs where
  \end{code}
  \begin{code}
  data Nat : Parity → Set where
    ze : Nat even
    su : Nat (inv p) → Nat p
  \end{code}
  \begin{code}[hide]
  variable
    n m : Nat p
  \end{code}
  \vspace{-6ex}
  \begin{code}[hide]
  postulate
  \end{code}
  \begin{code}
    _+_  : Nat p → Nat q → Nat (p xor q)
    +ze  : n + ze ≡[ ap Nat xor-even ]≡ n
  \end{code}
\end{itemize}
\end{frame}

\begin{frame}[t]
\frametitle{The \rewrite construct (2)}
\only<1>{
\begin{code}[hide]
module ParityExampleA where
\end{code}
\begin{code}
  data Nat : Parity → Set where
    ze : Nat even
    su : Nat (inv p) → Nat p

  _+_ : Nat p → Nat q → Nat (p xor q)
  _+_ {p} {q} ze      m = m
  _+_ {p} {q} (su n)  m = {!0!}
\end{code}
}
\only<2>{
\begin{code}[hide]
module ParityExampleB where
\end{code}
\begin{code}
  data Nat : Parity → Set where
    ze : Nat even
    su : Nat (inv p) → Nat p

  _+_ : Nat p → Nat q → Nat (p xor q)
  _+_ {p} {q} ze      m = m
  _+_ {p} {q} (su n)  m = su {!0!}
\end{code}
}
\only<3>{
\begin{code}[hide]
module ParityExampleC where
\end{code}
\begin{code}
  data Nat : Parity → Set where
    ze : Nat even
    su : Nat (inv p) → Nat p

  _+_ : Nat p → Nat q → Nat (p xor q)
  _+_ {p} {q} ze      m = m
  _+_ {p} {q} (su n)  m with n+m ← n + m
    = su {!0!}
\end{code}
}
\only<4>{
\begin{code}[hide]
module ParityExampleD where
\end{code}
\begin{code}
  data Nat : Parity → Set where
    ze : Nat even
    su : Nat (inv p) → Nat p

  _+_ : Nat p → Nat q → Nat (p xor q)
  _+_ {p} {q} ze      m = m
  _+_ {p} {q} (su n)  m with n+m ← n + m rewrite inv-xor {p} {q}
    = su {!0!}
\end{code}
}
\only<5>{
\begin{code}[hide]
module ParityExampleE where
\end{code}
\begin{code}
  data Nat : Parity → Set where
    ze : Nat even
    su : Nat (inv p) → Nat p

  _+_ : Nat p → Nat q → Nat (p xor q)
  _+_ {p} {q} ze      m = m
  _+_ {p} {q} (su n)  m with n+m ← n + m rewrite inv-xor {p} {q}
    = su n+m
\end{code}
}
% Magical vspace hacks
\vspace{-4ex}
\vskip0pt plus 1filll
% Bottom aligned
\only<1-4>{Goal type (and context):\\\vspace{-2ex}}
\only<5>{\AgdaDatatype{*All Done*}\\\vspace{-2ex}}
\only<1>{
\begin{myagda}
\>[0]\AgdaBound{p} \AgdaBound{q}
\>[1]\AgdaOperator{:} \AgdaDatatype{Parity}\\
\>[0]\AgdaBound{n}
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} 
\AgdaParens{\AgdaFunction{inv} \AgdaBound{p}}\\
\>[0]\AgdaBound{m} 
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} \AgdaBound{q}\\
\>[0]\AgdaOperator{⊢}
\AgdaHole{\{!0!\}} \AgdaOperator{:}
\AgdaDatatype{Nat} \AgdaParens{\AgdaBound{p} \xor \AgdaBound{q}}\\
\>[0]\phantom{a}
\end{myagda}
}%
\only<2>{
\begin{myagda}
\>[0]\AgdaBound{p} \AgdaBound{q}
\>[1]\AgdaOperator{:} \AgdaDatatype{Parity}\\
\>[0]\AgdaBound{n}
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} 
\AgdaParens{\AgdaFunction{inv} \AgdaBound{p}}\\
\>[0]\AgdaBound{m} 
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} \AgdaBound{q}\\
\>[0]\AgdaOperator{⊢}
\AgdaHole{\{!0!\}} \AgdaOperator{:} \AgdaDatatype{Nat} 
\AgdaParens{\inv \AgdaParens{\AgdaBound{p} \xor \AgdaBound{q}}}\\
\>[0]\phantom{a}
\end{myagda}
}%
\only<3>{
\begin{myagda}
\>[0]\AgdaBound{p} \AgdaBound{q}
\>[1]\AgdaOperator{:} \AgdaDatatype{Parity}\\
\>[0]\AgdaBound{n}
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} 
\AgdaParens{\AgdaFunction{inv} \AgdaBound{p}}\\
\>[0]\AgdaBound{m} 
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} \AgdaBound{q}\\
\>[0]\AgdaBound{n+m} 
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} 
\AgdaParens{\inv \AgdaBound{p} \xor \AgdaBound{q}}\\
\>[0]\AgdaOperator{⊢}
\AgdaHole{\{!0!\}} \AgdaOperator{:} \AgdaDatatype{Nat} 
\AgdaParens{\inv \AgdaParens{\AgdaBound{p} \xor \AgdaBound{q}}}
\end{myagda}
}%
\only<4>{
\begin{myagda}
\>[0]\AgdaBound{p} \AgdaBound{q}
\>[1]\AgdaOperator{:} \AgdaDatatype{Parity}\\
\>[0]\AgdaBound{n}
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} 
\AgdaParens{\AgdaFunction{inv} \AgdaBound{p}}\\
\>[0]\AgdaBound{m} 
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} \AgdaBound{q}\\
\>[0]\AgdaBound{n+m} 
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} 
\AgdaParens{\inv \AgdaParens{\AgdaBound{p} \xor \AgdaBound{q}}}\\
\>[0]\AgdaOperator{⊢}
\AgdaHole{\{!0!\}} \AgdaOperator{:} \AgdaDatatype{Nat} 
\AgdaParens{\inv \AgdaParens{\AgdaBound{p} \xor \AgdaBound{q}}}
\end{myagda}
}%
\only<5>{
\begin{myagda}
\>[0]\phantom{a}\\
\>[0]\phantom{a}\\
\>[0]\phantom{a}\\
\>[0]\phantom{a}\\
\>[0]\phantom{a}
\end{myagda}
}%
\end{frame}

\begin{frame}[t]
\frametitle{Ill-typed \with-abstractions}
\only<1>{
\begin{code}[hide]
data Nat : Parity → Set where
  ze : Nat even
  su : Nat (inv p) → Nat p
variable
  n m : Nat p

module ParityProofExampleA where
\end{code}
\begin{code}
  _+_ : Nat p → Nat q → Nat (p xor q)
  _+_ {p} {q} ze      m = m
  _+_ {p} {q} (su n)  m with n+m ← n + m rewrite inv-xor {p} {q}
    = su n+m

  +ze : n + ze ≡[ ap Nat xor-even ]≡ n
  +ze {n = ze} = refl
  +ze {n = su {p} n} = {!0!}
\end{code}
}
\only<2>{
\begin{code}[hide]
module ParityProofExampleB where
\end{code}
\begin{code}
  _+_ : Nat p → Nat q → Nat (p xor q)
  _+_ {p} {q} ze      m = m
  _+_ {p} {q} (su n)  m with n+m ← n + m rewrite inv-xor {p} {q}
    = su n+m

  +ze : n + ze ≡[ ap Nat xor-even ]≡ n
  +ze {n = ze} = refl
  +ze {n = su {p} n} with n′ ← n + ze
    = {!0!}
\end{code}
}
\only<3>{
\begin{code}[hide]
module ParityProofExampleC where
\end{code}
\begin{code}
  _+_ : Nat p → Nat q → Nat (p xor q)
  _+_ {p} {q} ze      m = m
  _+_ {p} {q} (su n)  m with n+m ← n + m rewrite inv-xor {p} {q}
    = su n+m

  +ze : n + ze ≡[ ap Nat xor-even ]≡ n
  +ze {n = ze} = refl
  +ze {n = su {p} n} with n′ ← n + ze rewrite inv-xor {p} {even} 
    = {!0!}
\end{code}
}
\only<4>{
\begin{code}[hide]
module ParityProofExampleD where
\end{code}
\begin{code}
  _+_ : Nat p → Nat q → Nat (p xor q)
  _+_ {p} {q} ze      m = m
  _+_ {p} {q} (su n)  m with n+m ← n + m rewrite inv-xor {p} {q}
    = su n+m

  +ze : n + ze ≡[ ap Nat xor-even ]≡ n
  +ze {n = ze} = refl
  +ze {n = su {p} n} with n′ ← n + ze in eq
    = {!0!}
\end{code}
}
\only<5>{
% \begin{code}[hide]
% module ParityProofExampleD where
% \end{code}
% \begin{code}
%   _+_ : Nat p → Nat q → Nat (p xor q)
%   _+_ {p} {q} ze      m = m
%   _+_ {p} {q} (su n)  m with n+m ← n + m rewrite inv-xor {p} {q}
%     = su n+m

%   +ze : n + ze ≡[ ap Nat xor-even ]≡ n
%   +ze {n = ze} = refl
%   +ze {n = su {p} n} with n′ ← n + ze in eq rewrite inv-xor {p} {even}
%     = {!0!}
% \end{code}
\SnipBAddZeIllTyped
}
\vspace{-6ex}
\vskip0pt plus 1filll
% Bottom aligned
\only<1-4>{Goal type (and context):\\\vspace{-2ex}}
\only<1>{
\begin{myagda}
\>[0]\AgdaBound{p}
\>[1]\AgdaOperator{:} \AgdaDatatype{Parity}\\
\>[0]\AgdaBound{n}
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} 
\AgdaParens{\AgdaFunction{inv} \AgdaBound{p}}\\
\>[0]\AgdaOperator{⊢}
\AgdaHole{\{!0!\}} \AgdaOperator{:}
\su \AgdaBound{n} \AgdaAdd \ze \AgdaBar \AgdaBound{n} \AgdaAdd \ze 
\AgdaDepEq{\AgdaAp \AgdaDatatype{Nat} \xorEven}
\su \AgdaBound{n}\\
\>[0]\phantom{a}\\
\>[0]\phantom{a}
\end{myagda}
}%
\only<2>{
\begin{myagda}
\>[0]\AgdaBound{p}
\>[1]\AgdaOperator{:} \AgdaDatatype{Parity}\\
\>[0]\AgdaBound{n}
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} 
\AgdaParens{\AgdaFunction{inv} \AgdaBound{p}}\\
\>[0]\AgdaBound{n′}
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat}
\AgdaParens{\AgdaFunction{inv} \AgdaBound{p} \xor \even}\\
\>[0]\AgdaOperator{⊢}
\AgdaHole{\{!0!\}} \AgdaOperator{:}
\su \AgdaBound{n} \AgdaAdd \ze \AgdaBar \AgdaBound{n′}
\AgdaDepEq{\AgdaAp \AgdaDatatype{Nat} \xorEven}
\su \AgdaBound{n}\\
\>[0]\phantom{a}
\end{myagda}
}%
\only<3>{
\begin{myagda}
\>[0]\AgdaBound{p}
\>[1]\AgdaOperator{:} \AgdaDatatype{Parity}\\
\>[0]\AgdaBound{n}
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} 
\AgdaParens{\AgdaFunction{inv} \AgdaBound{p}}\\
\>[0]\AgdaBound{n′}
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat}
\AgdaParens{\AgdaFunction{inv} \AgdaParens{\AgdaBound{p} \xor \even}}\\
\>[0]\AgdaOperator{⊢}
\AgdaHole{\{!0!\}} \AgdaOperator{:}
\su \AgdaBound{n′}
\AgdaDepEq{\AgdaAp \AgdaDatatype{Nat} \xorEven}
\su \AgdaBound{n}\\
\>[0]\phantom{a}
\end{myagda}
}%
\only<4>{
\begin{myagda}
\>[0]\AgdaBound{p}
\>[1]\AgdaOperator{:} \AgdaDatatype{Parity}\\
\>[0]\AgdaBound{n}
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat} 
\AgdaParens{\AgdaFunction{inv} \AgdaBound{p}}\\
\>[0]\AgdaBound{n′}
\>[1]\AgdaOperator{:} \AgdaDatatype{Nat}
\AgdaParens{\AgdaFunction{inv} \AgdaBound{p} \xor \even}\\
\>[0]\AgdaBound{eq}
\>[1]\AgdaOperator{:} \AgdaBound{n} \AgdaAdd \ze \AgdaEq \AgdaBound{n′}\\
\>[0]\AgdaOperator{⊢}
\AgdaHole{\{!0!\}} \AgdaOperator{:}
\su \AgdaBound{n′}
\AgdaDepEq{\AgdaAp \AgdaDatatype{Nat} \xorEven}
\su \AgdaBound{n}
\end{myagda}
}%
\only<5>{
\AgdaError{error: [UnequalTerms]}\\
\AgdaError{inv p xor even != lhs of type Parity when checking that the type}
\\...\\
\AgdaError{of the generated with function is well-formed}\\
\phantom{a}\\
\phantom{a}
}
\end{frame}

\begin{frame}
\frametitle{Smart \rewrite}
\begin{myagda}
\>[0]\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}+\AgdaUnderscore{}}}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaDatatype{Nat}\AgdaSpace{}%
\AgdaGeneralizable{p}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaDatatype{Nat}\AgdaSpace{}%
\AgdaGeneralizable{q}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaDatatype{Nat}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaGeneralizable{p}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{xor}}\AgdaSpace{}%
\AgdaGeneralizable{q}\AgdaSymbol{)}\<%
\\
\>[0]\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}+\AgdaUnderscore{}}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{q}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaInductiveConstructor{ze}\AgdaSpace{}%
\AgdaBound{m}\<%
\\
\>[0]\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}+\AgdaUnderscore{}}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{q}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaInductiveConstructor{su}\AgdaSpace{}%
\AgdaBound{n}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaBound{m}\<%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[2]\AgdaKeyword{rewrite}\AgdaSpace{}%
\AgdaFunction{inv-xor}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{q}\AgdaSymbol{\}}\<%
\\
\>[2]\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{su}\AgdaSpace{}%
\AgdaSymbol{(}%
\AgdaBound{n}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{+}}\AgdaSpace{}%
\AgdaBound{m}%
\AgdaSymbol{)}\<%
\\
\\
\>[0]\AgdaFunction{+ze}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaGeneralizable{n}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{+}}\AgdaSpace{}%
\AgdaInductiveConstructor{ze}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{≡[}}\AgdaSpace{}%
\AgdaFunction{ap}\AgdaSpace{}%
\AgdaDatatype{Nat}\AgdaSpace{}%
\AgdaFunction{xor-even}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{]≡}}\AgdaSpace{}%
\AgdaGeneralizable{n}\<%
\\
\>[0]\AgdaFunction{+ze}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{n}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{ze}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{refl}\<%
\\
\>[0]\AgdaFunction{+ze}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{n}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{su}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaBound{n}\AgdaSymbol{\}}\<%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[2]\AgdaKeyword{rewrite}\AgdaSpace{}%
\AgdaFunction{xor-even}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\<%
\\
% \>[2]\AgdaKeyword{rewrite}\AgdaSpace{}%
% \AgdaFunction{xor-even}\AgdaSpace{}%
% \AgdaSymbol{\{}\AgdaFunction{inv}\AgdaSpace{}%
% \AgdaBound{p}\AgdaSymbol{\}}\<%
% \\
\>[2]\AgdaKeyword{rewrite}\AgdaSpace{}%
\AgdaFunction{inv-xor}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{q}\AgdaSymbol{\}}\<%
\\
% \>[2]\AgdaKeyword{rewrite}\AgdaSpace{}%
% \AgdaFunction{xor-even-inv}\AgdaSpace{}%
% \AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\<%
% \\
\>[2]\AgdaKeyword{with}\AgdaSpace{}%
\AgdaInductiveConstructor{refl}\AgdaSpace{}%
\AgdaSymbol{←}\AgdaSpace{}%
\AgdaFunction{xor-even}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaFunction{inv}\AgdaSpace{}%
\AgdaBound{p}\AgdaSymbol{\}}\<%
\\
\>[2]\AgdaSymbol{=}\AgdaSpace{}%
\AgdaFunction{ap}\AgdaSpace{}%
\AgdaInductiveConstructor{su}\AgdaSpace{}%
\AgdaSymbol{(}%
\AgdaFunction{+ze} \AgdaSymbol{\{}\AgdaBound{n}\AgdaSymbol{\}}%
\AgdaSymbol{)}\<%
\\
\end{myagda} 
\end{frame}

\begin{frame}
  \centering \Large
  Theory and implementation
\end{frame}


\begin{frame}
\frametitle{Theory: A first attempt}
\begin{itemize}
\item<1-3> Context extension by \emph{convertibility assumptions}%
  \footcite{altenkirch2011case}$^{\text{--}}$\footcite{weirich2017specification, liu2023dependently}
  \[
  \frac{
  |⊢ Γ ctx|,\quad |Γ ⊢ t₁, t₂ : A|
  }{
  |⊢ Γ ▷ t₁ ~ t₂ ctx|
  }
  \]
\item<2-3> Local equality reflection
  \[\frac{\begin{matrix}
  |Γ ⊢ eq : t₁ = t₂|,\\ 
  |Γ ▷ t₁ ~ t₂ ▷ eq ~ refl ⊢ u : A|
  \end{matrix}}
  {|Γ ⊢ reflect eq in u : A|}\]
\item<3> Is this implementable?
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{(Un)decidable typechecking}
\begin{itemize}
\item<1-4> In definitionally inconsistent contexts (|tt ~ ff|), all types are
	equal, so reduction might loop!
\item<2-4> Detecting inconsistency is hard: given |⊢ foo : ℕ → 𝔹| and
  |⊢ bar : ℕ → 𝔹|, the equation |foo ~ bar| is definitionally consistent only 
  when |foo| and |bar| are extensionally equal.
\item<3-4> Need to restrict equations. Possible criteria:
  \begin{itemize}
  \item[1)] LHS must be neutral
  \item[2)] LHS may not occur in RHS
  \item[3)] LHS may not occur in any prior equation
  \end{itemize}
\item<4> This criteria is not stable under substitution!
%   \begin{code}[hide]
% data Halts? : Set where
%   yes  : Halts?
%   no   : Halts?

% postulate
%   TuringMachine : Set
%   runTM  : TuringMachine → ℕ → Halts?
%   myTM   : TuringMachine
%   \end{code}
%   \vspace{-1.5ex}
%   \begin{myagda}%
% \>[0]\AgdaKeyword{data}\AgdaSpace{}%
% \AgdaDatatype{Halts?}\AgdaSpace{}%
% \AgdaSymbol{:}\AgdaSpace{}%
% \AgdaPrimitive{Set}\AgdaSpace{}%
% \AgdaKeyword{where}\<%
% \\
% \>[0][@{}l@{\AgdaIndent{0}}]%
% \>[2]\AgdaInductiveConstructor{yes}%
% \>[7]\AgdaSymbol{:}\AgdaSpace{}%
% \AgdaDatatype{Halts?}\<%
% \\
% %
% \>[2]\AgdaInductiveConstructor{no}%
% \>[7]\AgdaSymbol{:}\AgdaSpace{}%
% \AgdaDatatype{Halts?}\<%
% \\
% %
% \\[\AgdaEmptyExtraSkip]%
% \>[0]\AgdaFunction{runTM}%
% \>[7]\AgdaSymbol{:}\AgdaSpace{}%
% \AgdaPostulate{TuringMachine}\AgdaSpace{}%
% \AgdaSymbol{→}\AgdaSpace{}%
% \AgdaDatatype{Nat}\AgdaSpace{}%
% \AgdaSymbol{→}\AgdaSpace{}%
% \AgdaDatatype{Halts?}\<%
% \\
% \>[0]\AgdaFunction{myTM}%
% \>[7]\AgdaSymbol{:}\AgdaSpace{}%
% \AgdaPostulate{TuringMachine}\<%
% \\
% %
% \\[\AgdaEmptyExtraSkip]%
% \>[0]\AgdaFunction{foo}\AgdaSpace{}%
% \AgdaSymbol{:}\AgdaSpace{}%
% \AgdaFunction{runTM}\AgdaSpace{}%
% \AgdaFunction{myTM}\AgdaSpace{}%
% \AgdaOperator{\AgdaDatatype{≡}}\AgdaSpace{}%
% \AgdaSymbol{(λ}\AgdaSpace{}%
% \AgdaBound{\AgdaUnderscore{}}\AgdaSpace{}%
% \AgdaSymbol{→}\AgdaSpace{}%
% \AgdaInductiveConstructor{no}\AgdaSymbol{)}\AgdaSpace{}%
% \AgdaSymbol{→}\AgdaSpace{}%
% \AgdaSymbol{...}\<%
% \\
% \>[0]\AgdaFunction{foo}\AgdaSpace{}%
% \AgdaBound{p}\AgdaSpace{}%
% \AgdaKeyword{rewrite}\AgdaSpace{}%
% \AgdaBound{p}\AgdaSpace{}%
% \AgdaSymbol{=}\AgdaSpace{}%
% \AgdaSymbol{...}\<%
%   \end{myagda}
% \item<3-4> \vspace{-1.5ex} 
%   I investigated 
%   \alt<4>{\textbf{\color{BrickRed}non-overlapping}}{non-overlapping}
%   % {\only<4>{\textbf<4>{\color{BrickRed}}non-overlapping}} 
%   Boolean equations during my Master's
% 	\footcite{burke2025local}. Equations at neutral and first-order
%   types seem reasonable.
\end{itemize}
\end{frame}


\begin{frame}
\frametitle{Theory: A second attempt}
\begin{itemize}
\item<1-3> Type and term judgements parameterised by both a signature of global 
  definitions (|Ξ|) and a local context (|Γ|)\\
  |Ξ ∣ Γ ⊢ A type|,\quad |Ξ ∣ Γ ⊢ t : A|
\item<2-3> \emph{Definitions} by local equality reflection
  \[\frac{\begin{matrix}
  |⊢ Ξ sig|,\quad |Ξ ∣ Γ ⊢ eq : t₁ = t₂|,\\ 
  |Ξ ∣ Γ ▷ t₁ ~ t₂ ▷ eq ~ refl ⊢ u : A|
  \end{matrix}}
  {|⊢ Ξ ▷ (Γ ⊢ reflect eq in u : A) sig|}\]

\item<3> \textbf{Important:} Top-level only! This
  gives us much more flexibility with how to 
  restrict equations.
  \begin{itemize}
  \item Note this is in-keeping with Agda's existing
    design for pattern-matching (generative).
  \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Normalisation sketch}
\begin{itemize}
\item<1-4> Aim to apply normalisation by evaluation (NbE).
\item<2-4> For every definition, we need to generate \emph{rewrite environments}
  (\AgdaKeyword{Ne} \AgdaOperator{→} \AgdaKeyword{Val} mappings). 
  This is inherently very syntactic.
\item<3-4> Evaluation w.r.t. a particular rewrite environment can be defined
  \emph{algebraically}.
\item<4> Rewriting requires mutually comparing normal forms during evaluation.
  This necessitates care in the definition of normal forms (e.g. extra type 
  annotations to avoid circularly relying on type former 
  injectivity).\footnote{\url{https://github.com/NathanielB123/TT/tree/main/NonLinNbE/}}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{A bit about implementation (WIP)}
\begin{itemize}
\item<1-5> Available at 
  \url{https://github.com/NathanielB123/agda/tree/local-rewrite-matches}
  (work-in-progess!)
\item<2-5> Built on top of local rewrite rules\footcite{leray2025encode}
  (Agda users also want these for other reasons).
\item<3-5> Need a mechanism for reflecting propositional equalities as local
  rewrite rules.
  \begin{itemize}
    \item<4-5> \textbf{Formally:} Top-level local equality reflection primitive
    \item<5> \textbf{In practice:} With-abstractions bind local rewrite
    rules and these get refined by pattern matching
  \end{itemize}    
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{\SWITH, without K?}
\begin{itemize}
\item<1-4> HoTT would massively benefit from a better way to deal with 
  transports.
\item<2-4> With the restrictions in place, we already are prevented from
  reflecting reflexive equations (LHS may not occur in 
  RHS).\footnocite{cockx2016eliminating}
\visible<3-4>{
\vspace{-1ex}
\begin{myagda}
\>[0]\AgdaPostulate{xor-even-inv}\AgdaSpace{}%
\>[42]\AgdaSymbol{:}\AgdaSpace{}%
\>[43]\AgdaFunction{xor-even}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaFunction{inv}\AgdaSpace{}%
\AgdaGeneralizable{p}\AgdaSymbol{\}}\AgdaSpace{}%
\\
\>[42]\AgdaOperator{\AgdaDatatype{≡}}\AgdaSpace{}%
\>[43]\AgdaFunction{inv-xor}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaGeneralizable{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaInductiveConstructor{even}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{∙}}\AgdaSpace{}%
\AgdaFunction{ap}\AgdaSpace{}%
\AgdaFunction{inv}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaFunction{xor-even}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaGeneralizable{p}\AgdaSymbol{\})}\<%
\\
\>[0]\AgdaFunction{+ze}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaGeneralizable{n}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{+}}\AgdaSpace{}%
\AgdaInductiveConstructor{ze}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{≡[}}\AgdaSpace{}%
\AgdaFunction{ap}\AgdaSpace{}%
\AgdaDatatype{Nat}\AgdaSpace{}%
\AgdaFunction{xor-even}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{]≡}}\AgdaSpace{}%
\AgdaGeneralizable{n}\<%
\\
% \>[0]\AgdaFunction{+ze}\AgdaSpace{}%
% \AgdaSymbol{\{}\AgdaArgument{n}\AgdaSpace{}%
% \AgdaSymbol{=}\AgdaSpace{}%
% \AgdaInductiveConstructor{ze}\AgdaSymbol{\}}\AgdaSpace{}%
% \AgdaSymbol{=}\AgdaSpace{}%
% \AgdaInductiveConstructor{refl}\<%
% \\
\>[0]\AgdaFunction{+ze}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{n}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{su}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaBound{n}\AgdaSymbol{\}}\<%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[2]\AgdaKeyword{rewrite}\AgdaSpace{}%
\AgdaFunction{xor-even}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\<%
\\
% \>[2]\AgdaKeyword{rewrite}\AgdaSpace{}%
% \AgdaFunction{xor-even}\AgdaSpace{}%
% \AgdaSymbol{\{}\AgdaFunction{inv}\AgdaSpace{}%
% \AgdaBound{p}\AgdaSymbol{\}}\<%
% \\
\>[2]\AgdaKeyword{rewrite}\AgdaSpace{}%
\AgdaFunction{inv-xor}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{q}\AgdaSymbol{\}}\<%
\\
\>[2]\AgdaKeyword{rewrite}\AgdaSpace{}%
\AgdaFunction{xor-even-inv}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\<%
\\
\>[2]\AgdaSymbol{=}\AgdaSpace{}%
\AgdaFunction{ap}\AgdaSpace{}%
\AgdaInductiveConstructor{su}\AgdaSpace{}%
\AgdaSymbol{(}%
\AgdaFunction{+ze} \AgdaSymbol{\{}\AgdaBound{n}\AgdaSymbol{\}}%
\AgdaSymbol{)}\<%
\end{myagda}
}%
\vspace{-4ex}
\item<4> Is \emph{\swith} consistent with HoTT?
\end{itemize}
\end{frame}

\begin{frame}
  \centering \Large
  \emph{Thank You!}
\end{frame}

\begin{frame}[allowframebreaks]
\frametitle{Bibliography}
\printbibliography
\end{frame}

\end{document}
