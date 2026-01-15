%if False
\begin{code}
{-# OPTIONS --prop --allow-unsolved-metas #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool renaming (true to tt; false to ff)
open import Agda.Builtin.Nat using () 
  renaming (Nat to ℕ; suc to su; zero to ze)
open import Agda.Primitive

module Presentation-FPDag.presentation where 

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
\newcommand{\AgdaAddDef}{\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}+\AgdaUnderscore{}}}}
\newcommand{\AgdaCong}{\AgdaFunction{cong}\xspace}
\newcommand{\xorEven}{\AgdaFunction{xor-even}\xspace}

\def\email#1{{\tt#1}}

\title{Smart \with}
\author{Nathaniel Burke}
\institute{TU Delft}
\date{FP Dag 2026}

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
\item<1-3> Case expressions are useful!
  \vspace{-1.5ex}
  \begin{myagda}
\>[0]\AgdaKeyword{case}\AgdaSpace\AgdaFunction{norm}\AgdaSpace%
\AgdaBound{t}\AgdaSpace%
\AgdaKeyword{of}\AgdaSpace%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[2]\AgdaInductiveConstructor{lam}\AgdaSpace\AgdaBound{x}%
\AgdaSpace\AgdaBound{t}\AgdaSpace%
\AgdaSymbol{→}\AgdaSpace\AgdaFunction{norm}\AgdaSpace%
\AgdaSymbol{(}\AgdaFunction{substitute}\AgdaSpace%
\AgdaBound{x}\AgdaSpace\AgdaBound{u}\AgdaSpace%
\AgdaBound{t}\AgdaSymbol{)}%
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
unzip ((x , y) ,- xys) with unzip xys
unzip ((x , y) ,- xys) | xs , ys
  = (x ,- xs) , (y ,- ys)
  \end{code}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{\with-abstractions (2)}
\begin{itemize}
\item<1-5> To support dependent elimination, \with-abstractions generalise
  the context.
  \vspace{-1.5ex}
  \begin{code}[hide]
data _＋_ (A B : Set) : Set where
  inl : A → A ＋ B
  inr : B → A ＋ B
  \end{code}
  \begin{code}
decide : (f : A → Bool) (x : A) → (f x ≡ tt) ＋ (f x ≡ ff)
decide f x with f x
decide f x | tt = inl refl
decide f x | ff = inr refl
  \end{code}
\item<2-5> \vspace{-1.5ex} Multi-step process:
  \begin{itemize}
  \item<3-5> Normalise the context \includegraphics{Emojis/Sad}
  \item<4-5> Replace occurrences of the matched term with the pattern
    \includegraphics{Emojis/Think}
  \item<5> Check the context is still well-typed \includegraphics{Emojis/AAA}
  \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}
  \centering \Large
  Examples
\end{frame}

\begin{frame}
\frametitle{A trickier \with-abstraction use-case}
\begin{myagda}%
\>[0]\AgdaFunction{f3}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{f}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaDatatype{Bool}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaDatatype{Bool}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{f}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{f}\AgdaSpace{}%
\AgdaInductiveConstructor{tt}\AgdaSymbol{))}\AgdaSpace{}%
\AgdaOperator{\AgdaDatatype{≡}}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaInductiveConstructor{tt}\<%
\end{myagda}
\end{frame}

\begin{frame}
\frametitle{A trickier \with-abstraction use-case}
\begin{code}
f3 : (f : Bool → Bool) → f (f (f tt)) ≡ f tt
f3 f with f tt in f-tt 
f3 f | tt with f tt | f-tt
f3 f | tt | tt | f-tt with f tt
f3 f | tt | tt | f-tt | tt = refl
f3 f | ff with f ff in f-ff
f3 f | ff | tt = f-tt
f3 f | ff | ff = f-ff
\end{code}
\end{frame}

\begin{frame}
\frametitle{Dream code}
\begin{myagda}
\>[0]\AgdaFunction{f3}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{f}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaDatatype{Bool}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaDatatype{Bool}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{f}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{f}\AgdaSpace{}%
\AgdaInductiveConstructor{tt}\AgdaSymbol{))}\AgdaSpace{}%
\AgdaOperator{\AgdaDatatype{≡}}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaInductiveConstructor{tt}\<%
\\
\>[0]\AgdaFunction{f3}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaKeyword{with}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaInductiveConstructor{tt}\AgdaSpace{}%
\\
\>[0]\AgdaFunction{f3}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaSymbol{||}\AgdaSpace{}%
\AgdaInductiveConstructor{tt}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{refl}\<%
\\
\>[0]\AgdaFunction{f3}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaSymbol{||}\AgdaSpace{}%
\AgdaInductiveConstructor{ff}\AgdaSpace{}%
\AgdaKeyword{with}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaInductiveConstructor{ff}\AgdaSpace{}%
\\
\>[0]\AgdaFunction{f3}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaSymbol{||}\AgdaSpace{}%
\AgdaInductiveConstructor{ff}\AgdaSpace{}%
\AgdaSymbol{||}\AgdaSpace{}%
\AgdaInductiveConstructor{tt}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{refl}\<%
\\
\>[0]\AgdaFunction{f3}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaSymbol{||}\AgdaSpace{}%
\AgdaInductiveConstructor{ff}\AgdaSpace{}%
\AgdaSymbol{||}\AgdaSpace{}%
\AgdaInductiveConstructor{ff}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{refl}\<%
\end{myagda}
\end{frame}

\begin{frame}
\frametitle{Indexed types and the \rewrite construct}
\begin{itemize}
\item<1-2> Agda's \emph{\rewrite} desugars to \with-abstraction.
\item<2> We can try to use \emph{\rewrite} as an alternative to manual 
  transports, e.g. when working with indexed types, but things quickly go 
  wrong...
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
  \begin{code}
_+_  : Nat p → Nat q → Nat (p xor q)
+ze  : n + ze ≡[ ap Nat xor-even ]≡ n
  \end{code}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Indexed types and the \rewrite construct (2)}
\begin{code}
ze + m = m
_+_ {p} {q} (su n) m  with  n + m
_+_ {p} {q} (su n) m  |     n+m
  rewrite inv-xor {p} {q} 
  = su n+m

+ze {n = ze} = refl
+ze {n = su {p} n}  with  n + ze --- in eq
+ze {n = su {p} n}  |     n′ 
  rewrite inv-xor {p} {even} 
  = {!   !} --- Cannot make progress!
\end{code}
\end{frame}

\begin{frame}
\frametitle{Dream code}
\begin{myagda}
% \>[0]\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}+\AgdaUnderscore{}}}\AgdaSpace{}%
% \AgdaSymbol{:}\AgdaSpace{}%
% \AgdaDatatype{Nat}\AgdaSpace{}%
% \AgdaGeneralizable{p}\AgdaSpace{}%
% \AgdaSymbol{→}\AgdaSpace{}%
% \AgdaDatatype{Nat}\AgdaSpace{}%
% \AgdaGeneralizable{q}\AgdaSpace{}%
% \AgdaSymbol{→}\AgdaSpace{}%
% \AgdaDatatype{Nat}\AgdaSpace{}%
% \AgdaSymbol{(}\AgdaGeneralizable{p}\AgdaSpace{}%
% \AgdaOperator{\AgdaFunction{xor}}\AgdaSpace{}%
% \AgdaGeneralizable{q}\AgdaSymbol{)}\<%
% \\
\>[0]\AgdaInductiveConstructor{ze}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{+}}\AgdaSpace{}%
\AgdaBound{m}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
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
%\>[0]\AgdaFunction{+ze}\AgdaSpace{}%
%\AgdaSymbol{:}\AgdaSpace{}%
%\AgdaGeneralizable{n}\AgdaSpace{}%
%\AgdaOperator{\AgdaFunction{+}}\AgdaSpace{}%
%\AgdaInductiveConstructor{ze}\AgdaSpace{}%
%\AgdaOperator{\AgdaFunction{≡[}}\AgdaSpace{}%
%\AgdaFunction{ap}\AgdaSpace{}%
%\AgdaDatatype{Nat}\AgdaSpace{}%
%\AgdaFunction{xor-even}\AgdaSpace{}%
%\AgdaOperator{\AgdaFunction{]≡}}\AgdaSpace{}%
%\AgdaGeneralizable{n}\<%
%\\
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
\>[2]\AgdaKeyword{rewrite}\AgdaSpace{}%
\AgdaFunction{xor-even}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaFunction{inv}\AgdaSpace{}%
\AgdaBound{p}\AgdaSymbol{\}}\<%
\\
\>[2]\AgdaKeyword{rewrite}\AgdaSpace{}%
\AgdaFunction{inv-xor}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{p}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{q}\AgdaSymbol{\}}\<%
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
\frametitle{Theory}
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
\item<3> Is this feasible?
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Decidable typechecking}
\begin{itemize}
\item<1-4> In definitionally inconsistent contexts (|tt ~ ff|), all types are
	equal, so reduction might loop!
\item<2-4> Detecting inconsistency is hard:
  \begin{code}[hide]
data Halts? : Set where
  yes  : Halts?
  no   : Halts?

postulate
  TuringMachine : Set
  runTM  : TuringMachine → ℕ → Halts?
  myTM   : TuringMachine
  \end{code}
  \vspace{-1.5ex}
  \begin{myagda}%
\>[0]\AgdaKeyword{data}\AgdaSpace{}%
\AgdaDatatype{Halts?}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaPrimitive{Set}\AgdaSpace{}%
\AgdaKeyword{where}\<%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[2]\AgdaInductiveConstructor{yes}%
\>[7]\AgdaSymbol{:}\AgdaSpace{}%
\AgdaDatatype{Halts?}\<%
\\
%
\>[2]\AgdaInductiveConstructor{no}%
\>[7]\AgdaSymbol{:}\AgdaSpace{}%
\AgdaDatatype{Halts?}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaFunction{runTM}%
\>[7]\AgdaSymbol{:}\AgdaSpace{}%
\AgdaPostulate{TuringMachine}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaDatatype{Nat}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaDatatype{Halts?}\<%
\\
\>[0]\AgdaFunction{myTM}%
\>[7]\AgdaSymbol{:}\AgdaSpace{}%
\AgdaPostulate{TuringMachine}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaFunction{foo}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaFunction{runTM}\AgdaSpace{}%
\AgdaFunction{myTM}\AgdaSpace{}%
\AgdaOperator{\AgdaDatatype{≡}}\AgdaSpace{}%
\AgdaSymbol{(λ}\AgdaSpace{}%
\AgdaBound{\AgdaUnderscore{}}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaInductiveConstructor{no}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaSymbol{...}\<%
\\
\>[0]\AgdaFunction{foo}\AgdaSpace{}%
\AgdaBound{p}\AgdaSpace{}%
\AgdaKeyword{reflect}\AgdaSpace{}%
\AgdaBound{p}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaSymbol{...}\<%
  \end{myagda}
\item<3-4> \vspace{-1.5ex} 
  I investigated 
  \alt<4>{\textbf{\color{BrickRed}non-overlapping}}{non-overlapping}
  % {\only<4>{\textbf<4>{\color{BrickRed}}non-overlapping}} 
  Boolean equations during my Master's
	\footcite{burke2025local}. Equations at neutral and first-order
  types seem reasonable.
\end{itemize}
\end{frame}


\begin{frame}
\frametitle{Theory (2)}
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
  restrict equations (avoiding subject reduction problems).
  \begin{itemize}
  \item Plus, this is in-keeping with Agda's existing
    design for pattern-matching (generative).
  \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{A bit about implementation (WIP)}
\begin{itemize}
\item<1-4> Build on top of local rewrite rules\footcite{leray2025encode}
  (Agda users also want these for other reasons).
\item<2-4> Need a mechanism for reflecting propositional equalities as local
  rewrite rules.
  \begin{itemize}
    \item<3-4> \textbf{Formally:} Top-level local equality reflection primitive
    \item<4> \textbf{In practice:} Allow pattern matching to refine local 
    rewrite rules (and improve ``{\color{AgdaFunction}green slime}'' while we 
    at it!)%
    \footcite{mcbride2012polynomial}
  \end{itemize}    
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Smart \with, without K?}
\begin{itemize}
\item<1-3> HoTT would massively benefit from a better way to deal with 
  transports.
\item<2-3> If we enforce non-convertibility of the LHS and RHS during 
  \emph{smart \with}, this appears to prevent the proof of UIP from ETT from 
  going through.\footnocite{cockx2016eliminating}
\item<3> Is restricted \emph{smart \with} consistent with HoTT?
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
