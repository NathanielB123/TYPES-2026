\documentclass{easychair}

\usepackage[conor]{agda}
\usepackage{xspace}
\usepackage{newunicodechar}
\usepackage[style=numeric,backend=biber]{biblatex}
\addbibresource{main.bib}

% Remove some unwanted entries from the bibliography
\AtEveryBibitem{
	\clearfield{issn}
	\clearfield{isbn}
	\clearfield{archivePrefix}
	\clearfield{arxivId}
	\clearfield{pmid}
	\clearfield{eprint}
	% Skip URL if there is a doi!
	\iffieldundef{doi}{}{\clearfield{url}}
}


% From https://tex.stackexchange.com/questions/262878/how-to-horizontal-vertical-combine-two-math-symbols
\providecommand*\colonequiv{\vcentcolon\mspace{-1.2mu}\equiv}

%include lhs2TeX.fmt
%include my_agda.fmt
%include lib.fmt

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

\title{Smart \with}

\author{Nathaniel Burke}

\institute{
  TU Delft, Netherlands, \email{n.burke@tudelft.nl}
}

\authorrunning{Burke}

\titlerunning{Smart \with}

\begin{document}

\maketitle

% \begin{abstract}
% In \cite{mcbride2004view}, McBride and McKinna proposed a syntax for 
% pattern matching in type
% theory named the \with construct,
% enabling matches on intermediary computations whilst generalising the
% context (abstracting over the matched term) to support dependent 
% elimination.
% 
% % TODO: I like this as a TLDR, but Jesper is definitely right that an abstract 
% % for an abstract is a bit silly
% % On the other hand, a bunch of TYPES abstracts last year were like this
% % Maybe just calling this "introduction" or "overview" instead of abstract
% % would be a good move
% This feature is implemented in Agda under the name \with-abstractions. 
% While useful, the feature can also be a footgun. 
% Proving simple laws about definitions defined by \with-abstraction is 
% often fiddly and sometimes impossible due to failures in the generalisation
% step producing \emph{ill-typed \with-abstraction} \cite{agda2024with}  errors.
% 
% Inspired by the \scase proposal of Altenkirch et al. \cite{altenkirch2011case},
% we propose an improved \with-abstraction mechanism. 
% Leveraging ongoing
% work to implement local rewrite rules in Agda, we
% aim to support local equality reflection for a subset of
% equations under which we can maintain decidable typechecking.
% \end{abstract}

\begin{code}[hide]
{-# OPTIONS --allow-unsolved-metas #-}
\end{code}

\paragraph{Motivation}

% In \cite{mcbride2004view}, McBride and McKinna proposed a syntax for 
% pattern matching in type
% theory named the \with construct,
% enabling matches on intermediary computations whilst generalising the
% context (abstracting over the matched term) to support dependent 
% elimination.

The \with construct, proposed by McBride and McKinna in \cite{mcbride2004view},
extends dependent pattern matching with a way to match on intermediary
computations whilst generalising the
context to support dependent 
elimination.
This feature is implemented in Agda under the name \with-abstractions. 
While useful, the feature can also be a footgun.
Proving simple laws about definitions by \with-abstraction is 
often fiddly and sometimes impossible due to failures in the generalisation
step producing \emph{ill-typed \with-abstraction} errors \cite{agda2024with}.
To illustrate the problem, consider the following definition of natural numbers
indexed by parity.

% We begin with a small Agda example to illustrate where \with-abstractions 
% fall short,
% starting by defining the datatype of Booleans with negation and exclusive or,
% albeit under some slightly more evocative names.
% proving properties of arithmetic on natural numbers,
% indexed by parity.

% \noindent
% \begin{minipage}{0.275\textwidth}
% \begin{code}
% data Parity : Set where
%   even odd : Parity
% \end{code}
% \end{minipage}
% \begin{minipage}{0.25\textwidth}
% \begin{code}
% inv : Parity → Parity
% inv even  = odd
% inv odd   = even
% \end{code}
% \end{minipage}
% \begin{minipage}{0.3\textwidth}
% \begin{code}
% _xor_ : Parity → Parity → Parity
% even  xor q = q
% odd   xor q = inv q
% \end{code}
% \end{minipage}

\vspace{-1.5ex}
\noindent
\begin{minipage}{0.275\textwidth}
\begin{code}
data Parity : Set where
  even  : Parity 
  odd   : Parity
\end{code}
\begin{code}[hide]
variable
  p q : Parity
\end{code}
\end{minipage}
\begin{minipage}{0.3\textwidth}
\begin{code}
inv     :  Parity → Parity
_xor_   :  Parity → Parity 
        →  Parity
\end{code}
\end{minipage}
\begin{minipage}{0.3\textwidth}
\begin{code}
data Nat : Parity → Set where
  ze : Nat even
  su : Nat (inv p) → Nat p
\end{code}
\end{minipage}
\vspace{-1.5ex}

\begin{code}[hide]
inv even  = odd
inv odd   = even
even  xor q = q
odd   xor q = inv q
\end{code}



% \footnote{We could define natural numbers independently 
% of parity, and then
% prove properties about how parity commutes with arithmetic operations 
% extrinsically.
% By working intrinsically instead, we hope to reap a golden ratio reduction in
% lines of code (\cite{wadler2022plfa}, DeBruijn, ``Intrinsic typing is
% golden'').
% 
% We could also dodge some of the issues that we are about to run into by 
% breaking
% \su into two constructors, keeping successor of \odd and \even
% separate. However,
% this obligates our later definitions to handle an extra case and furthermore
% relies on the index being finite (so this trick cannot be
% replicated for types like length-indexed vectors \AgdaVec, finite sets 
% \Fin, intrinsically-typed terms \Tm etc.).}

\begin{code}[hide]
open import Agda.Primitive
open import Agda.Builtin.Equality

variable
  ℓ : Level
  A B : Set ℓ
  x y : A

-- Utils
sym : x ≡ y → y ≡ x
sym refl = refl

transp : (P : A → Set) → x ≡ y → P x → P y
transp P refl px = px

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

J : (P : ∀ y → x ≡ y → Set) (p : x ≡ y) → P x refl → P y p
J P refl px = px

J-sym : (P : ∀ x → x ≡ y → Set) (p : x ≡ y) → P y refl → P x p
J-sym P refl px = px
-- End utils

inv-inv : inv (inv p) ≡ p
inv-inv {p = even}  = refl
inv-inv {p = odd}  = refl

inv-xor : inv p xor q ≡ inv (p xor q)
inv-xor {p = even} = refl
inv-xor {p = odd}  = sym inv-inv

xor-even : p xor even ≡ p
xor-even {p = even} = refl
xor-even {p = odd}  = refl
\end{code}

\begin{code}[hide]
variable
  n m l : Nat p
\end{code}


% Addition of natural numbers \xor{}s their respective parities. 
% The base case
% is easy: the typechecker automatically unifies \AgdaBound{p} with \even
% and reduces \even \xor \AgdaBound{q} to \AgdaBound{q}.
% 
% \noindent
% \begin{minipage}{0.5\textwidth}
% \begin{code}
% _+_ : Nat p → Nat q → Nat (p xor q)
% \end{code}
% \end{minipage}
% \begin{minipage}{0.4\textwidth}
% \begin{code}
% ze + m = m
% \end{code}
% \end{minipage}

\begin{code}[hide]
_+_ : Nat p → Nat q → Nat (p xor q)
ze + m = m
\end{code}

We will try to implement addition of \Nat{}s, \AgdaAddDef (which \xor{}s the 
respective
parities, \AgdaBound{p} and \AgdaBound{q}) as well as prove that \ze is a
right-identity of addition, \AddZe.
The base case of \AgdaAddDef
is easy, but the inductive step requires us to do some work. 
\inv \AgdaBound{p} \xor \AgdaBound{q} is stuck, so we must
prove a lemma about how \inv commutes with \xor
(concretely, \inv \AgdaBound{p} \xor \AgdaBound{q} \AgdaEq \inv 
\AgdaParens{\AgdaBound{p} \xor \AgdaBound{q}}).


% This is reasonable enough, but then we face 
% a more technical challenge in how to actually 
% apply this lemma. Aiming for convenience, we gravitate towards 
% Agda's \rewrite construct
% (which desugars to \with-abstraction plus a match on \refl) 
% capable of applying one-off 
% rewrites to the context in the direction of a propositional identity.
% Unfortunately, after matching on
% \su \AgdaBound{n}, nothing in the context directly has type 
% \inv \AgdaBound{p} \xor \AgdaBound{q}. To force the rewrite to actually
% do something, we additionally \with-abstract 
% the result of
% the recursive call (at type 
% \Nat \AgdaParens{\inv \AgdaBound{p} \xor \AgdaBound{q}}).

% \begin{code}
% _+_ {p = p} {q = q} (su n) m
%   with     n+m ← n + m
%   rewrite  inv-xor {p = p} {q = q}
%   = su n+m
% \end{code}

This is reasonable enough, but then we face 
a more technical challenge in how to actually 
apply this lemma. Aiming for convenience,
we gravitate towards Agda's indexed pattern matching. We first
\with-abstract over the recursive call in order to get some variable into the
context (\AgdaBound{n+m}) with type 
\Nat \AgdaParens{\inv \AgdaBound{p} \xor \AgdaBound{q}}.
Then, we use another \with-abstraction to rewrite 
\inv \AgdaBound{p} \xor \AgdaBound{q} in the type of \AgdaBound{n+m} to 
\inv \AgdaParens{\AgdaBound{p} \xor \AgdaBound{q}}.%
\footnote{Agda's \rewrite
construct desugars to the same simultaneous abstraction over the LHS
and identity proof.}

\vspace{-1.5ex}
\noindent
\begin{minipage}{0.43\textwidth}
\begin{code}
_+_ {p} {q} (su n) m
  with  n+m ← n + m
  with  inv p xor q       | inv-xor {p} {q}
... |   .(inv (p xor q))  | refl
  = su n+m
\end{code}
\begin{code}[hide]
+ze-sig : Nat p → Set
+ze-sig {p = p} n 
  with     n′ ← n + ze 
  rewrite  xor-even {p = p}
  = n′ ≡ n

_≡[_]≡_ : A → A ≡ B → B → Set _
x ≡[ refl ]≡ y = x ≡ y
infix 4 _≡[_]≡_

+ze : n + ze ≡[ cong Nat xor-even ]≡ n
+ze {n = ze} = refl
\end{code}
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{code}
+ze {n = su {p} n}
  with  n′ ← n + ze ----in eq
  with  inv p xor even       |  inv-xor {p} {even}
...  |  .(inv (p xor even))  | refl
  = {!!}
\end{code}
\end{minipage}
\vspace{-1.5ex}

Note that inlining \AgdaBound{n+m} breaks \AgdaAddDef. \with-abstractions only
apply one-off transformations. Agda does not ``remember''
the equality between \inv \AgdaBound{p} \xor \AgdaBound{q} and
\inv \AgdaParens{\AgdaBound{p} \xor \AgdaBound{q}}.

Proving \AddZe is trickier. Technically, the theorem is not even type correct 
without knowing 
\mbox{\AgdaBound{p} \xor \even \AgdaEq \AgdaBound{p}} but proving this is easy 
enough. We state the goal with a dependent identity type: \AgdaBound{n} 
\AgdaAdd \ze 
\AgdaDepEq{\AgdaCong \Nat \xorEven} \AgdaBound{n}.
In the inductive case we first need to repeat the same
\with-abstractions to make
\su \AgdaBound{n} \AgdaAdd \ze reduce.
The remaining goal (\AgdaHole{\{!!\}}) asks us to prove 
\mbox{\su \AgdaBound{n′} \AgdaDepEq{\AgdaCong \Nat \xorEven} 
\su \AgdaBound{n}}
% Manipulating dependent identity is its own can of worms, but
% more pressingly, 
but this is impossible: we have lost the connection 
between \AgdaBound{n′} and \AgdaBound{n} \AgdaAdd \ze. Since 2.6.2, Agda builds
in the \emph{inspect idiom}, allowing us to write ``\AgdaIn \AgdaBound{eq}'' 
after a \with-abstraction to bind a propositional identity between the abstracted
term and the pattern, but if we attempt to bind \AgdaIn \AgdaBound{eq}
in \AddZe, we hit the dreaded \emph{ill-typed \with-abstraction} error: 
\AgdaError{inv p xor even != lhs of type Parity} 
\AgdaError{when checking that the type} ...
\AgdaError{of the generated with function is well-formed}.

% Dream code:
\begin{code}[hide]
{-
_+_ {p = p} {q = q} (su n) m
  rewrite inv-xor {p = p} {q = q}
  = su (n + m)

+ze {n = ze} = refl
+ze {n = su {p = p} n}
  rewrite xor-even {p = p}
  rewrite inv-xor {p = p} {q = even}
  = refl
-}
\end{code}

% \noindent
% \begin{myagda}
% \>[0]\AgdaError{inv p xor even != lhs of type Parity}%0
% \\
% \>[0]\AgdaError{when checking that the type}%
% \\
% \>[0]...%
% \\
% \>[0]\AgdaError{of the generated with function is well-formed}%
% \end{myagda}

The problem is \with-abstractions' one-off nature.
For 
\AgdaBound{eq} : \AgdaBound{n′} \AgdaEq \AgdaBound{n} \AgdaAdd \ze 
to typecheck, both \AgdaBound{n′} and \AgdaBound{n} \AgdaAdd \ze must have
the same type. This is the case until we abstract over
\inv \AgdaBound{p} \xor \even. 
\AgdaBound{n′}'s type is rewritten, but \AgdaBound{n} \AgdaAdd \ze
is left alone, and now the context no longer typechecks.

% Experienced Agda users might find following along with this code example 
% slightly frustrating.
Conventional Agda wisdom suggests sidestepping these issues by 
forgoing automation features like \with-abstraction
and its derivatives. Instead, we should program with raw transports.
Transports have a bit of a UX problem (manually specifying exactly where
the equation should be applied is tedious), but more problematically,
proving properties of functions involving transports still risks a 
prolonged battle with
``transport-hell''.\footnote{A problem whose magnitude is corroborated by 
the large arsenal of folklore techniques for fighting it: massaging
equations into a fragment accepted by indexed pattern matching, 
redefining transport by induction on the target 
\cite{2024fin}, using ``John Major'' heterogeneous
equality \cite{mcbride2000dependently, saffrich2024intrinsically},
global rewrite rules \cite{cockx2020type, cockx2021taming, leray2024rewster} 
etc.}

Our perspective is that some manual transport reasoning is 
inherent to the design of intensional type theory, but that does not prevent us 
from doing a
much better job than existing proof assistants.
Inspired by the \scase proposal of Altenkirch et al. \cite{altenkirch2011case},
we propose an improved \with-abstraction mechanism for Agda. 

We plan to build upon (a subset\footnote{We
only need \emph{ground} rules: all variables in 
equations are bound in the context or via higher-order matching.} of) 
local rewrite rules, as proposed in \cite{leray2025encode}.
To elaborate \with-abstractions, the current generalisation procedure
normalises the context, replaces occurrences of the matched term
with the pattern and then checks the context is still well-typed. We plan
to instead simply add a local rewrite between the matched term and pattern.

Careful integration of local rewrite rules with indexed pattern matching
also improves, \textit{en passant}, some of the frustrating UX
problems with the latter (termed ``green slime'' in 
\cite{mcbride2012polynomial}). Rather than throwing an error as soon as
LHS unification fails, we should instead (where possible) force the index 
equations to hold with rewriting.
% \footnote{The details of implementation here are still
% somewhat up-for-debate, depending on how closely we want to follow the
% theoretical presentation vs reuse Agda's existing implementation of indexed
% pattern matching.}

\vspace{-2.0ex}
\paragraph{Theory}

% \subsection{Type Theory with Convertibility Assumptions}

We propose a target type theory for a language with \swith by way of
introducing a new contextual judgement for convertibility 
assumptions, following \cite{altenkirch2011case}. We denote a context |Γ|
extended by an equation between terms |t₁|, |t₂| with |Γ ▷ t₁ ~ t₂|.

% \[
% \frac{
% |⊢ Γ ctx|,\quad |Γ ⊢ t₁, t₂ : A|
% }{
% |⊢ Γ ▷ t₁ ~ t₂ ctx|
% }
% \]

% We aim to retain both decidable conversion and the judgemental
% β and η rules that give judgemental equality its power in existing 
% theorem provers based on intensional type theory (ITT).
Similar judgemental-equality-extending constructs 
have also been explored as an alternative to
judgemental computation rules \cite{sjoberg2015programming},
in the setting of
dependent Haskell \cite{weirich2017specification, liu2023dependently} and more
generally in synthetic ∞-category theory 
\cite{riehl2017synthetic} (namely topes),
cubical type theory
%\footnote{The presentation in 
%\cite{angiuli2025principles} is especially reminiscent of our substitution
%calculus.} 
\cite{cohen2015cubical, angiuli2021syntax} (namely cofibrations),
to control unfolding \cite{gratzer2025controlling} and record
patching \cite{zhang2023three}.

% We can think of supporting context extension by |t₁ ~ t₂| as similar to adding
% an extensional identity type former to the theory, except these convertibility
% assumptions are not first-class (so they cannot appear in the domain
% or range of a |Π| type, or any type former, for that matter).

% We extend parallel substitutions to account for these convertibility 
% assumptions. Concretely, to substitute from a context |Γ| extended
% with a convertibility assumption |t₁ ~ t₂|, |t₁| must be convertible to
% |t₂| in |Δ|.
% 
% \[
% \frac{\begin{matrix}
% |Δ ⊩ δ : Γ|,\quad |Δ ⊢ t₁ [ δ ] ≡ t₂ [ δ ] : A [ δ ]| 
% \end{matrix}}{
% |Δ ⊩ δ , t₁≡t₂ : Γ ▷ t₁ ~ t₂|
% }
% \]
% 
% To make reflection provable (if |t₁ ~ t₂| is in the context, then 
% |t₁ ≡ t₂| should hold), it is sufficient to ensure the above way of building
% substitution from contexts with convertibility assumptions is an isomorphism
% (we can project from the identity substitution, and then weaken as necessary).
% We give the rules for these projections explicitly.

% p/q version
%\begin{minipage}{0.4\textwidth}
%\[
%\frac{}{
%|Γ ▷ t₁ ~ t₂ ⊩ p~ : Γ|
%}
%\]
%\end{minipage}
%\begin{minipage}{0.5\textwidth}
%\[
%\frac{}{
%|Γ ▷ t₁ ~ t₂ ⊢ t₁ [ p~ ] ≡ t₂ [ p~ ] : A [ p~ ]|
%}
%\]
%\end{minipage}


% Projections version
% \phantom{a}
% 
% \noindent
% \begin{minipage}{0.35\textwidth}
% \[
% \frac{
% |Δ ⊩ δ : Γ ▷ t₁ ~ t₂| 
% }{
% |Δ ⊩ π₁~ δ : Γ|
% }
% \]
% \end{minipage}
% \begin{minipage}{0.6\textwidth}
% \[
% \frac{
% |Δ ⊩ δ : Γ ▷ t₁ ~ t₂| 
% }{
% |Δ ⊢ t₁ [ π₁~ δ ] ≡ t₂ [ π₁~ δ ] : A [ π₁~ δ ]|
% }(|π₂~|)
% \]
% \end{minipage}
% 
% \phantom{a}
% 

% To bind convertibility assumptions, we need to introduce an appropriate
% language construct.

We bind convertibility assumptions with a form of 
\emph{local equality reflection}: given a 
propositional identity |p : t₁ = t₂| we bind
both |t₁ ~ t₂| and |p ~ refl| in the body. 
To retain good metatheoretical properties (subject reduction, decidable
typechecking etc.) we make reflection \emph{second-class}, only available at the 
top-level.
% \footnote{%
% Another approach here could be to aim to elaborate a surface language with
% local reflection into a core type theory with only eliminators,
% analagous to the work on elaborating dependent pattern 
% matching \cite{goguen2006eliminating, cockx2016eliminating}.}
This is in keeping with Agda's generative pattern matching and
gives us the freedom to syntactically restrict 
equations (e.g. disallowing overlap), 
without endangering stability under substitution.

% To retain decidability of typechecking, we must restrict the set of
% equations we can 
% reflect.\footnote{By congruence and large elimination, inconsistent equations 
% collapse the
% judgemental equality, but detecting such inconsistencies quickly becomes 
% undecidable.
% 
% For example, take two closed |ℕ → 𝔹| functions, 
% |f, g : ℕ → 𝔹|. To determine whether the equation |f ~ g| is inconsistent
% we need to check if there exists an input natural number on which |f| and |g| 
% return distinct Booleans. If |f| is the function that constantly returns
% |true| and |g| is a function that runs a particular Turing machine for |n|
% steps, returning |false| only if it halts, then this is equivalent to
% deciding the halting problem.}

% We need a language construct to bind convertibility assumptions. Unfortunately,
% doing this with a first-class term former 
% (\emph{local equality reflection}) is unwieldy.

% We can arrive at one such construct by aiming to replace
% the eliminator for propositional identity types (for simplicity, we elide 
% transports over judgemental equality). 
% 
% \[
% \frac{\begin{matrix}
% |Γ ⊢ eq : t₁ = t₂|,\quad |Γ ▷ t₁ ~ t₂ ▷ eq ~ refl ⊢ u : A|
% \end{matrix}}{
% |Γ ⊢ reflect eq in u : A|
% }
% \]
% 
% \[
% \frac{\begin{matrix}
% |Γ ▷ t ~ t ▷ eq ~ refl ⊢ u : A|
% \end{matrix}}{
% |Γ ⊢ reflect refl in u ≡ u [ id , t≡t , refl≡refl ] : A|
% }(|reflectβ|)
% \]
% 
% We call this principle local equality reflection, noting the similarity with
% the equality reflection rule from extensional type theory (ETT), which enables
% turning |Γ ⊢ eq : t₁ = t₂| into |Γ ⊢ t₁ ≡ t₂ : A| directly.
% 
% While the simplicity is nice, unfortunately, 
% typechecking unrestricted local equality reflection
% is undecidable. The issue is that, by large elimination and congruence,
% inconsistent equations collapse the
% judgemental equality, so reduction under inconsistent equations might loop. 
% This means we need to detect when equations are 
% inconsistent, but in type theory with natural numbers, this is 
% undecidable.\footnote{For example, take two closed |ℕ → 𝔹| functions, 
% |f, g : ℕ → 𝔹|. To determine whether the equation |f ~ g| is inconsistent
% we need to check if there exists an input natural number on which |f| and |g| 
% return distinct Booleans. If |f| is the function that constantly returns
% |true| and |g| is a function that runs a particular Turing machine for |n|
% steps, returning |false| only if it halts, then this is equivalent to
% deciding the halting problem.}
% 
% Interestingly, while typechecking is undecidable, the resulting theory
% from adding local equality reflection appears to still be meaningfully more
% \textit{intensional} than ETT. Specifically, we cannot derive function
% extensionality from \reflect alone.
% On the other hand, deriving UIP is easy. We just set |A :≡ eq = refl|, and
% |u :≡ refl|.

% \subsection{Taming Local Equality Reflection}

% We would like to better control local equality reflection,
% in order to regain decidable typechecking and possibly independence from UIP. 
% Concretely, we want to add side conditions to |reflect_in_| about
% |t₁| and |t₂| in order to only allow a particular subset of equations.

% However, many useful side conditions
% (such as terms being of neutral form, or different equations not overlapping 
% etc.) break stability of typing under substitution.\footnote{Stability of 
% under substitution is necessary for 
% key metatheoretical properties like subject reduction.} Our solution is
% to make reflection second-class

% As an example,
% consider that a context with |x ~ true| and |y ~ false| is consistent,
% but if we apply the substitution, |x / y|, we are left with inconsistent 
% equations |x ~ true| and |x ~ false|.\footnote{In principle, it might be 
% possible to detect judgementally inconsistent
% sets of equations (and fix other confluence issues) using techniques from
% term rewriting such as ground completion or equality saturation. 
% However, adapting these techniques to the setting of type theory 
% (with |β|-equations and large elimination) while ensuring termination
% appears non-trivial.}

% We note, however, that this is not too different from the situation with
% dependent pattern matching: the success of LHS unification is certainly
% not stable under substitution either. We therefore reuse the same trick:
% reflection should be second-class, only available at the top-level.\footnote{%
% Another approach here could be to aim to elaborate a surface language with
% local reflection into a core type theory with only eliminators,
% analagous to the work on elaborating dependent pattern 
% matching \cite{goguen2006eliminating, cockx2016eliminating}.}

% The improvement proposed by \swith is 
% simply that will be able to support a much larger class of equations
% in pattern matches. 

% Formally, we introduce a notion of global
% definition signatures. 
% Terms, types and substitutions are now defined with respect to a
% signature and a local context, written |Ξ ∣ Γ|.
% We reuse contexts
% for definition telescopes and substitutions for argument instantiations
% (note that \reflect is not a term former - it is \textit{only} available
% as a top-level construct in signatures).
% 
% 
% \[\frac{\begin{matrix}
% |⊢ Ξ sig|,\quad |Ξ ∣ Γ ⊢ eq : t₁ = t₂|,\quad 
% |Ξ ∣ Γ ▷ t₁ ~ t₂ ▷ eq ~ refl ⊢ u : A [ p~ ]|
% \end{matrix}}
% {|⊢ Ξ ▷ (Γ ⊢ reflect eq in u : A) sig|}\]
% 
% \[\frac{
% }{
% |Ξ ▷ (Γ ⊢ reflect eq in u : A) ∣ Γ [ p𝒮 ] ⊢ call : A [ p𝒮 ]|
% }\]
% 
% \[\dfrac{\begin{matrix}
% |Ψ ∣ Δ ⊩ δ : Ξ ▷ (Γ ⊢ reflect eq in u : A) ∣ Γ [ p𝒮 ]|,\\ 
% |Ψ ∣ Δ ⊢ t₁ [ p𝒮 ⨾ δ ] ≡ t₂ [ p𝒮 ⨾ δ ] : A [ p𝒮 ⨾ δ ]|,\\  
% |Ψ ∣ Δ ⊢ eq [ p𝒮 ⨾ δ ] ≡ refl : t₁ [ p𝒮 ⨾ δ ] = t₂ [ p𝒮 ⨾ δ ]|
% \end{matrix}}{
% |Ψ ∣ Δ ⊢ call [ δ ] ≡ u [ p𝒮 ⨾ (δ , t₁≡t₂ , eq≡refl) ] : A [ p𝒮 ⨾ δ ]|
% }(\textit{callβ})\]
% 
% With this set-up, we can freely constrain the convertibility
% assumptions inside telescopes
% of top-level definitions, without worrying about stability under 
% substitution.\footnote{Intuitively, substitutions build up at |call|s right up 
% until the blocked equation reduces to |refl|, at which point we can
% safely expand the body.}
% For example,
% we could require all sides of equations to be neutral and non-overlapping to
% enable a conversion checking strategy where we check conversion modulo
% assumptions after β-normalising (similar to the common strategy of
% delaying η-conversion). Alternatively, we might want to consider equations 
% where only one side is neutral, which requires us to eagerly apply rewrites
% mutually with reduction. 

The theory for Booleans was explored in detail in \cite{burke2025local} by
extending normalisation by evaluation with an extra step during 
unquote/reflect: before embedding a β-neutral term into the values, we need
to first syntactically compare it with the LHSs of the in-scope rewrites.
This approach is slightly unsatisfying though, because it (temporarily)
breaks the conversion relation, requiring a definition of syntax that allows
distinguishing convertible terms (i.e. type theory as a setoid rather than 
a quotient inductive type), and for a fully formal proof, syntactic lemmas
such as confluence of reduction must be proven. We are investigating
an alternative approach based on stabilised neutrals 
\cite{sterling2021normalization}.

Additionally, equations at more complicated types than Booleans
pose some extra difficulties. For example, the natural number equation
|n ~ su (f n)| must be oriented towards |su (f n)| to unblock β
reductions, but also loops if we apply it naively.

Finally, we note another interesting side condition on reflected
equations. If we enforce that both sides, |t₁| and |t₂|, 
are not convertible 
(inspired by
\cite{cockx2016eliminating}), then it does not appear to be possible to
replicate extensional type theory's standard proof of UIP.
%\footnote{An alternative
%restriction to try and avoid UIP could be to only bind |t₁ ~ t₂| without
%the additional |eq ~ refl|. This would, however, severely limit \reflect's 
%power, making it impossible to prove even the |J| rule.}
This begs the following question: 

\textbf{Open Question:} Is MLTT extended with global definitions and local
per-definition equality reflection, conditional on |t₁ ≢ t₂|, 
consistent with HoTT?

% \appendix
% \section{Some Typing Rules}
% 
% \textbf{TODO:} Typing rules can go here...

% \bibliographystyle{plain}
% \bibliography{main}
\begingroup
\sloppy
\printbibliography
\endgroup

\end{document}

