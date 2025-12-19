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
\newcommand{\AgdaCong}{\AgdaFunction{cong}\xspace}
\newcommand{\xorEven}{\AgdaFunction{xor-even}\xspace}

\title{Smart \with}

\author{Nathaniel Burke}

\institute{
  TU Delft, Netherlands\\
  \email{n.burke@tudelft.nl}
}

\authorrunning{Burke}

\titlerunning{Smart \with}

\begin{document}

\maketitle

\begin{abstract}
  In \cite{mcbride2004view}, McBride and McKinna proposed a syntax for 
  pattern matching in type
  theory named the \with construct,
  enabling matches on intermediary computations whilst generalising the
  context (abstracting over the matched term) to support dependent 
  elimination.

  This feature is implemented in Agda under the name \with-abstractions. 
  While useful, the feature can also be a footgun. 
  Proving simple laws about definitions defined by \with-abstraction is 
  often fiddly and sometimes impossible due to failures in the generalisation
  step producing ``ill-typed \with-abstraction'' errors.

  We propose an improved \with-abstraction mechanism leveraging ongoing
  work to implement local rewrite rules in Agda, inspired by the
  \scase proposal of Altenkirch et al. \cite{altenkirch2011case}. 
  Essentially, we
  aim to support local equality reflection for a subset of
  equations under which we can maintain decidable typechecking.
\end{abstract}

\begin{code}[hide]
{-# OPTIONS --allow-unsolved-metas #-}
\end{code}

\section{Motivation}

We begin with a small Agda example to show where \with-abstractions fall short,
starting by defining the datatype of Booleans with negation and exclusive or,
albeit under some slightly more evocative names.

\noindent
\begin{minipage}{0.275\textwidth}
\begin{code}
data Parity : Set where
  even odd : Parity
\end{code}
\end{minipage}
\begin{minipage}{0.25\textwidth}
\begin{code}
inv : Parity → Parity
inv even  = odd
inv odd   = even
\end{code}
\end{minipage}
\begin{minipage}{0.3\textwidth}
\begin{code}
_xor_ : Parity → Parity → Parity
even  xor q = q
odd   xor q = inv q
\end{code}
\end{minipage}

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

variable
  p q : Parity

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

Our aim is to implement and prove properties of arithmetic on natural numbers,
indexed by their parity.\footnote{We could define natural numbers independently 
of parity, and then
prove properties about how parity commutes with arithmetic operations 
extrinsically.
By working intrinsically instead, we hope to reap a golden ratio reduction in
lines of code (\cite{wadler2022plfa}, DeBruijn, ``Intrinsic typing is
golden'').

We could also dodge some of the issues that we are about to run into by 
breaking
\su into two constructors, keeping successor of \odd and \even
separate. However,
this obligates our later definitions to handle an extra case and furthermore
relies on the index being finite (so this trick cannot be
replicated for types like length-indexed vectors \AgdaVec, finite sets 
\Fin, intrinsically-typed terms \Tm etc.).}

\begin{code}
data Nat : Parity → Set where
  ze : Nat even
  su : Nat (inv p) → Nat p
\end{code}

\begin{code}[hide]
variable
  n m l : Nat p
\end{code}

Addition of natural numbers \xor{}s their respective parities. The base case
is easy: the typechecker automatically unifies \AgdaBound{p} with \even
and reduces \even \xor \AgdaBound{q} to \AgdaBound{q}.

\noindent
\begin{minipage}{0.5\textwidth}
\begin{code}
_+_ : Nat p → Nat q → Nat (p xor q)
\end{code}
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{code}
ze + m = m
\end{code}
\end{minipage}

The inductive step requires us to actually do some work. 
\inv \AgdaBound{p} \xor \AgdaBound{q} is stuck, so we need to
prove a lemma about how \inv commutes with \xor
(concretely, \inv \AgdaBound{p} \xor \AgdaBound{q} \AgdaEq \inv 
\AgdaParens{\AgdaBound{p} \xor \AgdaBound{q}}).


This is reasonable enough, but then we face 
a more technical challenge in how to actually 
apply this lemma. Aiming for convenience, we gravitate towards 
Agda's \rewrite construct
(which desugars to \with-abstraction plus a match on \refl) 
capable of applying one-off 
rewrites to the context in the direction of a propositional identity.
Unfortunately, after matching on
\su \AgdaBound{n}, nothing in the context directly has type 
\inv \AgdaBound{p} \xor \AgdaBound{q}. To force the rewrite to actually
do something, we additionally \with-abstract 
the result of
the recursive call (at type 
\Nat \AgdaParens{\inv \AgdaBound{p} \xor \AgdaBound{q}}).

\begin{code}
_+_ {p = p} {q = q} (su n) m
  with     n+m ← n + m
  rewrite  inv-xor {p = p} {q = q}
  = su n+m
\end{code}

Finally, we aim to prove that zero is a right-identity of addition. Technically,
this theorem is not even type correct without knowing 
\AgdaBound{p} \xor \even \AgdaEq \AgdaBound{p} but proving this is easy enough.
To formulate the lemma, we use a dependent identity type.

\begin{code}[hide]
+ze-sig : Nat p → Set
+ze-sig {p = p} n 
  with     n′ ← n + ze 
  rewrite  xor-even {p = p}
  = n′ ≡ n

_≡[_]≡_ : A → A ≡ B → B → Set _
x ≡[ refl ]≡ y = x ≡ y
infix 4 _≡[_]≡_
\end{code}

\begin{code}
+ze : n + ze ≡[ cong Nat xor-even ]≡ n
\end{code}

Following the definition of addition itself, the base case is easy, but
the inductive case is significantly harder. To make
\su \AgdaBound{n} \AgdaAdd \ze reduce, we need to repeat the same
\with-abstraction and \rewrite.

\begin{code}
+ze {n = ze} = refl
+ze {n = su {p = p} n}
  with     n′ ← n + ze
  rewrite  inv-xor {p = p} {q = even}
  = {!!}
\end{code}

The goal asks us to prove 
\su \AgdaBound{n′} \AgdaDepEq{\AgdaCong \Nat \xorEven} 
\su \AgdaBound{n}. Manipulating dependent identity is its own can of worms, but
more pressingly, this is simply impossible to prove: we have lost the connection 
between \AgdaBound{n′} and \AgdaBound{n} \AgdaAdd \ze. Since 2.6.2, Agda builds
in the ``inspect idiom'', allowing us to write ``\AgdaIn \AgdaBound{eq}'' after
a \with-abstraction to bind a propositional equality between the abstracted
term and the pattern, but if we attempt to bind \AgdaIn \AgdaBound{eq}
in \AddZe, we hit an error: 

\noindent
\begin{myagda}
\>[0]\AgdaError{inv p xor even != lhs of type Parity}%0
\\
\>[0]\AgdaError{when checking that the type}%
\\
\>[0]...%
\\
\>[0]\AgdaError{of the generated with function is well-formed}%
\end{myagda}

The issue is with how \rewrite only applies a one-off rewrite to the
context. For 
\AgdaBound{eq} : \AgdaBound{n′} \AgdaEq \AgdaBound{n} \AgdaAdd \ze 
to typecheck, both \AgdaBound{n′} and \AgdaBound{n} \AgdaAdd \ze must have
the same type. This is the case until we \rewrite by 
\InvXor \AgdaBraces{\AgdaArgument{p} \AgdaDefEq \AgdaBound{p}} 
\AgdaBraces{\AgdaArgument{q} \AgdaDefEq \even}. 
\AgdaBound{n′}'s type is rewritten, but \AgdaBound{n} \AgdaAdd \ze
is left alone, and now the context no longer typechecks.

Experienced Agda users might find following along with this code example 
slightly frustrating.
Conventional wisdom suggests sidestepping these issues by 
forgoing automation features like \with-abstraction
and its derivatives. Instead, we should program with raw transports.

Transports have a bit of a UX problem (needing to manually specify exactly where
the equation should be used is tedious), but more problematically,
proving properties of functions involving transports risks a 
prolonged battle with
``transport-hell'', a problem whose magnitude is corroborated by 
the large arsenal of folklore 
techniques for fighting it: manually abstracting over expressions to
massage equations into a fragment accepted by indexed pattern matching, 
redefining transport for specific types by induction on the target rather than 
the identity proof \cite{2024fin}, using ``John Major'' heterogeneous 
equality \cite{mcbride2000dependently} such that outermost transports can
be absorbed \cite{saffrich2024intrinsically},
global rewrite rules \cite{cockx2020type, cockx2021taming, leray2024rewster} 
etc. 

Our perspective is that some manual transport reasoning is 
inherent to the design of ITT, but for many cases (especially when the
equations are at neutral or first-order types) we can do a much better job than
current proof assistants. Concretely, the typechecker should fully internalise
the equations introduced via \with-abstraction, and apply these equations
automatically. 

With respect to implementation, we propose building on top of (a subset of) 
local rewrite rules, as proposed in \cite{leray2025encode} (specifically, we
only need ``ground'' rules, in the sense that variables in 
equations are always bound in the context or via higher-order matching).

Such an improved \with-abstraction
mechanism also resolves, \textit{en passant}, some of the frustrating UX
problems with
dependent pattern matching (termed ``green slime'' in 
\cite{mcbride2012polynomial}). Rather than throwing an error as soon as
LHS unification fails, we can instead just force the index equations
to hold with rewriting.

\section{Theory}

\subsection{Type Theory with Convertibility Assumptions}

We propose a target type theory for a language with \swith by way of
including a new contextual judgement for convertibility 
assumptions, following \cite{altenkirch2011case}. 

\[
\frac{
|⊢ Γ ctx|,\quad |Γ ⊢ t₁, t₂ : A|
}{
|⊢ Γ ▷ t₁ ~ t₂ ctx|
}
\]

Constructs similar to this have also been explored as an alternative to
judgemental computation rules \cite{sjoberg2015programming},
and in the setting of
dependent Haskell \cite{weirich2017specification, liu2023dependently}.
We aim to retain both decidable conversion and the judgemental
β and η rules that give judgemental equality its power in existing 
theorem provers based on intensional type theory (ITT).

Type theories featuring second-class propositions in contexts
which nonetheless manipulate the judgemental equality have also been explored
in the context of synthetic ∞-category theory \cite{riehl2017synthetic} 
(namely topes),
cubical type theory\footnote{The presentation in 
\cite{angiuli2025principles} is especially reminiscent of our substitution
calculus.} 
\cite{cohen2015cubical, angiuli2021syntax} (namely cofibrations),
to control unfolding \cite{gratzer2025controlling} and more 
\cite{zhang2023three}.

We can think of supporting context extension by |t₁ ~ t₂| as similar to adding
an extensional identity type former to the theory, except these convertibility
assumptions are not first-class (so they cannot appear in the domain
or range of a |Π| type, or any type former, for that matter).

We extend parallel substitutions to account for these convertibility 
assumptions. Concretely, to substitute from a context |Γ| extended
with a convertibility assumption |t₁ ~ t₂|, |t₁| must be convertible to
|t₂| in |Δ|.

\[
\frac{\begin{matrix}
|Δ ⊩ δ : Γ|,\quad |Δ ⊢ t₁ [ δ ] ≡ t₂ [ δ ] : A [ δ ]| 
\end{matrix}}{
|Δ ⊩ δ , t₁≡t₂ : Γ ▷ t₁ ~ t₂|
}
\]

To make reflection provable (if |t₁ ~ t₂| is in the context, then 
|t₁ ≡ t₂| should hold), it is sufficient to ensure the above way of building
substitution from contexts with convertibility assumptions is an isomorphism
(we can project from the identity substitution, and then weaken as necessary).
We give the rules for these projections explicitly.

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
\phantom{a}

\noindent
\begin{minipage}{0.35\textwidth}
\[
\frac{
|Δ ⊩ δ : Γ ▷ t₁ ~ t₂| 
}{
|Δ ⊩ π₁~ δ : Γ|
}
\]
\end{minipage}
\begin{minipage}{0.6\textwidth}
\[
\frac{
|Δ ⊩ δ : Γ ▷ t₁ ~ t₂| 
}{
|Δ ⊢ t₁ [ π₁~ δ ] ≡ t₂ [ π₁~ δ ] : A [ π₁~ δ ]|
}(|π₂~|)
\]
\end{minipage}

\phantom{a}

To bind convertibility assumptions, we need to introduce an appropriate
language construct. We can arrive at one such construct by aiming to replace
the eliminator for propositional identity types (for simplicity, we elide 
transports over judgemental equality). 

\[
\frac{\begin{matrix}
|Γ ⊢ eq : t₁ = t₂|,\quad |Γ ▷ t₁ ~ t₂ ▷ eq ~ refl ⊢ u : A|
\end{matrix}}{
|Γ ⊢ reflect eq in u : A|
}
\]

\[
\frac{\begin{matrix}
|Γ ▷ t ~ t ▷ eq ~ refl ⊢ u : A|
\end{matrix}}{
|Γ ⊢ reflect refl in u ≡ u [ id , t≡t , refl≡refl ] : A|
}(|reflectβ|)
\]

We call this principle local equality reflection, noting the similarity with
the equality reflection rule from extensional type theory (ETT), which enables
turning |Γ ⊢ eq : t₁ = t₂| into |Γ ⊢ t₁ ≡ t₂ : A| directly.

While the simplicity is nice, unfortunately, 
typechecking unrestricted local equality reflection
is undecidable. The issue is that, by large elimination and congruence,
inconsistent equations collapse the
judgemental equality, so reduction under inconsistent equations might loop. 
This means we need to detect when equations are 
inconsistent, but in type theory with natural numbers, this is 
undecidable.\footnote{For example, take two closed |ℕ → 𝔹| functions, 
|f, g : ℕ → 𝔹|. To determine whether the equation |f ~ g| is inconsistent
we need to check if there exists an input natural number on which |f| and |g| 
return distinct Booleans. If |f| is the function that constantly returns
|true| and |g| is a function that runs a particular Turing machine for |n|
steps, returning |false| only if it halts, then this is equivalent to
deciding the halting problem.}

Interestingly, while typechecking is undecidable, the resulting theory
from adding local equality reflection appears to still be meaningfully more
\textit{intensional} than ETT. Specifically, we cannot derive function
extensionality from \reflect alone.
On the other hand, deriving UIP is easy. We just set |A :≡ eq = refl|, and
|u :≡ refl|.

\subsection{Taming Local Equality Reflection}

We would like to better control local equality reflection,
in order to regain decidable typechecking and possibly independence from UIP. 
Concretely, we want to add side conditions to |reflect_in_| about
|t₁| and |t₂| in order to only allow a particular subset of equations.

Unfortunately, many useful such side conditions, such as terms
being of neutral form, or different equations not overlapping etc.
are properties that turn out to be unstable under substitution. As an example,
consider that a context with |x ~ true| and |y ~ false| is consistent,
but if we apply the substitution, |x / y|, we are left with inconsistent 
equations |x ~ true| and |x ~ false|.\footnote{In principle, it might be 
possible to detect judgementally inconsistent
sets of equations (and fix other confluence issues) using techniques from
term rewriting such as ground completion or equality saturation. 
However, adapting these techniques to the setting of type theory 
(with |β|-equations and large elimination) while ensuring termination
appears non-trivial.}

We note, however, that this is not too different from the situation with
dependent pattern matching: the success of LHS unification is certainly
not stable under substitution either. We therefore reuse the same trick:
reflection should be second-class, only available at the top-level.\footnote{%
Another approach here could be to aim to elaborate a surface language with
local reflection into a core type theory with only eliminators,
analagous to the work on elaborating dependent pattern 
matching \cite{goguen2006eliminating, cockx2016eliminating}.}

% The improvement proposed by \swith is 
% simply that will be able to support a much larger class of equations
% in pattern matches. 

To make this trick formal, we introduce notions of global
definition signatures and signature weakenings. 
Terms, types and substitutions are now defined with respect to a
signature and a local context, written |Ξ ∣ Γ|.
We reuse contexts
for definition telescopes and substitutions for argument instantiations
(note that \reflect is no longer a term former - it is \textit{only} available
as a top-level construct in signatures).


\[\frac{\begin{matrix}
|⊢ Ξ sig|,\quad |Ξ ∣ Γ ⊢ eq : t₁ = t₂|,\quad 
|Ξ ∣ Γ ▷ t₁ ~ t₂ ▷ eq ~ refl ⊢ u : A [ p~ ]|
\end{matrix}}
{|⊢ Ξ ▷ (Γ ⊢ reflect eq in u : A) sig|}\]

\textbf{TODO:} Explain these typing rules (also maybe we need to make weakening 
implicit and/or come up with some better notation because this is quite 
ugly, even without the transports...)

\[\frac{
}{
|Ξ ▷ (Γ ⊢ reflect eq in u : A) ∣ Γ [ p𝒮 ] ⊢ call : A [ p𝒮 ]|
}\]

\[\dfrac{\begin{matrix}
|Ψ ∣ Δ ⊩ δ : Ξ ▷ (Γ ⊢ reflect eq in u : A) ∣ Γ [ p𝒮 ]|,\\ 
|Ψ ∣ Δ ⊢ t₁ [ p𝒮 ⨾ δ ] ≡ t₂ [ p𝒮 ⨾ δ ] : A [ p𝒮 ⨾ δ ]|,\\  
|Ψ ∣ Δ ⊢ eq [ p𝒮 ⨾ δ ] ≡ refl : t₁ [ p𝒮 ⨾ δ ] = t₂ [ p𝒮 ⨾ δ ]|
\end{matrix}}{
|Ψ ∣ Δ ⊢ call [ δ ] ≡ u [ p𝒮 ⨾ (δ , t₁≡t₂ , eq≡refl) ] : A [ p𝒮 ⨾ δ ]|
}(\textit{callβ})\]

With this set-up, we can freely constrain the convertibility
assumptions inside telescopes
of top-level definitions, without worrying about stability under 
substitution.\footnote{Intuitively, substitutions build up at |call|s right up 
until the blocked equation reduces to |refl|, at which point we can
safely expand the body.}
For example,
we could require all sides of equations to be neutral and non-overlapping to
enable a conversion checking strategy where we check conversion modulo
assumptions only after β-normalising (similar to the common strategy of
delaying η-conversion). Alternatively, we might want to consider equations 
where only one side is neutral, which requires us to eagerly apply rewrites
mutually with reduction. 

The case for Booleans was explored in detail in \cite{burke2025local} by
extending normalisation by evaluation with an extra step during 
unquote/reflect: before embedding a β-neutral form into the values, we need
to first syntactically compare it with the LHSs of the in-scope rewrites.
This approach is slightly unsatisfying though, because it (temporarily)
breaks the conversion relation, requiring a definition of syntax that allows
distinguishing convertible terms (i.e. type theory as a setoid rather than 
a quotient inductive type), and for a fully formal proof, syntactic lemmas
such as confluence of single-step reduction must be proven. We are investigating
an alternative approach based on stabilised neutrals 
\cite{sterling2021normalization}.

We also note that equations at more complicated types than Booleans
pose some extra difficulties. For example, the natural number equation
|n ≡ su (f n)| must be oriented towards |su (f n)| to unblock β
reductions, but also loops if we apply it naively. It appears that 
we need some form of occurs check.

Finally, we note another interesting side condition on reflected
equations. If we enforce that the sides of the equation, |t₁| and |t₂|, 
are not convertible 
(inspired by
\cite{cockx2016eliminating}), then it does not appear to be possible to
replicate the standard ETT proof of UIP.\footnote{An alternative
restriction to try and avoid UIP could be to only bind |t₁ ~ t₂| without
the additional |eq ~ refl|. This would, however, severely limit \reflect's 
power, making it impossible to prove even the |J| rule.}
This begs the following question: 

\textbf{Open Question:} Is MLTT extended with global definitions and local
per-definition equality reflection, conditional on |t₁ ≢ t₂|, 
consistent with HoTT?

% \bibliographystyle{plain}
% \bibliography{main}
\begingroup
\sloppy
\printbibliography
\endgroup

\end{document}

