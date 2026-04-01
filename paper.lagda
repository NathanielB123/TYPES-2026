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
\newcommand{\srewrite}{smart \AgdaKeyword{rewrite}\xspace}
\newcommand{\SWITH}{Smart \AgdaKeyword{with}\xspace}
\newcommand{\scase}{smart \AgdaKeyword{case}\xspace}
\newcommand{\SCASE}{Smart \AgdaKeyword{case}\xspace}
\newcommand{\reflect}{\AgdaKeyword{reflect}\xspace}
\newcommand{\AgdaIn}{\AgdaKeyword{in}\xspace}
% Rocq keyword, not Agda keyword, but oh well
\newcommand{\match}{\AgdaKeyword{match}\xspace}

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
\newcommand{\AgdaAddDef}{\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}+\AgdaUnderscore{}}}}
\newcommand{\AgdaAp}{\AgdaFunction{ap}\xspace}
\newcommand{\xorEven}{\AgdaFunction{xor-even}\xspace}
\newcommand{\invXor}{\AgdaFunction{inv-xor}\xspace}

\title{Smart \with}

\author{Nathaniel Burke}

\institute{
  TU Delft, Netherlands, \email{n.burke@tudelft.nl}
}

\authorrunning{Burke}

\titlerunning{Smart \with}

\begin{document}

\maketitle

\begin{code}[hide]
{-# OPTIONS --allow-unsolved-metas #-}
\end{code}

\paragraph{Motivation}

The \with construct, proposed by McBride and McKinna \cite{mcbride2004view},
extends dependent pattern matching \cite{coquand1992pattern} 
with a mechanism for matching on intermediary
computations, whilst generalising the
context to support dependent 
elimination.
This feature is implemented in Agda under the name \with-abstractions. 
While useful, the feature can also be a footgun.
Proving simple laws about definitions by \with-abstraction is 
often fiddly and sometimes impossible due to failures in the generalisation
step producing \emph{ill-typed \with-abstraction} errors \cite{agda2024with}.

To illustrate the problem, and our solution, 
consider the following attempt to prove
that filtering a list twice with the same predicate returns the same result
as filtering once\footnote{The examples in this abstract are also
available self-contained \cite{nathaniel2026examples}.}.

\begin{code}[hide]
open import Agda.Primitive
open import Agda.Builtin.List renaming (_∷_ to _,-_)
open import Agda.Builtin.Bool renaming (true to tt; false to ff)
open import Agda.Builtin.Equality

variable
  ℓ : Level
  A B : Set _
  f : A → B
  xs ys : List _
  x y : A
  b : Bool

-- Utils
sym : x ≡ y → y ≡ x
sym refl = refl

transp : (P : A → Set) → x ≡ y → P x → P y
transp P refl px = px

ap : (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

infix 0 if_then_else_

if_then_else_ : Bool → A → A → A
if tt then t else f = t
if ff then t else f = f
\end{code}

\noindent
\begin{minipage}{0.45\textwidth}
\begin{code}
filter : (A → Bool) → List A → List A
filter f []         = []
filter f (x ,- xs)  with f x
... | tt = x ,- filter f xs
... | ff = filter f xs
\end{code}

\end{minipage}
\begin{minipage}{0.4\textwidth}

% filter-twice : filter f (filter f xs) ≡ filter f xs
% filter-twice          {xs = []}       = refl
% filter-twice {f = f}  {xs = x ,- xs}  with f x
% ... | tt = {!!}
% ... | ff = filter-twice {xs = xs}
\begin{myagda}%
\>[0]\AgdaFunction{filter-twice}\AgdaSpace{}%
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
\>[0]\AgdaFunction{filter-twice}%
\>[23]\AgdaSymbol{\{}\AgdaArgument{xs}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{[]}\AgdaSymbol{\}}%
\>[39]\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{refl}\<%
\\
\>[0]\AgdaFunction{filter-twice}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{f}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{f}\AgdaSymbol{\}}%
\>[23]\AgdaSymbol{\{}\AgdaArgument{xs}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{x}\AgdaSpace{}%
\AgdaOperator{\AgdaInductiveConstructor{,-}}\AgdaSpace{}%
\AgdaBound{xs}\AgdaSymbol{\}}%
\>[39]\AgdaKeyword{with}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaBound{x}\<%
\\
\>[0]\AgdaSymbol{...}\AgdaSpace{}%
\AgdaSymbol{||}\AgdaSpace{}%
\AgdaInductiveConstructor{tt}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaHole{\{!!\}}\<%
\\
\>[0]\AgdaSymbol{...}\AgdaSpace{}%
\AgdaSymbol{||}\AgdaSpace{}%
\AgdaInductiveConstructor{ff}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaFunction{filter-twice}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{xs}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{xs}\AgdaSymbol{\}}\<%
\end{myagda}
\end{minipage}

The base case of \filterTwice is easy: the match on
\AgdaBraces{\AgdaArgument{xs} \AgdaDefEq \nil} substitutes \AgdaBound{xs} for
\nil in the context, allowing the \filter applications on both sides of
the goal to reduce to \nil.

The inductive case is harder. Because \filter is defined by \with-abstraction,
\filterTwice must repeat the match on \AgdaBound{f} \AgdaBound{x} to make
progress. In the false case, the goal reduces to exactly the induction 
hypothesis, but in the true case (left as a hole, \AgdaHole{\{!!\}}),
Agda displays the goal type as
\mbox{\filter \AgdaBound{f} \AgdaParens{\AgdaBound{x} \cons 
\filter \AgdaBound{f} \AgdaBound{xs}} 
\AgdaBar \AgdaBound{f} \AgdaBound{x} 
\AgdaEq \AgdaBound{x} \cons \filter \AgdaBound{f} \AgdaBound{xs}}.
The ``\AgdaBar \AgdaBound{f} \AgdaBound{x}'' syntax on the left-hand side 
denotes that the
outer \filter application is still stuck on \AgdaBound{f} \AgdaBound{x},
rather than reducing to \mbox{\AgdaBound{x} \cons \filter \AgdaBound{f} 
\AgdaParens{\filter \AgdaBound{f} \AgdaBound{xs}}}
as we might hope.

The problem is due a fundamental limitation in how \with-abstractions support
dependent elimination. Generalisation (during which the matched term is
abstracted
over)
is a one-off transformation so, \textbf{critically}, Agda does not 
``remember''
the equality between \AgdaBound{f} \AgdaBound{x} and \true.
Indeed, if we \with-abstract over \AgdaBound{f} \AgdaBound{x} once more, 
Agda will ask us to handle both the case when
\AgdaBound{f} \AgdaBound{x} is \true and when it is \false, but we already know
it is \true! 

Since version 2.6.2, Agda builds
in the \emph{inspect idiom}, allowing us to write ``\AgdaIn \AgdaBound{eq}'' 
after a \with-abstraction to bind a propositional identity between the 
abstracted term and the pattern. In the present example, 
this feature enables us to
complete the proof by \with-abstracting over \AgdaBound{f} \AgdaBound{x} once 
more, simultaneously with \AgdaBound{eq} to refute the false case:

\begin{code}[hide]
filter-twice : filter f (filter f xs) ≡ filter f xs
filter-twice {xs = []} = refl
\end{code}

\begin{code}
filter-twice {f = f} {xs = x ,- xs} with f x in eq
... | ff = filter-twice {xs = xs}
... | tt with f x | eq
... | tt | eq = ap (x ,-_) (filter-twice {xs = xs})
... | ff | () --- absurd
\end{code}

Even so, the workaround is tedious, and sometimes does not work at all.

% TODO: Do we want to introduce local rewrite rules at this point?
% Delaying the "real" examples is sad, but I think it might be a good idea
% for readability...
Inspired by the \scase proposal of Altenkirch et al. \cite{altenkirch2011case},
we propose an improved \with-abstraction mechanism for Agda. On our
work-in-progress branch \cite{nathaniel2026matches}, we can directly fill the 
original hole with
\AgdaFunction{ap}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{x}\AgdaSpace{}%
\AgdaOperator{\AgdaInductiveConstructor{,-\AgdaUnderscore{}}}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaFunction{filter-twice}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaArgument{xs}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{xs}\AgdaSymbol{\})}.

Our implementation builds upon (a subset\footnote{We
only need \emph{ground} rules: all variables in 
equations are bound in the context or via higher-order matching.} of)
local rewrite rules as proposed by Leray and
Winterhalter \cite{leray2025encode} and recently implemented in Agda 
\cite{nathaniel2026local}.
To elaborate \with-abstractions, Agda's existing generalisation procedure
first
normalises the context (and goal), then applies a one-off rewrite
(replacing occurrences of the matched term with a fresh argument)
and finally checks the context is still
well-typed. 
\SWITH, on the other hand, simply extends the context with a local
rewrite rule from the matched term to the fresh argument
(and this
rewrite rule is refined in the clauses). By no longer
having to normalise the entire context, we are also hopeful that 
\swith can be
made more performant than Agda's existing \with construct.

%TODO: I want to include this, but I think it makes more sense to have this
% later now...
%
% By carefully integrating local rewrite rules with indexed pattern matching
% we also aim to improve some of the frustrating UX
% problems of the latter (termed ``green slime'' in 
% \cite{mcbride2012polynomial}). Rather than throwing an error as soon as
% LHS unification fails, we should instead (where possible) force the index 
% equations to hold with rewriting.
\vspace{-2.0ex}
\paragraph{Indexed datatypes and \rewrite}

\SWITH is especially powerful when working with indexed datatypes. Consider
the following definition of natural numbers
indexed by parity:

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

\begin{code}[hide]
inv-inv : inv (inv p) ≡ p
inv-inv {p = even}  = refl
inv-inv {p = odd}  = refl

inv-xor : inv p xor q ≡ inv (p xor q)
inv-xor {p = even} = refl
inv-xor {p = odd}  = sym inv-inv

xor-even : p xor even ≡ p
xor-even {p = even} = refl
xor-even {p = odd}  = refl

variable
  n m l : Nat p
\end{code}

\begin{code}[hide]
-- _+_ : Nat p → Nat q → Nat (p xor q)
\end{code}

We will try to implement addition of \Nat{}s, \AgdaAddDef (which \xor{}s the 
respective
parities, \AgdaBound{p} and \AgdaBound{q}) as well as prove that \ze is a
right-identity of addition, \AddZe.
The base case of \AgdaAddDef
is easy, but the inductive step requires us to do some work. 
\inv \AgdaBound{p} \xor \AgdaBound{q} is stuck, so we must
prove a lemma about how \inv commutes with \xor
(concretely, \invXor \AgdaColon \inv \AgdaBound{p} \xor \AgdaBound{q} 
\AgdaEq \inv 
\AgdaParens{\AgdaBound{p} \xor \AgdaBound{q}}).

This is reasonable enough, but we then face 
a more technical challenge in how to actually 
use this lemma. Aiming for convenience,
we gravitate towards Agda's \rewrite construct. 
We first \with-abstract over the recursive call in order to get some variable
into the
context (\AgdaBound{n+m}) with type 
\mbox{\Nat \AgdaParens{\inv \AgdaBound{p} \xor \AgdaBound{q}}}.
Then, we \rewrite its type to the required 
\Nat \AgdaParens{\inv \AgdaParens{\AgdaBound{p} \xor \AgdaBound{q}}}
and apply successor.

\vspace{-1.5ex}
\noindent
\begin{minipage}{0.45\textwidth}
\begin{code}
_+_ : Nat p → Nat q → Nat (p xor q)
_+_ {p} {q} (su n) m
  with     n+m ← n + m
  rewrite  inv-xor {p} {q}
  = su n+m
\end{code}
\begin{code}[hide]
ze + m = m

_≡[_]≡_ : A → A ≡ B → B → Set _
x ≡[ refl ]≡ y = x ≡ y
infix 4 _≡[_]≡_

-- +ze : n + ze ≡[ ap Nat xor-even ]≡ n
\end{code}
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{code}
+ze : n + ze ≡[ ap Nat xor-even ]≡ n
+ze {n = su {p} n}
  with     n′ ← n + ze --- in eq
  rewrite  inv-xor {p} {even}
  = {!!}
\end{code}
\begin{code}[hide]
+ze {n = ze} = refl
\end{code}
\end{minipage}
\vspace{-1.5ex}

Note that inlining \AgdaBound{n+m} does not work.
\rewrite{} desugars to simultaneous
\with-abstraction over the left-hand-side and identity proof, and therefore 
inherits the same limitations: Agda does not 
``remember''
the equality between \inv \AgdaBound{p} \xor \AgdaBound{q} and
\inv \AgdaParens{\AgdaBound{p} \xor \AgdaBound{q}}.

Proving \AddZe is trickier. Technically, the theorem is not even type correct 
without knowing 
\mbox{\xorEven \AgdaColon \AgdaBound{p} \xor \even \AgdaEq \AgdaBound{p}} but 
proving this is easy 
enough. We then state the type of \AddZe with a dependent identity type.
In the inductive case, we first need to repeat the same
\with-abstraction and \rewrite to make
\su \AgdaBound{n} \AgdaAdd \ze reduce.
The remaining goal (\AgdaHole{\{!!\}}) asks us to prove 
\mbox{\su \AgdaBound{n′} \AgdaDepEq{\AgdaAp \Nat \xorEven} 
\su \AgdaBound{n}},
% Manipulating dependent identity is its own can of worms, but
% more pressingly, 
but this is impossible: we have lost the connection 
between \AgdaBound{n′} and \AgdaBound{n} \AgdaAdd \ze.
If we try to apply the inspect idiom again and bind ``\AgdaIn \AgdaBound{eq}''
in \AddZe, we hit the dreaded \emph{ill-typed \with-abstraction} error: 
\AgdaError{inv p xor even != lhs of type Parity when checking that the type} ...
\AgdaError{of the generated with function is well-formed}.

Again, the problem is \with-abstractions' one-off nature.
For 
\AgdaBound{eq} : \AgdaBound{n′} \AgdaEq \AgdaBound{n} \AgdaAdd \ze 
to typecheck, both \AgdaBound{n′} and \AgdaBound{n} \AgdaAdd \ze must have
the same type. This is the case until we apply the \rewrite.
\AgdaBound{n′}'s type is rewritten, but \AgdaBound{n} \AgdaAdd \ze
is left alone, and now the context no longer typechecks.

% Conventional Agda wisdom suggests sidestepping these issues by 
% forgoing automation features like \with-abstraction
% and its derivatives. Instead, we should program with raw transports.
% However, transports have a usability problem (manually specifying where
% to apply the equation is tedious), and more problematically,
% proving properties of functions involving transports still risks a 
% prolonged battle with
% ``transport-hell''.\footnote{A problem whose magnitude is corroborated by 
% the large arsenal of folklore techniques for fighting it: massaging
% equations into a fragment accepted by indexed pattern matching, 
% redefining transport by induction on the target 
% \cite{2024fin}, using ``John Major'' heterogeneous
% equality \cite{mcbride2000dependently, saffrich2024intrinsically},
% global rewrite rules \cite{cockx2020type, cockx2021taming, leray2024rewster} 
% etc.}
% Our perspective is that some manual transport reasoning is 
% inherent to the design of intensional type theory, but that does not rule out
% the possibility of doing a
% much better job than existing proof assistants.

Finally, we give a taste of a more practical application. 
Many useful models of type theory are generated
by interpreting types as instances of some algebraic structure. 
For example, the groupoid \cite{hofmann1998groupoid} and
presheaf \cite{altenkirch1995categorical, altenkirch2017normalisation} models 
of type theory interpret types as groupoids and 
presheaves respectively. 
Actually, to account for type dependency, we
interpret contexts as groupoids/presheaves and types as (fibrant) displayed 
groupoids/displayed presheaves.
% I don't think this footnote adds much
% \footnote{Fibrant displayed groupoids over 
% |⟦Γ⟧| are equivalent to functors from |⟦Γ⟧| to |Grpd| and displayed
% presheaves over |⟦Γ⟧| are equivalent to presheaves on the category of
% elements of |⟦Γ⟧|, |∫ ⟦Γ⟧| \cite{neumann2025generalized}. 
% Note that existing mechanisations of the groupoid model
% in type theory in Rocq and Lean \cite{sozeau2014towards, hua2025hottlean}
% do not take this displayed approach, perhaps in part because of the 
% ``transport-hell'' problem explained here.} 

When trying to mechanise these constructions in a proof assistant,
this dependency causes a ``transport-hell'' problem: the groupoid/functor laws
only hold propositionally, and so we must insert transports in the 
interpretation of types\footnote{``Transport-hell'' can also arise from 
type theory's own substitution calculus, but \emph{strictification} via global
rewrite rules or Kaposi and Pujet's construction \cite{kaposi2025type}
can mostly resolve this.}. When defining
the interpretation of terms, these transports need to manually shifted around,
adding significant clutter to the proofs \cite{burke2026tt}.
With \swith/\srewrite, we could instead reflect these equations in each case
and allow the transports to reduce away, 
getting us much closer to the clarity of
informal presentations.
% bridging the gap between mechanised
% and less formal presentations.

\vspace{-2.0ex}
\paragraph{Theory}

We propose a target type theory for a language featuring \swith by way of
introducing a new contextual judgement for convertibility 
assumptions, following \cite{altenkirch2011case}. We denote a context |Γ|
extended by an equation between terms |t₁|, |t₂| with |Γ ▷ t₁ ~ t₂|.

Similar judgemental-equality-extending constructs 
have been explored as an alternative to
judgemental computation rules \cite{sjoberg2015programming},
in the setting of
dependent Haskell \cite{weirich2017specification, liu2023dependently} and more
generally (by the name cofibrations) 
in cubical type theory \cite{cohen2015cubical, angiuli2021syntax} and
synthetic ∞-category theory \cite{riehl2017synthetic},
as well as to control unfolding \cite{gratzer2025controlling} and to implement 
record patching \cite{zhang2023three}.

We bind convertibility assumptions with a form of 
\emph{local equality reflection}: given a 
propositional identity |p : t₁ = t₂| we bind
both |t₁ ~ t₂| and |p ~ refl| in the body. 
To retain good metatheoretical properties (subject reduction, decidable
typechecking etc.) we make reflection \emph{second-class}, only available at the 
top-level.
This is in keeping with Agda's generative pattern matching and
gives us the freedom to syntactically restrict 
equations (e.g. disallowing overlap), 
without endangering stability under substitution.

The theory for Boolean equations was explored in earlier work
\cite{burke2025local}.
Since then, we have worked to clarify and extend the normalisation argument.
The algorithm is comprised of two components: first, 
we generate term rewriting systems (TRSs) from the
convertibility assumptions in the 
telescope of every top-level definition. This step is inherently
very
syntactic (\swith validity is not stable under conversion).
Once we have the TRS, we can extend normalisation by
evaluation (NbE) by rewriting β-neutral terms during unquote/reflect
(conditional on neutral/normal form comparisons). 
Staying \emph{algebraic} (working with type theory as a
quotient inductive-inductive type) in the NbE component 
appears feasible, but requires care to avoid circularity. E.g. 
we cannot depend on injectivity of type formers during normalisation. 

We are also investigating whether stabilised
neutrals \cite{sterling2021normalization} can help to further abstract
the proof (moving from presheaves on thinnings to presheaves on arbitrary 
renamings).
Additionally, equations at more complicated types than Booleans
pose some further difficulties. For example, the natural number equation
|n ~ su (f n)| must be oriented towards |su (f n)| to unblock 
β-reductions, but loops if we apply it naively.

Finally, we touch on conservativity/consistency. 
Local equality reflection is implied by
judgemental equality reflection so a translation into ETT is immediate, but we 
would ideally have a translation into ITT that does not rely on 
function extensionality
(we only allow reflecting individual equations, not families of equations) or 
UIP (for consistency with HoTT).

Unfortunately, naive \swith certainly does
imply UIP. The situation somewhat resembles that of dependent pattern matching
\cite{coquand1992pattern, goguen2006eliminating, barras2008new},
where it is possible to avoid UIP by restricting 
the unification algorithm \cite{cockx2016eliminating}, so we are hopeful
a similar criterion on reflected equations could be employed (e.g. disallowing
reflexive equations).

\begingroup
\sloppy
\printbibliography
\endgroup

\end{document}

