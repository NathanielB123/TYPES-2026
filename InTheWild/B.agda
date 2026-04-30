{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Equality.Rewrite

-- https://agda.zulipchat.com/#narrow/channel/238741-general/topic/.E2.9C.94.20With-abstraction.20question/with/567123765
module InTheWild.B where

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

Σ-syntax : ∀ (A : Set) (F : A → Set) → Set
Σ-syntax X F = Σ X F

syntax Σ-syntax X (λ x → F) = Σ[ x ∈ X ] F
infix 4 Σ-syntax

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

data Maybe (T : Set) : Set where
  just : T → Maybe T
  nothing : Maybe T

is-just : ∀ { T } → Maybe T → Set
is-just (just x) = ⊤
is-just nothing = ⊥

postulate
  T : Set
  f : T → Maybe T

ι : T → Maybe (Σ[ l ∈ T ] is-just (f l))
ι l with f l
... | nothing = nothing
... | just _ = just (l , tt)
