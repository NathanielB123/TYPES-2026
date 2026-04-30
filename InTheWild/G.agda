{-# OPTIONS --smart-with #-}

import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Bool hiding ( _≤_)
open import Data.Unit
open import Data.Empty

-- https://agda.zulipchat.com/#narrow/channel/238741-general/topic/ill-typed.20with.20abstractions/with/427915992
module InTheWild.G where

data _↓_ (A : Set) (f : A → Bool) : Set where
  filtered : (x : A) → (T (f x)) → A ↓ f

unfiltered : ∀{A}{f : A → Bool} → A ↓ f → A
unfiltered (filtered x _) = x

filter' : ∀{A} (f : A → Bool) → List A → List (A ↓ f)
filter' f [] = []
filter' f (x ∷ xs) with f x
... | false = filter' f xs
... | true = filtered x tt ∷ filter' f xs

lemma : ∀ {A : Set} f (xs : List A) v → unfiltered v ∈ xs → v ∈ filter' f xs
lemma f (x ∷ xs) v p with f x 
lemma f (x ∷ xs) v                (there p)   | true  = there (lemma f xs v p)
lemma f (x ∷ xs) (filtered x prf) (here refl) | true  = here refl
lemma f (x ∷ xs) v                (there p)   | false = lemma f xs v p
lemma f (x ∷ xs) (filtered x prf) (here refl) | false = ⊥-elim prf
