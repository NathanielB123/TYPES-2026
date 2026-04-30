{-# OPTIONS --cubical --guardedness --smart-with #-}

import Agda.Builtin.Equality.Rewrite

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum
  renaming (rec to ⊎-rec; elim to ⊎-elim; map to ⊎-map)
open import Cubical.Data.Unit.Base renaming (Unit to ⊤)
open import Cubical.Data.Empty renaming (rec to absurd) hiding (elim)
open import Cubical.Relation.Nullary

-- https://agda.zulipchat.com/#narrow/channel/260790-cubical/topic/.E2.9C.94.20Splitting.20an.20interval.20in.20Agda.20Cubical/with/527580783
module InTheWild.C where

_≢_ : ∀ {ℓ} {A : Type ℓ} → (x y : A) → Type ℓ
x ≢ y = x ≡ y → ⊥

inl≢inr : {A B : Type} → (a : A) → (b : B) → inl a ≢ inr b
inl≢inr {A} {B} a b p = transport (cong P p) tt
  where
    P : A ⊎ B → Type
    P (inl _) = ⊤
    P (inr _) = ⊥

inl-injective : {A B : Type} (x y : A) → _≡_ {A = A ⊎ B} (inl x) (inl y) → x ≡ y
inl-injective {A} {B} x y p i with p i
... | inl a = a
... | inr b = absurd (inl≢inr x b λ j → p (i ∧ j))
