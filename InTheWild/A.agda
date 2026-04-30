{-# OPTIONS --smart-with #-}

import Agda.Builtin.Equality.Rewrite

open import Data.Sum using (_⊎_)
open _⊎_
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ)
import Data.Nat.Properties
open Data.Nat.Properties using (≤-total)
open import Relation.Binary.Reasoning.Preorder Data.Nat.Properties.≤-preorder

-- https://agda.zulipchat.com/#narrow/channel/238741-general/topic/can.27t.20reimplement.20max-assoc.20for.20some.20reason.3F/near/576799689
module InTheWild.A where

max :  ℕ → ℕ →  ℕ
max x y with ≤-total x y
... | inj₁ x≤y = y
... | inj₂ y≤x = x

max-assoc : (a b c : ℕ) → max (max a b) c ≡ max a (max b c)
max-assoc a b c with ≤-total a b | ≤-total b c
max-assoc a b c | lorr₁ | lorr₂ = begin-equality
  max (max a b) c ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ∎

