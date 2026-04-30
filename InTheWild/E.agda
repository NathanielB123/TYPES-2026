{-# OPTIONS --smart-with #-}

import Agda.Builtin.Equality.Rewrite

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Tactic.RingSolver
open import Data.List
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- https://agda.zulipchat.com/#narrow/channel/259644-newcomers/topic/Ring.20solver.20on.20compound.20subexprs.20avoiding.20.60with.60.20abstraction/with/463212052
-- This example is admittedly very brittle. The ring solver dies if we replace 
-- 'u' with 'f x' in the steps, but it does *work*
module InTheWild.E where

g : ℕ → ℕ → ℕ
g x y = {!   !}

opaque
  f : ℕ → ℕ
  f x = {!!}

lem : ∀ x y → f x ≡ g x y
lem = {!   !}

identity : ∀ x y → f x + 0 ≡ g x y
identity x y with u ← f x = begin
  u + 0 ≡⟨ solve (u ∷ []) ⟩
  u     ≡⟨ lem x y ⟩
  g x y ∎