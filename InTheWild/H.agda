{-# OPTIONS --smart-with #-}

import Agda.Builtin.Equality.Rewrite

open import Data.Nat
open import Data.List
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality

-- https://agda.zulipchat.com/#narrow/channel/238741-general/topic/How.20to.20help.20Agda.20recognise.20the.20rewrite.20expression.3F/with/418437010
module InTheWild.H where

data Term : Set where
  num : ℕ → Term
  add : Term → Term → Term

-- think it as building a big add Term from a list
_+s_ : Term → List Term → Term
_+s_ n [] = n
_+s_ n (n' ∷ ns) = (add n n') +s ns

-- rewrite a non-empty list into a appending form
lst-destruct-rev : ∀ (l : List Term)
  → 0 < length l
  → ∃[ x ] (∃[ xs ] (xs ++ x ∷ [] ≡ l))
lst-destruct-rev (x ∷ []) (s≤s z≤n) = ⟨ x , ⟨ [] , refl ⟩ ⟩
lst-destruct-rev (x ∷ y ∷ l) (s≤s z≤n) with lst-destruct-rev (y ∷ l) (s≤s z≤n)
... | ⟨ x' , ⟨ xs' , eq ⟩ ⟩ rewrite eq = ⟨ x' , ⟨ x ∷ xs' , refl ⟩ ⟩

data Property : Term → Set where
  anything : ∀ {t} → Property t

lemma : ∀ e es → Property (e +s es)
lemma e [] = anything
lemma e es@(e' ∷ es') with lst-destruct-rev es (s≤s z≤n)
... | ⟨ x' , ⟨ xs' , eq ⟩ ⟩ rewrite eq = h
  where
    postulate h : Property (e +s (xs' ++ x' ∷ []))
