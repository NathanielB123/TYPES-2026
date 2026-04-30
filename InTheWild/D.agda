{-# OPTIONS --smart-with #-}

import Agda.Builtin.Equality.Rewrite

open import Level
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)
open import Relation.Binary.Construct.Closure.Equivalence using (gmap; isEquivalence; EqClosure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Product using (uncurry′)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal

-- https://agda.zulipchat.com/#narrow/channel/263194-categories/topic/Can.27t.20aid.20Agda.20in.20unifying.20two.20propositionally-equal.20types/with/472982116
module InTheWild.D where

data Hom : ℕ → ℕ → Set

variable
  i o m    : ℕ
  i₁ i₂ i₃ : ℕ
  o₁ o₂ o₃ : ℕ
  m₁ m₂ m₃ : ℕ

  n : Hom i o
  a b c k : Hom i o

instance
  i≡i+0 : i ≡ i + 0
  i≡i+0 = sym (+-identityʳ _)
  

infixl 8 _⨾_
infixl 9 _⊗_
data Hom where
  id : Hom i i
  _⊗_ : {{i ≡ i₁ + i₂}} → {{o ≡ o₁ + o₂}}
    → Hom i₁ o₁
    → Hom i₂ o₂
    ------------
    → Hom i o
  _⨾_ :
      Hom i m
    → Hom   m o
    → Hom i   o

pattern id₀ = id {0}
{-# DISPLAY id {0} = id₀ #-}

infixl 1 _~′_ 
-- Small-step syntactical equivalence
data _~′_ : Rel (Hom i o) 0ℓ where
  ⨾-id : n ⨾ id ~′ n
  id-⨾ : id ⨾ n ~′ n
  ⨾-assoc : a ⨾ b ⨾ c ~′ a ⨾ (b ⨾ c)
  
  ⊗-assoc :
      {{i≡ : i ≡ i₁ + i₂ + i₃}}
    → {{o≡ : o ≡ o₁ + o₂ + o₃}}
    → {a : Hom i₁ o₁}
    → {b : Hom i₂ o₂}
    → {c : Hom i₃ o₃}
    → a ⊗ b ⊗ c ~′ _⊗_ {{trans i≡ (+-assoc i₁ _ _)}} {{trans o≡ (+-assoc o₁ _ _)}} a (b ⊗ c)
  ⊗-empty : n ⊗ id₀ ~′ n
  empty-⊗ : id₀ ⊗ n ~′ n

  distr :
      {{i≡ : i ≡ i₁ + i₂}}
    → {{o≡ : o ≡ o₁ + o₂}}
    → {{m≡ : m ≡ m₁ + m₂}}
    → {a₁ : Hom i₁ m₁}
    → {a₂ : Hom i₂ m₂}
    → {b₁ : Hom m₁ o₁}
    → {b₂ : Hom m₂ o₂}
    → (_⊗_ {{i≡}} {{m≡}} a₁ a₂) ⨾ (_⊗_ {{m≡}} {{o≡}} b₁ b₂) ~′ (a₁ ⨾ b₁) ⊗ (a₂ ⨾ b₂)

  id⊗id : ∀ {a b : ℕ} → id {a} ⊗ id {b} ~′ id {a + b}

  -- structural transitivity
  ⊗₁ : a ~′ b → a ⊗ k ~′ b ⊗ k
  ⊗₂ : a ~′ b → k ⊗ a ~′ k ⊗ b
  ⨾₁ : a ~′ b → a ⨾ k ~′ b ⨾ k
  ⨾₂ : a ~′ b → k ⨾ a ~′ k ⨾ b

infix  3 _~_
-- Syntactical equivalence
_~_ : Rel (Hom i o) 0ℓ
_~_ = EqClosure _~′_

Hom-Cat : Category 0ℓ 0ℓ 0ℓ
Hom-Cat = record
  { Obj = ℕ
  ; _⇒_ = Hom
  ; _≈_ = _~_
  ; id = id
  ; _∘_ = λ a b → b ⨾ a
  ; assoc = (bwd ⨾-assoc) ◅ ε
  ; sym-assoc = (fwd ⨾-assoc) ◅ ε
  ; identityˡ = fwd ⨾-id ◅ ε
  ; identityʳ = fwd id-⨾ ◅ ε
  ; identity² = fwd ⨾-id ◅ ε
  ; equiv = isEquivalence _
  ; ∘-resp-≈ = λ a b → ⨾₁* b ◅◅ ⨾₂* a
  }
  where
  ⨾₁* : a ~ b → a ⨾ k ~ b ⨾ k
  ⨾₁* {k = k} = gmap (_⨾ k) ⨾₁

  ⨾₂* : a ~ b → k ⨾ a ~ k ⨾ b
  ⨾₂* {k = k} = gmap (k ⨾_) ⨾₂

Hom-Monoidal : Monoidal Hom-Cat
Hom-Monoidal = monoidalHelper Hom-Cat (record
  { ⊗ = ⊗-Cat
  ; unit = 0
  ; unitorˡ = unitorˡ
  ; unitorʳ = unitorʳ
  ; associator = {!!}
  ; unitorˡ-commute = unitorˡ-commute
  ; unitorʳ-commute = unitorʳ-commute
  ; assoc-commute = {!!}
  ; triangle = {!!}
  ; pentagon = {!!}
  })
  where
    open import Categories.Functor.Bifunctor using (Bifunctor)
    open import Categories.Morphism Hom-Cat using (_≅_)

    ⊗-Cat : Bifunctor Hom-Cat Hom-Cat Hom-Cat
    ⊗-Cat = record
      { F₀ = uncurry′ _+_
      ; F₁ = uncurry′ _⊗_
      ; identity = fwd id⊗id ◅ ε
      ; homomorphism = (bwd distr) ◅ ε
      ; F-resp-≈ = uncurry′ λ a b → ⊗₁* a ◅◅ ⊗₂* b 
      }
      where
        ⊗₁* : a ~ b → a ⊗ k ~ b ⊗ k
        ⊗₁* {k = k} = gmap (_⊗ k) ⊗₁

        ⊗₂* : a ~ b → k ⊗ a ~ k ⊗ b
        ⊗₂* {k = k} = gmap (k ⊗_) ⊗₂

    open Bifunctor ⊗-Cat

    unitorˡ : ∀ {X} → 0 + X ≅ X
    unitorˡ {X} = record
      { from = id₀ ⊗ X′
      ; to = X′ ⊗ id₀
      ; iso = record
        { isoˡ = fwd (⨾₁ id⊗id) ◅ fwd (⨾₂ ⊗-empty) ◅ fwd id-⨾ ◅ ε
        ; isoʳ = fwd (⨾₁ ⊗-empty) ◅ fwd id-⨾ ◅ fwd id⊗id ◅ ε }
      }
      where X′ = id {X}

    unitorʳ : ∀ {X} → X + 0 ≅ X
    unitorʳ {X}
      -- rewriting needed because X+0 doesn't simplify as nicely as 0+X above
      rewrite +-identityʳ X
      =
        record
          { from = X′ ⊗ id₀
          ; to = id₀ ⊗ X′
          ; iso = record
            { isoˡ = fwd (⨾₁ ⊗-empty) ◅ fwd id-⨾ ◅ fwd id⊗id ◅ ε
            ; isoʳ = fwd (⨾₁ id⊗id) ◅ fwd (⨾₂ ⊗-empty) ◅ fwd id-⨾ ◅ ε }
          }
      where
        X′ = id {X}

    -- Agda expects this type signature:
  --unitorˡ-commute : ∀ {f : Hom i o} → (id₀ ⊗ f) ⨾ unitorˡ.from   ~ unitorˡ.from   ⨾ f
    -- But it reduces to this simpler type signature:
    unitorˡ-commute : ∀ {f : Hom i o} → (id₀ ⊗ f) ⨾ (id₀ ⊗ id {o}) ~ (id₀ ⊗ id {i}) ⨾ f
    unitorˡ-commute =
        fwd (⨾₁ empty-⊗)
      ◅ fwd (⨾₂ empty-⊗)
      ◅ fwd ⨾-id
      ◅ bwd id-⨾
      ◅ bwd (⨾₁ empty-⊗)
      ◅ ε

    -- Agda expects this type signature:
    unitorʳ-commute : ∀ {f : Hom i o} → f ⊗ id₀ ⨾ _≅_.from (unitorʳ {o}) ~ _≅_.from (unitorʳ {i}) ⨾ f
    -- Whereas I wanted this type signature:
  --unitorʳ-commute : ∀ {f : Hom i o} → f ⊗ id₀ ⨾ (id {o} ⊗ id₀) ~ (id {i} ⊗ id₀) ⨾ f
    unitorʳ-commute {i} {o} {f} 
        rewrite +-identityʳ i
        rewrite +-identityʳ o
        = unitorʳ-commute′
      -- I tried:
      --  - rewrite (+-identityʳ i) ==> reports an error about (lhs != i + 0 of type ℕ), ill-typed with abstraction
      --  - with (+-identityʳ i)    ==> doesn't allow me to pattern match the equality
      --  - subst (+-identityʳ i) in body ==> doesn't change anything
      --  - writing the record with copattern and using one of
      --    the above directly instead of having a separate definition ==> same problems as above
      --  - case_of_ and case_returning_of_
      --  - proving a separate lemma : _≅_.from (unitorʳ {x}) ≡ id {x} ⊗ id₀
      where
      -- here's what the proof should be
      unitorʳ-commute′ : ∀ {f : Hom i o} → (f ⊗ id₀) ⨾ (id {o} ⊗ id₀) ~ (id {i} ⊗ id₀) ⨾ f
      unitorʳ-commute′ {i} =
          fwd (⨾₁ ⊗-empty)
        ◅ fwd (⨾₂ ⊗-empty)
        ◅ fwd ⨾-id
        ◅ bwd id-⨾
        ◅ bwd (⨾₁ ⊗-empty)
        ◅ ε
    