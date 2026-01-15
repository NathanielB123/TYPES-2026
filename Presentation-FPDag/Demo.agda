{-# OPTIONS --rewriting --local-confluence-check --exact-split #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Bool renaming (true to tt; false to ff)

module Presentation-FPDag.Demo where

module _ where
  infix 4 _≡[_]≡_

  private variable
    ℓ   : Level
    A B : Set _
    x y z : A

  sym : x ≡ y → y ≡ x
  sym refl = refl

  _∙_ : x ≡ y → y ≡ z → x ≡ z
  refl ∙ q = q

  transp : (P : A → Set ℓ) → x ≡ y → P x → P y
  transp P refl d = d

  ap : (f : A → B) → x ≡ y → f x ≡ f y
  ap f refl = refl

  _≡[_]≡_ : A → A ≡ B → B → Set _
  x ≡[ refl ]≡ y = x ≡ y

  data Singleton {a} {A : Set a} (x : A) : Set a where
    _with≡_ : (y : A) → x ≡ y → Singleton x

  inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
  inspect x = x with≡ refl

  data ⊥ : Set where

  ⊥-elim : ⊥ → A
  ⊥-elim ()















not : Bool → Bool
not tt = ff
not ff = tt





-- Example 1

not-not : (b : Bool) → not (not b) ≡ b
not-not b = {!!}























-- Example 2

f3 : (f : Bool → Bool) → f (f (f tt)) ≡ f tt
f3 f = {!!}




























-- Example 3

data Parity : Set where
  odd  : Parity
  even : Parity

variable
  p q : Parity

inv : Parity → Parity
inv odd  = even
inv even = odd

_xor_ : Parity → Parity → Parity
even xor q = q
odd  xor q = inv q


inv-inv : inv (inv p) ≡ p
inv-inv {p = even} = refl
inv-inv {p = odd}  = refl

inv-xor : inv p xor q ≡ inv (p xor q)
inv-xor {p = even} = refl
inv-xor {p = odd}  = sym inv-inv

xor-even : p xor even ≡ p
xor-even {p = even} = refl
xor-even {p = odd}  = refl


data Nat : Parity → Set where
  ze : Nat even
  su : Nat (inv p) → Nat p

variable
  n m : Nat p 

_+_ : Nat p → Nat q → Nat (p xor q)
n + m = {!!}
+ze : n + ze ≡[ ap Nat xor-even ]≡ n
+ze = {!!}



































{-
ze + m = m
_+_ {p} {q} (su n) m with n + m
... | n+m rewrite inv-xor {p} {q} = su n+m

+ze {n = ze} = refl
+ze {n = su {p = p} n} with n + ze in eq
... | n′ rewrite inv-xor {p} {even} = {!   !}
-}

