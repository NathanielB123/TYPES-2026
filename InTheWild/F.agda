{-# OPTIONS --smart-with #-}

import Agda.Builtin.Equality.Rewrite

open import Agda.Builtin.Equality
open import Data.Maybe
open import Data.Nat

-- https://agda.zulipchat.com/#narrow/channel/259644-newcomers/topic/Pattern.20matching.20and.20proof.20of.20equality/with/448292624
-- Admittedly, the use-case for "smart with" is a bit more tenuous here: the
-- inspect idiom is also sufficient.
module InTheWild.F where

f? : (n : ℕ) → Maybe ℕ
f? 0 = just 0
f? 3 = just 2
f? 6 = just 0
f? _ = nothing

g? : (n : ℕ) → Maybe ℕ
g? 3 = just 2
g? (suc n) with f? n
... | just n' = just (suc n')
... | nothing = nothing
g? _ = nothing

f?-≤ : ∀ n {n'} → f? n ≡ just n' → n' ≤ n
f?-≤ 0 refl = z≤n
f?-≤ 3 refl = s≤s (s≤s z≤n)
f?-≤ 6 refl = z≤n

g?-≤ : ∀ n {n'} → g? n ≡ just n' → n' ≤ n
g?-≤ 1 refl = s≤s z≤n
g?-≤ 3 refl = s≤s (s≤s z≤n)
g?-≤ (suc (suc (suc (suc n'')))) g?n≡n' with f? (suc (suc (suc n'')))
g?-≤ _ () | nothing
... | just n''' with f?-≤ (suc (suc (suc n''))) {n'''} refl
... | hyp' with refl ← g?n≡n' = s≤s hyp'
