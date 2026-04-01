open import Agda.Builtin.Equality
open import Agda.Builtin.List renaming (_∷_ to _,-_)
open import Agda.Builtin.Bool renaming (true to tt; false to ff)

-- Examples from the abstract, self-contained
module Examples where

module Utils where
  variable
    A B C : Set _
    x y z : A
    f g h : A → B
    xs ys : List _

  infix 4 _≡[_]≡_

  sym : x ≡ y → y ≡ x
  sym refl = refl

  _∙_ : x ≡ y → y ≡ z → x ≡ z
  refl ∙ q = q

  ap : (f : A → B) → x ≡ y → f x ≡ f y
  ap f refl = refl

  _≡[_]≡_ : A → A ≡ B → B → Set _
  x ≡[ refl ]≡ y = x ≡ y
open Utils

-- Filter example

filter : (A → Bool) → List A → List A
filter f []           = []
filter f (x ,- xs) with f x
... | tt = x ,- filter f xs
... | ff = filter f xs

filter-twice : filter f (filter f xs) ≡ filter f xs
filter-twice         {xs = []}         = refl
filter-twice {f = f} {xs = x ,- xs} with f x in eq
... | ff = filter-twice {xs = xs}
... | tt with f x | eq
... | tt | eq = ap (x ,-_) (filter-twice {xs = xs})
... | ff | ()

-- With "smart with" we can instead implement |filter-twice| as follows:
{-
filter-twice : filter f (filter f xs) ≡ filter f xs
filter-twice         {xs = []}         = refl
filter-twice {f = f} {xs = x ,- xs} with f x
... | ff = filter-twice {xs = xs}
... | tt = ap (x ,-_) (filter-twice {xs = xs})
-}

-- Parity example

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
ze + m = m
_+_ {p} {q} (su n) m
  with    n+m ← n + m
  rewrite inv-xor {p} {q}
  = su n+m

+ze : n + ze ≡[ ap Nat xor-even ]≡ n
+ze {n = ze}   = refl
+ze {n = su {p} n} 
  with    n′ ← n + ze -- in eq
                      -- ^ Uncommenting this hits an "ill-typed 
                      --   with-abstraction" error.
  rewrite inv-xor {p} {even}
  = {!!} -- We are stuck!

-- With "smart with" we can instead implement |_+_| and |+ze| as follows
{-
_+_ : Nat p → Nat q → Nat (p xor q)
ze + m                  = m
_+_ {p} {q} (su n) m with inv p xor q | inv-xor {p} {q}
... | _ | refl = su (n + m)

+ze : n + ze ≡[ ap Nat xor-even ]≡ n
+ze {n = ze}          = refl
+ze {n = su {p} n} with inv p xor even | inv-xor {p} {even}
                      | p xor even | xor-even {p}
                      | xor-even {inv p}
... | _ | refl | _ | refl | refl = ap su (+ze {n = n})
-}

-- With "smart rewrite" sugar, we can simply write
{-
_+_ : Nat p → Nat q → Nat (p xor q)
ze + m = m
_+_ {p} {q} (su n) m 
  rewrite inv-xor {p} {q}
  = su (n + m)

+ze : n + ze ≡[ ap Nat xor-even ]≡ n
+ze {n = ze} = refl
+ze {n = su {p} n} 
  rewrite inv-xor {p} {even}
  rewrite xor-even {p}
  rewrite xor-even {inv p}
  = ap su (+ze {n = n})
-}

-- Note the final |with|-abstraction/|rewrite| should probably be rejected by
-- |--smart-with|, |--without-K|.
-- We should instead reflect the below higher equation.
xor-even-inv : xor-even {inv p} ≡ inv-xor {p} {even} ∙ ap inv (xor-even {p})
xor-even-inv {p = odd}  = refl
xor-even-inv {p = even} = refl
