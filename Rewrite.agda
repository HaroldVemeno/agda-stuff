{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality
open import Data.Nat

b : (a : ℕ) -> a + 0 ≡ a
b zero = refl
b (suc a₁) = cong suc (b a₁)

c : (n m : ℕ) -> n + (suc m) ≡ suc (n + m)
c zero m = refl
c (suc a₁) m = cong suc (c a₁ m)

{-# REWRITE b c #-}

p : (n m : ℕ) -> suc n + 0 + suc m ≡ suc (suc (n + m))
p _ _ = refl
