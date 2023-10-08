{-# OPTIONS --safe #-}

open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary

infix 7 _∣_
infix 7 _∤_

data _∣_ : ℕ -> ℕ -> Set where
  _by_ : {d n : ℕ} -> (m : ℕ) -> d * m ≡ n -> d ∣ n

_∤_ : ℕ -> ℕ -> Set
n ∤ m = ¬ (n ∣ m)

2∣8 : 2 ∣ 8
2∣8 = 4 by refl

too-big : {n d : ℕ} -> n < d -> n ≢ 0 -> d ∤ n
too-big {.(d * 0)} {d} p n≢0 (0 by refl) = n≢0 (*-comm d 0)
too-big {.(d * 1)} {d} p n≢0 (1 by refl)
  = <-irrefl (refl {_} {_} {d}) {!!}
too-big {.(d * suc (suc m))} {d} p n≢0 (suc (suc m) by refl) = {!!}

record is-prime (n : ℕ) : Set where
  field
    size : 2 ≤ n
    primality : (d : ℕ) -> d ∣ n -> (d ≡ 1) ⊎ (d ≡ n)

open is-prime



p2 : is-prime 2
size p2 = ≤-refl
primality p2 zero (m by ())
primality p2 (suc zero) x = inj₁ refl
primality p2 (suc (suc zero)) x = inj₂ refl
primality p2 (suc (suc (suc d))) (m by x) = {!!}


data ℚ : Set where
