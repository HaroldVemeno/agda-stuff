{-# OPTIONS --safe #-}
module OddsAndEvens where

open import Data.Nat
open import Data.Nat.Properties


data Even : ℕ → Set
data Odd  : ℕ → Set

data Even where
  zero : Even zero
  suc  : ∀ {n : ℕ} → Odd n → Even (suc n)

data Odd where
  suc : ∀ {n : ℕ} → Even n → Odd (suc n)


-- | Implement all these functions
infixl 6 _e+e_ _o+e_ _o+o_ _e+o_
_e+e_ : ∀ {m n : ℕ} → Even m → Even n → Even (m + n)
_o+e_ : ∀ {m n : ℕ} → Odd  m → Even n → Odd  (m + n)
_o+o_ : ∀ {m n : ℕ} → Odd  m → Odd  n → Even (m + n)
_e+o_ : ∀ {m n : ℕ} → Even m → Odd  n → Odd  (m + n)

zero e+e e = e
suc o e+e e = suc (o o+e e)

suc e o+e ee = suc (e e+e ee)

suc e o+o o = suc (e e+o o)

zero e+o o = o
suc o e+o oo = suc (o o+o oo)
