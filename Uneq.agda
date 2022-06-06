module Uneq where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Empty

data One : Set where
  a : One

∃-type-ne : ∃ λ (A : Set) → ∃ λ B → A ≢ B
proj₁ ∃-type-ne = ⊥
proj₁ (proj₂ ∃-type-ne) = One
proj₂ (proj₂ ∃-type-ne) x with b <- a rewrite sym x = b
