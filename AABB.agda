{-# OPTIONS --safe #-}
module AABB where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties

invert : (a b : ℕ) → a + a ≡ b + b → a ≡ b
invert zero zero x = refl
invert (suc a) (suc b) x
  with x <- suc-injective x
  rewrite +-comm a (suc a)
        | +-comm b (suc b)
  with x <- suc-injective x = cong suc (invert a b x)
