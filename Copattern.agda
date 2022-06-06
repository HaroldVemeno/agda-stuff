{-# OPTIONS --copattern --safe --no-sized-types --guardedness #-}
module Copattern where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream public

-- | Bisimulation as equality
record _==_ {A : Set} (x : Stream A) (y : Stream A) : Set where
  coinductive
  field
    refl-head : head x ≡ head y
    refl-tail : tail x == tail y
open _==_ public

ex : Stream ℕ
head ex = 2
head (tail ex) = 5
head (tail (tail ex)) = 8
head (tail (tail (tail ex))) = 12
head (tail (tail (tail (tail ex)))) = 155
tail (tail (tail (tail (tail ex)))) = ex

-- Getting started:
module Introduction where

  -- Infinite sequence of `ones`.
  ones : Stream ℕ
  head ones = suc zero
  tail ones = ones

  -- Infinite sequence of give number
  repeat : {A : Set} -> A -> Stream A
  head (repeat x) = x
  tail (repeat x) = repeat x

  -- Odd and Even, as you've implemented in:
  -- https://www.codewars.com/kata/tear-me-apart-and-merge-the-pieces-together
  even : ∀ {A} -> Stream A -> Stream A
  head (even a) = head a
  tail (even a) = even (tail (tail a))

  odd : ∀ {A} -> Stream A -> Stream A
  head (odd a) = head (tail a)
  tail (odd a) = odd (tail (tail a))

module Bisimulation where
  open Introduction

  -- Refl for bisimulation
  refl′ : ∀ {A} -> (a : Stream A) -> a == a
  refl-head (refl′ a₁) = refl
  refl-tail (refl′ a₁) = refl′ (tail a₁)

  oddEven : ∀ {A} -> (a : Stream A) -> odd a == even (tail a)
  refl-head (oddEven a) = refl
  refl-tail (oddEven a) = oddEven (tail (tail a))

module Merge where
  open Bisimulation
  open Introduction

  merge : ∀ {A} -> Stream A -> Stream A -> Stream A
  head (merge a _) = head a
  head (tail (merge _ b)) = head b
  tail (tail (merge a b)) = merge (tail a) (tail b)

  -- Merge! Even! Odd!
  moe : ∀ {A} -> (a : Stream A) -> (merge (even a) (odd a) == a)
  refl-head (moe a) = refl
  refl-head (refl-tail (moe a)) = refl
  refl-tail (refl-tail (moe a)) = moe (tail (tail a))
