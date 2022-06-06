{-# OPTIONS --cubical --safe #-}
module Transport where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Unit

Thing : ℕ -> Type
Thing 3 = ⊥
Thing _ = Unit

theWrongThing : 1 + 1 ≡ 3 → ⊥
theWrongThing thatMoney = subst Thing thatMoney tt
