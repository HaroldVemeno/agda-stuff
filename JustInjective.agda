{-# OPTIONS --cubical --safe #-}
module JustInjective where

open import Cubical.Core.Everything renaming (_≡_ to _==_)
open import Cubical.Data.Unit
open import Cubical.Foundations.Everything

data maybe (A : Set) : Set where
  just : A -> maybe A
  nothing : maybe A


from-maybe : {A : Set} (a : A) -> maybe A -> A
from-maybe a (just x) = x
from-maybe a nothing = a


just-injective : ∀ {A : Set} (a b : A) → just a == just b → a == b
just-injective a b p i = from-maybe a (p i)
