{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Everything
open import Data.Maybe
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

module Isaac where
isaac : ∀ {n} → Maybe (Fin n) ≡ Fin (suc n)
isaac {n} = isoToPath (iso f g p q)
  where
  f : Maybe (Fin n) → Fin (suc n)
  f (just (m , m<n)) = (suc m , suc-≤-suc m<n)
  f nothing = (zero , n , (+-comm n 1))
  g : Fin (suc n) → Maybe (Fin n)
  g (zero , _) = nothing
  g (suc m , sm<sn) = just (m , (pred-≤-pred sm<sn))
  p : section f g
  p (zero , a , b) = {!!}
  p (suc n , n<m) = {!!}
  q : retract f g
  q a = {!!}

-- maybe helpful

-- prove it!

open Iso

maybeInjective : {A B : Set} → Maybe A ≡ Maybe B → A ≡ B
maybeInjective {A} {B} x = isoToPath (iso f g p q)
  where
  is : Iso (Maybe A) (Maybe B)
  is = pathToIso x
  f : A → B
  f a with is .fun (just a) | inspect (is .fun) (just a)
  ... | just b | _ = b
  ... | nothing | [ E1 ] = {!!}

  g : B → A
  g = {!!}
  p : section f g
  p = {!!}
  q : retract f g
  q = {!!}
