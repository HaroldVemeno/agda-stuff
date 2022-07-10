{-# OPTIONS --cubical --safe #-}
open import Cubical.Foundations.Everything
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Data.Unit
module NnotUnit where

fact : isContr Unit
fst fact = tt
snd fact tt = refl
fact2 : ¬ isContr ℕ
fact2 (n , e) = non (e (suc n))
  where
    non :  ¬ n ≡ suc n  
    non p = {!!}
oh : ¬ (ℕ ≡ Unit)
oh p = fact2 (transport (λ i -> isContr (p (~ i))) fact)
