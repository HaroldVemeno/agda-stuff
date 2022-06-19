-- {-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Empty

-- this one is provable, we're just making use of it below
coerce : {A B : Set} → A ≡ B → A → B
coerce refl a = a



J : {A : Set} (P : (x y : A) → x ≡ y → Set) →
    ((x : A) → P x x refl) → (x y : A) (x≡y : x ≡ y) → P x y x≡y
J P p x .x refl = p x


K : {A : Set} {x : A} (P : x ≡ x → Set) →
    P refl → (x≡x : x ≡ x) → P x≡x
K P p refl = p

J' : {A : Set} (x : A) (P : (y : A) → x ≡ y → Set) →
   P x refl → (y : A) (x≡y : x ≡ y) → P y x≡y
J' x P p x refl = p

