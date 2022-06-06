{-# OPTIONS --cubical #-}
module Homo where

open import Cubical.Foundations.Everything
open import Data.Nat
open import Data.List
open import Function

data Test : Type where
  point : Test
  pointo : Test
  pointy : Test -> Test
  pathy : point ≡ pointo

open Iso

tton : Test -> ℕ
tton point = zero
tton pointo = zero
tton (pointy x) = suc (tton x)
tton (pathy i) = zero

ntot : ℕ -> Test
ntot zero = point
ntot (suc x) = pointy (ntot x)

ri : section tton ntot
ri zero = refl
ri (suc zero) = refl
ri (suc (suc b)) = cong suc (ri (suc b))

li : retract tton ntot
li point = refl
li pointo = pathy
li (pointy a) = cong pointy (li a)
li (pathy i) j = pathy (i ∧ j)

hmm : Iso Test ℕ
fun hmm = tton
inv hmm = ntot
rightInv hmm = ri
leftInv hmm = li

thepath : Test ≡ ℕ
thepath = isoToPath hmm

t : Test
t = transport (sym thepath) 6

tu : List ℕ
tu = 2 ∷ 4 ∷ 2 ∷ 9 ∷ 5 ∷ 10 ∷ []

ttu : List Test
ttu = subst List (sym thepath) tu

_+'_ : Test -> Test -> Test
_+'_ = subst (λ a -> a -> a -> a) (sym thepath) _+_



iu = transport thepath $ foldl _+'_ pointo ttu

data Old : Type where
  point : Old
  pointy : Old -> Old
  pathy : point ≡ pointy point


ωpathy : (p : Old) -> p ≡ pointy p
ωpathy point = pathy
ωpathy (pointy p) = cong pointy (ωpathy p)
ωpathy (pathy i) j = PathP (λ i -> pathy i ≡ cong pointy (pathy i)) pathy (cong pointy pathy) i j

Ωpathy : (p : Old) -> point ≡ p
Ωpathy point = refl
Ωpathy (pointy p) = pathy ∙ cong pointy (Ωpathy p)
Ωpathy (pathy i) j = {!cong ()!}

Old-Contr : isContr Old
fst Old-Contr = point
snd Old-Contr = {!!}
