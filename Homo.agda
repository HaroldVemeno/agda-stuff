{-# OPTIONS --cubical #-}
module Homo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Data.Nat
open import Data.List
open import Function

-- private
--   data Test : Type where
--     point : Test
--     pointo : Test
--     pointy : Test -> Test
--     pathy : point ≡ pointo

--   open Iso

--   tton : Test -> ℕ
--   tton point = zero
--   tton pointo = zero
--   tton (pointy x) = suc (tton x)
--   tton (pathy i) = zero

--   ntot : ℕ -> Test
--   ntot zero = point
--   ntot (suc x) = pointy (ntot x)

--   ri : section tton ntot
--   ri zero = refl
--   ri (suc zero) = refl
--   ri (suc (suc b)) = cong suc (ri (suc b))

--   li : retract tton ntot
--   li point = refl
--   li pointo = pathy
--   li (pointy a) = cong pointy (li a)
--   li (pathy i) j = pathy (i ∧ j)

--   hmm : Iso Test ℕ
--   fun hmm = tton
--   inv hmm = ntot
--   rightInv hmm = ri
--   leftInv hmm = li

--   thepath : Test ≡ ℕ
--   thepath = isoToPath hmm

--   t : Test
--   t = transport (sym thepath) 6

--   tu : List ℕ
--   tu = 2 ∷ 4 ∷ 2 ∷ 9 ∷ 5 ∷ 10 ∷ []

--   ttu : List Test
--   ttu = subst List (sym thepath) tu

--   _+'_ : Test -> Test -> Test
--   _+'_ = subst (λ a -> a -> a -> a) (sym thepath) _+_



--   iu = transport thepath $ foldl _+'_ pointo ttu

data C : Type where
  point : C
  pointy : C -> C
  pathy : point ≡ pointy point

ppathy : pointy point ≡ pointy (pointy point)
ppathy i = pointy (pathy i)

pppathy : point ≡ pointy (pointy point)
pppathy i = hcomp (λ j -> λ where
                  (i = i0) -> point
                  (i = i1) -> pointy (pathy j)
            ) (pathy i)

ppppathy : pointy point ≡ pointy (pointy point)
ppppathy i = hcomp (λ j -> λ where
                  (i = i0) -> pathy j
                  (i = i1) -> pointy (pathy j)
            ) (pathy i)

hpathy : PathP (λ i -> pathy i ≡ pointy (pathy i) )
               (λ i -> pathy i)
               (λ i -> pointy (pathy i))
hpathy i j = {!!}



ωpathy : (p : C) -> p ≡ pointy p
ωpathy point = pathy
ωpathy (pointy p) = cong pointy (ωpathy p)
ωpathy (pathy i) = {!!}

Ωpathy : (p : C) -> point ≡ p
Ωpathy point = refl
Ωpathy (pointy p) i = hcomp (λ j -> λ where
        (i = i0) -> point
        (i = i1) -> pointy (Ωpathy p j)
  ) (pathy i)
Ωpathy (pathy j) i = {!!}


  -- hfill (λ k -> λ where
  --       (i = i0) -> pathy k
  --       (i = i1) -> pointy (Ωpathy point k)
  -- ) (inS (pathy j)) i


-- Old-Contr : isContr C
-- fst Old-Contr = point
-- snd Old-Contr y = {!!}
