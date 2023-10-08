{-# OPTIONS --cubical #-}
module Homo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Int hiding (_+_)

open Iso

-- data Croissant : Type where
--     point : Croissant
--     line  : point ≡ point
--     surface  : line ≡ line

data FilledCroissant : Type where
    point : FilledCroissant
    line  : point ≡ point
    surface  : line ≡ line
    filling  : surface ≡ refl

sa : ℤ -> ℤ
sa (pos n) = pos (suc n)
sa (negsuc n) = negsuc (suc n)

n2z : ℕ -> ℤ
n2z zero = pos zero
n2z (suc zero) = negsuc zero
n2z (suc (suc n)) = sa (n2z n)


z2n : ℤ -> ℕ
z2n (pos zero) = zero
z2n (pos (suc n)) = suc (suc (z2n (pos n)))
z2n (negsuc zero) = suc zero
z2n (negsuc (suc n)) = suc (suc (z2n (negsuc n)))

z2n2z : (z : ℤ) -> n2z (z2n z) ≡ z
z2n2z (pos zero) = refl
z2n2z (pos (suc n)) = cong sa (z2n2z (pos n))
z2n2z (negsuc zero) = refl
z2n2z (negsuc (suc n)) = cong sa (z2n2z (negsuc n))

z2nsa : (z : ℤ) -> z2n (sa z) ≡ suc (suc (z2n z))
z2nsa (pos n) = refl
z2nsa (negsuc n) = refl

n2z2n : (n : ℕ) -> z2n (n2z n) ≡ n
n2z2n zero = refl
n2z2n (suc zero) = refl
n2z2n (suc (suc n)) = z2nsa _ ∙ cong (λ a -> suc (suc a)) (n2z2n n)

ala : Iso ℕ ℤ
ala .fun = n2z
ala .inv = z2n
ala .rightInv = z2n2z
ala .leftInv = n2z2n

lol : ℕ ≡ ℤ
lol = isoToPath ala

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

bpathy : PathP (λ i -> pathy i ≡ pointy point)
               (λ i -> pathy i)
               (λ i -> pointy point)
bpathy i j = pathy (i ∨ j)

hpathy : PathP (λ i -> pathy i ≡ pointy (pathy i) )
               (λ i -> pathy i)
               (λ i -> pointy (pathy i))
hpathy i j = hcomp (λ k -> λ where
       (i = i0) -> pathy j
       (i = i1) -> pointy (pathy (k ∧ j))
       (j = i0) -> pathy i
       (j = i1) -> pointy (pathy (k ∧ i))
    ) (pathy  (i ∨ j))


ωpathy : (p : C) -> p ≡ pointy p
ωpathy point = pathy
ωpathy (pointy p) = cong pointy (ωpathy p)
ωpathy (pathy i) j = hpathy i j

-- Ωpathy : (p : C) -> p ≡ point
-- Ωpathy point = refl
-- -- Ωpathy (pointy p) i = hcomp (λ k -> λ where
-- --   (i = i0) -> ωpathy p k
-- --   (i = i1) -> point
-- --      ) (Ωpathy p i)
-- Ωpathy (pointy p) = sym (ωpathy p) ∙ Ωpathy p
-- Ωpathy (pathy i) j = {!!}

  -- hfill (λ k -> λ where
  --       (i = i0) -> pathy k
  --       (i = i1) -> pointy (Ωpathy point k)
  -- ) (inS (pathy j)) i


C-Contr : isContr C
fst C-Contr = point
snd C-Contr y = {!!}

private module _ where
    data nS1 : Type where
        base : nS1
        loop : base ≡ base
        nope : refl ≡ loop

    nS1-Contr : isContr nS1
    fst nS1-Contr = base
    snd nS1-Contr base = refl
    snd nS1-Contr (loop i) j = nope j i
    snd nS1-Contr (nope i j) k = nope (k ∧ i) j

    nS1≅Unit : Iso nS1 Unit
    Iso.fun nS1≅Unit _ = tt
    Iso.inv nS1≅Unit _ = base
    Iso.rightInv nS1≅Unit tt = refl
    Iso.leftInv nS1≅Unit base = refl
    Iso.leftInv nS1≅Unit (loop i) j = nope j i
    Iso.leftInv nS1≅Unit (nope i j) k = nope (k ∧ i) j

    nS1≡Unit : nS1 ≡ Unit
    nS1≡Unit = ua (isoToEquiv nS1≅Unit)

module _ where

    ContrToProp : (A : Type) -> isContr A -> isProp A
    ContrToProp A (c , f) x y i =
        hcomp (λ where
                 j (i = i0) -> f x j
                 j (i = i1) -> f y j
        ) c

    PropToSet : (A : Type) -> isProp A -> isSet A
    PropToSet A prp a b p q i j =
        hcomp (λ where
                    k (i = i0) -> prp a (p j) k
                    k (i = i1) -> prp a (q j) k
                    k (j = i0) -> prp a a k
                    k (j = i1) -> prp a b k)
               a

    data S1 : Type where
        base : S1
        loop : base ≡ base

    S1-¬Contr : ¬ isContr S1
    S1-¬Contr c = fls tru
      where

        pr : isSet S1
        pr = isProp→isSet (isContr→isProp c)

        tru : refl ≡ loop
        tru = pr _ _ refl loop

        invb : Bool -> Bool
        invb false = true
        invb true = false

        invi : Iso Bool Bool
        fun invi = invb
        inv invi = invb
        rightInv invi false = refl
        rightInv invi true = refl
        leftInv invi false = refl
        leftInv invi true = refl

        tobb : S1 -> Type
        tobb base = Bool
        tobb (loop i) = isoToPath invi i

        tobbb : base ≡ base -> Bool
        tobbb l =  subst tobb l true

        tf : Bool -> Type
        tf false = ⊥
        tf true = Unit

        fls : ¬ refl ≡ loop
        fls x = transport (cong tf  (cong tobbb x)) tt
