{-# OPTIONS --cubical --safe #-}
module SymInt where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat

data Z : Type₀ where
  pos    : (n : ℕ) → Z
  neg    : (n : ℕ) → Z
  posneg : pos 0 ≡ neg 0

recℤ : ∀ {l} {A : Type l} → (pos' neg' : ℕ → A) → pos' 0 ≡ neg' 0 → Z → A
recℤ pos' neg' eq (pos m)    = pos' m
recℤ pos' neg' eq (neg m)    = neg' m
recℤ pos' neg' eq (posneg i) = eq i

indℤ : ∀ {l} (P : Z → Type l)
       → (pos' : ∀ n → P (pos n))
       → (neg' : ∀ n → P (neg n))
       → (λ i → P (posneg i)) [ pos' 0 ≡ neg' 0 ]
       → ∀ z → P z
indℤ P pos' neg' eq (pos n) = pos' n
indℤ P pos' neg' eq (neg n) = neg' n
indℤ P pos' neg' eq (posneg i) = eq i

sucℤ : Z → Z
sucℤ (pos n)       = pos (suc n)
sucℤ (neg zero)    = pos 1
sucℤ (neg (suc n)) = neg n
sucℤ (posneg _)    = pos 1

predℤ : Z → Z
predℤ (pos zero)    = neg 1
predℤ (pos (suc n)) = pos n
predℤ (neg n)       = neg (suc n)
predℤ (posneg _)    = neg 1

sucPredℤ : ∀ n → sucℤ (predℤ n) ≡ n
sucPredℤ (pos zero)    = sym posneg
sucPredℤ (pos (suc _)) = refl
sucPredℤ (neg _)       = refl
sucPredℤ (posneg i) j  = posneg (i ∨ ~ j)

predSucℤ : ∀ n → predℤ (sucℤ n) ≡ n
predSucℤ (pos _)       = refl
predSucℤ (neg zero)    = posneg
predSucℤ (neg (suc _)) = refl
predSucℤ (posneg i) j  = posneg (i ∧ j)

_+ℤ_ : Z → Z → Z
m +ℤ (pos (suc n)) = sucℤ   (m +ℤ pos n)
m +ℤ (neg (suc n)) = predℤ  (m +ℤ neg n)
m +ℤ _             = m

sucPathℤ : Z ≡ Z
sucPathℤ  = isoToPath (iso sucℤ predℤ sucPredℤ predSucℤ)

-- We do the same trick as in Cubical.Data.Int to prove that addition
-- is an equivalence
addEqℤ : ℕ → Z ≡ Z
addEqℤ zero    = refl
addEqℤ (suc n) = addEqℤ n ∙ sucPathℤ

predPathℤ : Z ≡ Z
predPathℤ = isoToPath (iso predℤ sucℤ predSucℤ sucPredℤ)

subEqℤ : ℕ → Z ≡ Z
subEqℤ zero    = refl
subEqℤ (suc n) = subEqℤ n ∙ predPathℤ

addℤ : Z → Z → Z
addℤ m (pos n)    = transport (addEqℤ n) m
addℤ m (neg n)    = transport (subEqℤ n) m
addℤ m (posneg _) = m

isEquivAddℤ : (m : Z) → isEquiv (λ n → addℤ n m)
isEquivAddℤ (pos n)    = isEquivTransport (addEqℤ n)
isEquivAddℤ (neg n)    = isEquivTransport (subEqℤ n)
isEquivAddℤ (posneg _) = isEquivTransport refl

addℤ≡+ℤ : addℤ ≡ _+ℤ_
addℤ≡+ℤ i  m (pos (suc n)) = sucℤ   (addℤ≡+ℤ i m (pos n))
addℤ≡+ℤ i  m (neg (suc n)) = predℤ  (addℤ≡+ℤ i m (neg n))
addℤ≡+ℤ i  m (pos zero)    = m
addℤ≡+ℤ i  m (neg zero)    = m
addℤ≡+ℤ _  m (posneg _)    = m

isEquiv+ℤ : (m : Z) → isEquiv (λ n → n +ℤ m)
isEquiv+ℤ = subst (λ _+_ → (m : Z) → isEquiv (λ n → n + m)) addℤ≡+ℤ isEquivAddℤ




data Sign : Type₀ where
  pos neg : Sign

sign : Z → Sign
sign (pos n)       = pos
sign (neg 0)       = pos
sign (neg (suc n)) = neg
sign (posneg i)    = pos

abs : Z → ℕ
abs (pos n) = n
abs (neg n) = n
abs (posneg i) = 0

signed : Sign → ℕ → Z
signed Sign.pos n = pos n
signed Sign.neg n = neg n

signed-inv : ∀ z → signed (sign z) (abs z) ≡ z
signed-inv (pos n)       = refl
signed-inv (neg zero)    = posneg
signed-inv (neg (suc n)) = refl
signed-inv (posneg i)    = \ j → posneg (i ∧ j)
{-
 The square for   signed-inv (posneg i)
              posneg i
       --------------------->
       ^                     ^
       |                     |
 pos 0 |                     | posneg j
       |                     |
       |                     |
       |                     |
       ---------------------->
         = pos 0
         = signed Sign.pos 0
         signed (sign (posneg i))
                (abs (posneg i))
-}


+-i-pos0 : ∀ a → pos zero +ℤ a ≡ a
+-i-pos0 (pos zero) = refl
+-i-pos0 (pos (suc n)) = cong sucℤ (+-i-pos0 (pos n))
+-i-pos0 (neg zero) = posneg
+-i-pos0 (neg (suc n)) = cong predℤ (+-i-pos0 (neg n))
+-i-pos0 (posneg i) j = posneg (i ∧ j)

+-i-zero : ∀ a i → posneg i +ℤ a ≡ a
+-i-zero (pos zero) i j = posneg (~ j ∧ j ∨ i)
+-i-zero (pos (suc n)) i j = cong sucℤ (+-i-zero (pos n) i) j
+-i-zero (neg zero) i j = posneg (j ∨ i)
+-i-zero (neg (suc n)) i j = cong predℤ (+-i-zero (neg n) i) j
+-i-zero (posneg i) j k = posneg ((~ k ∨ i) ∧ (k ∨ j))

{- {!(~ j ∧ i) ∨ (j ∧ k)!}
j k i
0 0 0 -> 0
0 0 1 -> 0
0 1 0 -> 0
0 1 1 -> 1
1 0 0 -> 1
1 0 1 -> 1
1 1 0 -> 0
1 1 1 -> 1
-}
