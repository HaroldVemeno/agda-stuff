
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

rsum : ℕ -> ℕ
rsum zero = zero
rsum (suc n) = suc n + rsum n

infixl 7 _/2

_/2 : ℕ -> ℕ
zero /2 = zero
suc zero /2 = zero
suc (suc n) /2 = suc (n /2)

asum : ℕ -> ℕ
asum n = suc n * n /2

[n+n+k]/2≡n+k/2 : (n k : ℕ) -> (n + n + k) /2 ≡ n + (k /2)
[n+n+k]/2≡n+k/2 zero k = (0 + 0 + k) /2 ≡⟨⟩ k /2 ≡⟨⟩ 0 + (k /2) ∎
[n+n+k]/2≡n+k/2 (suc n) k =
    (suc n + suc n + k) /2 ≡⟨⟩
    suc (n + suc n + k) /2 ≡⟨ cong (λ a -> suc (a + k) /2) (+-comm n (suc n)) ⟩
    suc (suc n + n + k) /2 ≡⟨⟩
    suc (suc (n + n + k)) /2 ≡⟨⟩
    suc ((n + n + k) /2) ≡⟨ cong suc ([n+n+k]/2≡n+k/2 n k) ⟩
    suc (n + k /2) ≡⟨⟩
    suc n + k /2 ∎


asum≡rsum : (n : ℕ) -> rsum n ≡ asum n
asum≡rsum zero = rsum zero ≡⟨⟩ zero ≡⟨⟩ asum zero ∎
asum≡rsum (suc n) =
    rsum (suc n)                     ≡⟨⟩
    suc (n + rsum n)                 ≡⟨  cong (λ a -> suc (n + a))      (asum≡rsum n) ⟩
    suc (n + asum n)                 ≡⟨⟩
    suc (n + suc n * n /2)           ≡⟨  cong (λ a -> suc (n + a /2) )  (*-comm (suc n) n) ⟩
    suc (n + n * suc n /2)           ≡˘⟨ cong suc                       ([n+n+k]/2≡n+k/2 n (n * suc n)) ⟩
    suc ((n + n + n * suc n) /2)     ≡⟨  cong (λ a -> suc (a /2))       (+-assoc n n (n * suc n)) ⟩
    suc ((n + (n + n * suc n)) /2)   ≡˘⟨ cong (λ a -> suc ((n + a) /2)) (+-comm (n * suc n) n) ⟩
    suc ((n + (n * suc n + n)) /2)   ≡˘⟨ cong (λ a -> suc (a /2))       (+-assoc n (n * suc n) n) ⟩
    suc ((n + n * suc n + n) /2)     ≡⟨⟩
    suc (suc (n + n * suc n) + n) /2 ≡˘⟨ cong (λ a -> suc a /2)         (+-comm n (suc (n + n * suc n))) ⟩
    suc (n + suc (n + n * suc n)) /2 ≡⟨⟩
    suc (suc n) * suc n /2           ≡⟨⟩
    asum (suc n) ∎

open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver


:suc : Polynomial 1 → Polynomial 1
:suc = con 1 :+_

asum≡rsum' : (n : ℕ) -> rsum n ≡ asum n
asum≡rsum' zero = refl
asum≡rsum' (suc n) =
    rsum (suc n) ≡⟨⟩
    suc (n + rsum n)       ≡⟨ cong (λ a -> suc (n + a)) (asum≡rsum' n) ⟩
    suc (n + asum n)       ≡⟨⟩
    suc (n + suc n * n /2) ≡˘⟨ cong suc ([n+n+k]/2≡n+k/2 n (suc n * n)) ⟩
    suc (suc (n + n + suc n * n)) /2
        ≡⟨ cong (λ a -> a /2) (solve 1 (λ n ->
                  :suc (:suc (n :+ n :+ :suc n :* n))
               := :suc (:suc n) :* :suc n
             ) refl n) ⟩
    suc (suc n) * suc n /2 ≡⟨⟩
    asum (suc n) ∎

open import Data.List
open import Data.Nat.Tactic.RingSolver renaming (solve to solve!)

asum≡rsum'' : (n : ℕ) -> rsum n ≡ asum n
asum≡rsum'' zero = refl
asum≡rsum'' (suc n) =
    rsum (suc n) ≡⟨⟩
    suc (n + rsum n)       ≡⟨ cong (λ a -> suc (n + a)) (asum≡rsum' n) ⟩
    suc (n + asum n)       ≡⟨⟩
    suc (n + suc n * n /2) ≡˘⟨ cong suc ([n+n+k]/2≡n+k/2 n (suc n * n)) ⟩
    suc (suc (n + n + suc n * n)) /2
        ≡⟨ cong (_/2) (solve! (n ∷ [])) ⟩
    suc (suc n) * suc n /2 ≡⟨⟩
    asum (suc n) ∎

[n+n+k]/2≡n+k/2' : (n k : ℕ) -> (n + n + k) /2 ≡ n + (k /2)
[n+n+k]/2≡n+k/2' zero k = refl
[n+n+k]/2≡n+k/2' (suc n) k =
    (suc n + suc n + k) /2 ≡⟨ cong _/2 (solve! (n ∷ k ∷ [])) ⟩
    suc ((n + n + k) /2) ≡⟨ cong suc ([n+n+k]/2≡n+k/2' n k) ⟩
    suc n + k /2 ∎
