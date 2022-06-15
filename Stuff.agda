open import Data.Nat
open import Data.Sum

data Even : ℕ -> Set
data Odd : ℕ -> Set

data Even where
  even-0 : Even 0
  even-suc-odd : {n : ℕ} -> Odd n -> Even (suc n)

data Odd where
  odd-suc-even : {n : ℕ} -> Even n -> Odd (suc n)

even-or-odd : (n : ℕ) -> Even n ⊎ Odd n
even-or-odd zero = inj₁ even-0
even-or-odd (suc n') with even-or-odd n'
... | inj₁ even-n = inj₂ (odd-suc-even even-n)
... | inj₂ odd-n = inj₁ (even-suc-odd odd-n)
