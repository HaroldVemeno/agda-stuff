
open import Data.Nat hiding (_^_)
open import Data.Bool hiding (_≟_)
open import Relation.Binary
open import Relation.Nullary

choose : ℕ -> ℕ -> ℕ
choose n zero = 1
choose zero (suc k) = 0
choose (suc n) (suc k) with n ≟ k
... | yes _ = 1
... | no _ = choose n k + choose n (suc k)


_^_ : ℕ -> ℕ -> ℕ
zero ^ zero = 1
zero ^ suc e = 0
suc b ^ e = f e
  where
      f : ℕ -> ℕ
      f 0 = 1
      f (suc e') = choose e (suc e') * (b ^ (suc e')) + f e'
