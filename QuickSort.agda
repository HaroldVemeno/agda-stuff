module QuickSort where

open import Level using (Level) renaming (suc to lsuc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

infixr 6 _+>_
data List : Set where
  [] : List
  _+>_ : ℕ -> List -> List


infixr 4 _++_
_++_ : List -> List -> List
[] ++ b = b
(x +> a) ++ b = x +> (a ++ b)

length : List -> ℕ
length [] = 0
length (x +> a) = suc $ length a

filter : (ℕ -> Bool) -> List -> List
filter f [] = []
filter f (x +> a) with f x
... | true = x +> filter f a
... | false = filter f a

quicksort-gas : ℕ -> List -> List
quicksort-gas zero a = a
quicksort-gas (suc n) [] = []
quicksort-gas (suc n) (x +> a) =
              quicksort-gas n (filter (λ t -> does $ t <? x) a)
           ++ x +> quicksort-gas n (filter (λ t -> does $ x ≤? t) a)

quicksort : List -> List
quicksort a = quicksort-gas (length a) a

nnn : List
nnn = quicksort $ 1 +> 4 +> 5 +> 45 +> 1 +> 3 +> []

open ≡-Reasoning

nat-strong-ind' : (P : ℕ -> Set)
                 (P0 : P 0)
                 (Ind : (n : ℕ)
                        (Ip : (a : ℕ) -> (a ≤ n) -> P n)
                        -> P (suc n))
                 (n : ℕ) (k : ℕ) -> (k ≤ n) -> P k
nat-strong-ind' P P0 Ind n .zero z≤n = P0
nat-strong-ind' P P0 Ind (suc n) (suc k) (s≤s Q) with <-cmp n k
... | tri< n<k n≢k  n≯k = contradiction (≤∧≢⇒< Q (≢-sym n≢k)) n≯k
... | tri≈ n≮k refl n≯k = Ind k (nat-strong-ind' P P0 Ind n)
... | tri> n≮k n≢k  n>k = Ind {!!} {!!}
-- = Ind _ (nat-strong-ind' {!P!} {!P0!} {!!} _)
--
nat-strong-ind : (P : ℕ -> Set)
                 (Ind : (n : ℕ)
                        (Ip : (a : ℕ) -> (a < n) -> P a)
                        -> P n)
                 (n : ℕ) -> P n
nat-strong-ind P Ind n = {!!}


quicksort-gas-add : (l : List) (n : ℕ) -> quicksort-gas (length l) l ≡ quicksort-gas (length l + n) l
quicksort-gas-add l n = {!!}

data Sorted : List -> Set where
  [] : Sorted []
  [-] : {a : ℕ} -> Sorted (a +> [])
  _+>_ : {a b : ℕ}{r : List} ->  a ≤ b -> Sorted (b +> r) -> Sorted (a +> b +> r)

quicksort-sorted : (a : List) -> Sorted (quicksort a)
quicksort-sorted [] = []
quicksort-sorted (x +> a) = Sorted (quicksort-gas (length (x +> a)) (x +> a)) ∋ {!!}
