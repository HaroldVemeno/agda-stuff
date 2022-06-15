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
                 (Ind : (n : ℕ)
                        (Ip : (a : ℕ) -> (a < n) -> P a)
                        -> P n)
                 (n : ℕ) (k : ℕ) -> (k < n) -> P k
nat-strong-ind' P Ind (suc n) k (s≤s k≤n)
  = Ind k λ a a<k -> nat-strong-ind' P Ind n a (<-transˡ a<k k≤n )

nat-strong-ind : (P : ℕ -> Set)
                 (Ind : (n : ℕ)
                        (Ip : (a : ℕ) -> (a < n) -> P a)
                        -> P n)
                 (n : ℕ) -> P n
nat-strong-ind P Ind n = nat-strong-ind' P Ind (suc n) n ≤-refl

list-strong-ind' : {ℓ : Level} (P : List -> Set ℓ)
                 (Ind : (l : List)
                        (Ip : (a : List) -> (length a < length l) -> P a)
                        -> P l)
                 (l : List) (k : List) -> (length k < length l) -> P k
list-strong-ind' P Ind (x₁ +> l) k (s≤s k≤l)
  = Ind k λ a a<k -> list-strong-ind' P Ind l a (<-transˡ a<k k≤l)

list-strong-ind : {ℓ : Level} (P : List -> Set ℓ)
                 (Ind : (l : List)
                        (Ip : (a : List) -> (length a < length l) -> P a)
                        -> P l)
                 (l : List) -> P l
list-strong-ind P Ind l = list-strong-ind' P Ind (6 +> l) l ≤-refl

filter-smaller : (l : List) (f : ℕ -> Bool) -> length (filter f l) ≤ length l
filter-smaller [] f = ≤-refl
filter-smaller (x +> l) f with f x
... | false = ≤pred⇒≤ (filter-smaller l f)
... | true = s≤s (filter-smaller l f)

quicksort-gas-add : (l : List) (n : ℕ) -> quicksort-gas (length l) l ≡ quicksort-gas (length l + n) l
quicksort-gas-add l n =
    list-strong-ind (λ l n -> quicksort-gas (length l) l ≡ quicksort-gas (length l + n) l) (
      λ where
        [] Ind → {!!}
        (x +> l) Ind → {!!}
    ) l n

data Sorted : List -> Set where
  [] : Sorted []
  [-] : {a : ℕ} -> Sorted (a +> [])
  _+>_ : {a b : ℕ}{r : List} ->  a ≤ b -> Sorted (b +> r) -> Sorted (a +> b +> r)

quicksort-sorted : (a : List) -> Sorted (quicksort a)
quicksort-sorted [] = []
quicksort-sorted (x +> a) = Sorted (quicksort-gas (length (x +> a)) (x +> a)) ∋ {!!}
