
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Sum
open import Data.Product

infixr 4 _||_
infixr 5 _++_
infixr 5 _+++_
infixr 6 _+>_
infixr 6 _%_>_

data List : Set where
  [] : List
  _+>_ : ℕ -> List -> List

_++_ : List -> List -> List
[] ++ b = b
(x +> a) ++ b = x +> (a ++ b)

data Sorted : List -> Set where
  [] : Sorted []
  [-] : {n : ℕ} -> Sorted (n +> [])
  _+>_ : {l : List} {n m : ℕ} -> (n ≤ m) -> Sorted (m +> l) -> Sorted (n +> m +> l)

data Permutation : List -> List -> Set where
  [] : Permutation [] []
  _+>_ : (n : ℕ) -> {a b : List} -> Permutation a b -> Permutation (n +> a) (n +> b)
  _%_>_ : (n m : ℕ) -> {a b : List} -> Permutation a b -> Permutation (n +> m +> a) (m +> n +> b)
  _||_ : {a b c : List} -> Permutation a b -> Permutation b c -> Permutation a c

asdf : Permutation (4 +> 4 +> 7 +> 2 +> []) (7 +> 2 +> 4 +> 4 +> [])
asdf = 4 +> 4 % 7 > 2 +> [] || 4 % 7 > 4 % 2 > [] || 7 +> 4 % 2 > 4 +> []

perm-refl : (a : List) -> Permutation a a
perm-refl [] = []
perm-refl (x +> a) = x +> perm-refl a

perm-sym : {a b : List} -> Permutation a b -> Permutation b a
perm-sym [] = []
perm-sym (n +> x) = n +> perm-sym x
perm-sym (n % m > x) = m % n > perm-sym x
perm-sym (p || q) = perm-sym q || perm-sym p

perm-equiv : IsEquivalence Permutation
IsEquivalence.refl perm-equiv = perm-refl _
IsEquivalence.sym perm-equiv = perm-sym
IsEquivalence.trans perm-equiv = _||_

perm-setoid : Setoid _ _
Setoid.Carrier perm-setoid = List
Setoid._≈_ perm-setoid = Permutation
Setoid.isEquivalence perm-setoid = perm-equiv

_+++_ : {a b c d : List} -> Permutation a b -> Permutation c d -> Permutation (a ++ c) (b ++ d)
[] +++ cd = cd
(n +> ab) +++ cd = n +> (ab +++ cd)
(n % m > ab) +++ cd = n % m > (ab +++ cd)
(ab || b₁b) +++ cd = (ab +++ cd) || (b₁b +++ perm-refl _)

++-perm-sym : (a b : List) -> Permutation (a ++ b) (b ++ a)
++-perm-sym [] [] = []
++-perm-sym [] (y +> b) = y +> ++-perm-sym [] b
++-perm-sym (x +> a) [] = x +> ++-perm-sym a []
++-perm-sym (x +> a) (y +> b) = x +> ++-perm-sym a (y +> b)
                             || x % y > ++-perm-sym b a
                             || y +> ++-perm-sym (x +> a) b

open import Relation.Binary.Reasoning.Setoid perm-setoid

fdsa : Permutation (4 +> 4 +> 7 +> 2 +> []) (7 +> 2 +> 4 +> 4 +> [])
fdsa = begin
  4 +> 4 +> 7 +> 2 +> [] ≈⟨ 4 +> 4 % 7 > 2 +> [] ⟩
  4 +> 7 +> 4 +> 2 +> [] ≈⟨ 4 % 7 > 4 % 2 > [] ⟩
  7 +> 4 +> 2 +> 4 +> [] ≈⟨ 7 +> 4 % 2 > 4 +> [] ⟩
  7 +> 2 +> 4 +> 4 +> [] ∎



insert : ℕ -> List -> List
insert n [] = n +> []
insert n (x +> l) with n ≤? x
... | yes _ = n +> x +> l
... | no  _ = x +> insert n l

insert-sorted : (n : ℕ) (l : List) -> Sorted l -> Sorted (insert n l)
insert-sorted n [] S = [-]
insert-sorted n (x +> []) S with n ≤? x
... | yes p = p +> [-]
... | no np = (≰⇒≥ np) +> [-]
insert-sorted n (x +> y +> l) (s +> S) with n ≤? x
... | yes p = p +> s +> S
... | no np with insert-sorted n (y +> l) S
...         | IH with n ≤? y
...              | yes _ = (≰⇒≥ np) +> IH
...              | no  _ = s +> IH

insert-perm : (n : ℕ) (l : List) -> Permutation (insert n l) (n +> l)
insert-perm n [] = perm-refl _
insert-perm n (x +> l) with n ≤? x
... | yes _ = begin n +> x +> l ∎
... | no  _ = begin
    x +> insert n l ≈⟨ x +> insert-perm n l ⟩
    x +> n +> l     ≈⟨ x % n > perm-refl l  ⟩
    n +> x +> l     ∎


insertList : List -> List -> List
insertList [] o = o
insertList (x +> i) o = insertList i (insert x o)

insertList-sorted : (i : List) (o : List) -> Sorted o -> Sorted (insertList i o)
insertList-sorted [] o S = S
insertList-sorted (x +> i) o S = insertList-sorted i (insert x o) (insert-sorted x o S)

insertList-perm : (i o : List) -> Permutation (insertList i o) (i ++ o)
insertList-perm [] o = begin
    insertList [] o ≡⟨⟩
    o ≡⟨⟩
    [] ++ o ∎
insertList-perm (x +> i) o = begin
    insertList i (insert x o) ≈⟨ insertList-perm i (insert x o)   ⟩
    i ++ insert x o           ≈⟨ perm-refl i +++ insert-perm x o  ⟩
    i ++ x +> o               ≈⟨ ++-perm-sym i (x +> o)           ⟩
    x +> (o ++ i)             ≈⟨ x +> ++-perm-sym o i             ⟩
    x +> (i ++ o)             ∎

insertSort : List -> List
insertSort l = insertList l []

insertSort-sorted : (l : List) -> Sorted (insertSort l)
insertSort-sorted l = insertList-sorted l [] []

insertSort-perm : (l : List) -> Permutation (insertSort l) l
insertSort-perm l = begin
        insertList l [] ≈⟨ insertList-perm l [] ⟩
        l ++ [] ≈⟨ ++-perm-sym l [] ⟩
        [] ++ l ≡⟨⟩
        l ∎

list : List
list = 5 +> 3 +> 9 +> 8 +> 9 +> 3 +> 10 +> 9 +> []

slistperm : Permutation (insertSort list) list
slistperm = insertSort-perm list

slistsorted : Sorted (insertSort list)
slistsorted = insertSort-sorted list

verifiedInsertSort : (l : List) -> Σ[ s ∈ List ] Permutation s l × Sorted s
verifiedInsertSort l = insertSort l , (insertSort-perm l , insertSort-sorted l)
