
open import Data.Bool.Base hiding (_≤_; _<_)
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Sum
open import Data.Product
infixr 4 _||_
infixr 5 _++_
infixr 5 _+++_
infixr 6 _+>_
infixr 6 _⇆_>_

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
  _⇆_>_ : (n m : ℕ) -> {a b : List} -> Permutation a b -> Permutation (n +> m +> a) (m +> n +> b)
  _||_ : {a b c : List} -> Permutation a b -> Permutation b c -> Permutation a c

asdf : Permutation (4 +> 4 +> 7 +> 2 +> []) (7 +> 2 +> 4 +> 4 +> [])
asdf = 4 +> 4 ⇆ 7 > 2 +> [] || 4 ⇆ 7 > 4 ⇆ 2 > [] || 7 +> 4 ⇆ 2 > 4 +> []


perm-refl : (a : List) -> Permutation a a
perm-refl [] = []
perm-refl (x +> a) = x +> perm-refl a

perm-sym : {a b : List} -> Permutation a b -> Permutation b a
perm-sym [] = []
perm-sym (n +> x) = n +> perm-sym x
perm-sym (n ⇆ m > x) = m ⇆ n > perm-sym x
perm-sym (p || q) = perm-sym q || perm-sym p

perm-equiv : IsEquivalence Permutation
IsEquivalence.refl perm-equiv = perm-refl _
IsEquivalence.sym perm-equiv = perm-sym
IsEquivalence.trans perm-equiv = _||_

perm-setoid : Setoid _ _
Setoid.Carrier perm-setoid = List
Setoid._≈_ perm-setoid = Permutation
Setoid.isEquivalence perm-setoid = perm-equiv

open import Relation.Binary.Reasoning.Setoid perm-setoid

_+++_ : {a b c d : List} -> Permutation a b -> Permutation c d -> Permutation (a ++ c) (b ++ d)
[] +++ cd = cd
(n +> ab) +++ cd = n +> (ab +++ cd)
(n ⇆ m > ab) +++ cd = n ⇆ m > (ab +++ cd)
(ax || xb) +++ cd = (ax +++ cd) || (xb +++ perm-refl _)

++-perm-sym : (a b : List) -> Permutation (a ++ b) (b ++ a)
++-perm-sym [] [] = []
++-perm-sym [] (y +> b) = y +> ++-perm-sym [] b
++-perm-sym (x +> a) [] = x +> ++-perm-sym a []
-- ++-perm-sym (x +> a) (y +> b) = x +> ++-perm-sym a (y +> b)
--                              || x ⇆ y > ++-perm-sym b a
--                              || y +> ++-perm-sym (x +> a) b
++-perm-sym (x +> a) (y +> b) = begin
   x +> (a ++ y +> b) ≈⟨ x +> ++-perm-sym a (y +> b) ⟩
   x +> y +> (b ++ a) ≈⟨ x ⇆ y > ++-perm-sym b a    ⟩
   y +> x +> (a ++ b) ≈⟨ y +> ++-perm-sym (x +> a) b ⟩
   y +> (b ++ x +> a) ∎


fdsa : Permutation (4 +> 4 +> 7 +> 2 +> []) (7 +> 2 +> 4 +> 4 +> [])
fdsa = begin
  4 +> 4 +> 7 +> 2 +> [] ≈⟨ 4 +> 4 ⇆ 7 > 2 +> [] ⟩
  4 +> 7 +> 4 +> 2 +> [] ≈⟨ 4 ⇆ 7 > 4 ⇆ 2  > [] ⟩
  7 +> 4 +> 2 +> 4 +> [] ≈⟨ 7 +> 4 ⇆ 2 > 4 +> [] ⟩
  7 +> 2 +> 4 +> 4 +> [] ∎

insert : ℕ -> List -> List
insert n [] = n +> []
insert n (x +> l) with n ≤? x
... | yes _ = n +> x +> l
... | no  _ = x +> insert n l

insert-sorted : (n : ℕ) (l : List) -> Sorted l -> Sorted (insert n l)
insert-sorted n [] [] = [-]
insert-sorted n (x +> []) [-] with n ≤? x
... | yes n≤x = n≤x +> [-]
... | no  n≰x =  (≰⇒≥ n≰x) +> [-]
insert-sorted n (x +> y +> l) (x≤y +> Syl) with n ≤? x
... | yes n≤x = n≤x +> x≤y +> Syl
... | no  n≰x with Sinyl <- insert-sorted n (y +> l) Syl
                 | n ≤? y
...         | yes n≤y = (≰⇒≥ n≰x) +> Sinyl
...         | no  n≰y = x≤y +> Sinyl

insert-perm : (n : ℕ) (l : List) -> Permutation (insert n l) (n +> l)
insert-perm n [] = perm-refl _
insert-perm n (x +> l) with n ≤? x
... | yes _ = begin n +> x +> l ∎
... | no  _ = begin
    x +> insert n l ≈⟨ x +> insert-perm n l ⟩
    x +> n +> l     ≈⟨ x ⇆ n > perm-refl l  ⟩
    n +> x +> l     ∎

insertList : List -> List -> List
insertList [] o = o
insertList (x +> i) o = insertList i (insert x o)

insertList-sorted : (i : List) (o : List) -> Sorted o -> Sorted (insertList i o)
insertList-sorted [] o S = S
insertList-sorted (x +> i) o S = insertList-sorted i (insert x o) (insert-sorted x o S)

insertList-perm : (i o : List) -> Permutation (insertList i o) (i ++ o)
insertList-perm [] o = begin o ∎
insertList-perm (x +> i) o = begin
    insertList i (insert x o) ≈⟨ insertList-perm i (insert x o)   ⟩
    i ++ insert x o           ≈⟨ perm-refl i +++ insert-perm x o  ⟩
    i ++ (x +> o)             ≈⟨ ++-perm-sym i (x +> o)           ⟩
    (x +> o) ++ i             ≡⟨⟩
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
list = 5 +> 3 +> 2 +> 8 +> 9 +> 5 +> 10 +> 4 +> []

list2 : List
list2 = 5 +> 3 +> 9 +> 7 +> 10 +> []

list3 : List
list3 = 1 +> 2 +> 3 +> []

testperm : Permutation (insertSort list3) list3
testperm = insertSort-perm list3

slist2perm : Permutation (insertSort list2) list2
slist2perm = insertSort-perm list2

slistperm : Permutation (insertSort list) list
slistperm = insertSort-perm list

slistsorted : Sorted (insertSort list)
slistsorted = insertSort-sorted list

verifiedInsertSort : (l : List) -> Σ[ s ∈ List ] Permutation s l × Sorted s
verifiedInsertSort l = insertSort l , (insertSort-perm l , insertSort-sorted l)

perm-map-+> : {a b : List} (n : ℕ) -> Permutation a b -> Permutation (n +> a) (n +> b)
perm-map-+> n [] = n +> []
perm-map-+> n (m +> x) = n +> m +> x
perm-map-+> n (m ⇆ k > x) = n +> m ⇆ k > x
perm-map-+> n (l || r) = perm-map-+> n l || perm-map-+> n r

perm-map-⇆> : {a b : List} (n m : ℕ) -> Permutation a b -> Permutation (n +> m +> a) (m +> n +> b)
perm-map-⇆> n m [] = n ⇆ m > []
perm-map-⇆> n m (k +> x) = n ⇆ m > k +> x
perm-map-⇆> n m (k ⇆ j > x) = n ⇆ m > k ⇆ j > x
perm-map-⇆> n m (l || r) = perm-map-⇆> n m l || perm-map-+> m (perm-map-+> n r)

perm-flatten : {a b : List} -> Permutation a b -> Permutation a b
perm-flatten [] = []
perm-flatten (n +> pr) = perm-map-+> n (perm-flatten pr)
perm-flatten (n ⇆ m > pr) = perm-map-⇆> n m (perm-flatten pr)
perm-flatten (l || r) = perm-flatten l || perm-flatten r

perm-reassoc-to : {a b c : List} -> Permutation a b -> Permutation b c -> Permutation a c
perm-reassoc-to (l || r) o = perm-reassoc-to l (perm-reassoc-to r o)
perm-reassoc-to i o = i || o

perm-reassoc : {a b : List} -> Permutation a b -> Permutation a b
perm-reassoc p = perm-reassoc-to p (perm-refl _)

_≟ₗ_ : DecidableEquality List
[] ≟ₗ [] = true because ofʸ refl
[] ≟ₗ (n +> l) = false because ofⁿ λ()
(n +> l) ≟ₗ [] = false because ofⁿ λ()
(x +> xs) ≟ₗ (y +> ys) with x ≟ y | xs ≟ₗ ys
... | yes refl | yes refl  = true because ofʸ refl
... | yes refl | no  xs≢ys = false because ofⁿ λ {refl -> xs≢ys refl}
... | no x≢y   | yes refl  = false because ofⁿ λ {refl -> x≢y refl}
... | no x≢y   | no  xs≢ys = false because ofⁿ λ {refl -> x≢y refl}

perm-unrefl : {a b : List} -> Permutation a b -> Permutation a b
perm-unrefl {a} {b} (_||_ {b = c} p q) with a ≟ₗ c | c ≟ₗ b
... | yes refl | yes refl = perm-refl a
... | yes refl | no _ = perm-unrefl q
... | no _ | yes refl = perm-unrefl p
... | no _ | no _ = perm-unrefl p || perm-unrefl q
perm-unrefl {a} {b} p with a ≟ₗ b
... | yes refl = perm-refl a
... | no a≢b with p
...     | [] = contradiction refl a≢b
...     | n +> q = n +> perm-unrefl q
...     | n ⇆ m > q = n ⇆ m > perm-unrefl q
...     | q || r = p

perm-normalize : {a b : List} -> Permutation a b -> Permutation a b
perm-normalize p = perm-reassoc (perm-flatten (perm-unrefl p))

length : List -> ℕ
length [] = 0
length (x +> a) = 1 + length a

perm-length : {a b : List} -> Permutation a b -> length a ≡ length b
perm-length [] = refl
perm-length (n +> x) = cong suc (perm-length x)
perm-length (n ⇆ m > x) = cong (suc ∘ suc) (perm-length x)
perm-length (x || y) = trans (perm-length x) (perm-length y)

nperm-length : {a b : List} -> length a ≢ length b -> ¬ Permutation a b
nperm-length nl p = contradiction (perm-length p) nl

perm-len-contr : {a b : List} -> length a ≢ length b -> Permutation a b -> ⊥
perm-len-contr x y = x (perm-length y)


gnasd : {a b : ℕ} -> a ≢ b -> ¬ Permutation (a +> []) (b +> [])
gnasd {a} {.a} a≢a (.a +> p) = a≢a refl
gnasd a≢b (_||_ {b = []} x y) = perm-len-contr (λ()) y
gnasd a≢b (_||_ {b = n +> m +> r} x y) = perm-len-contr (λ()) y
gnasd {a} {b} a≢b (_||_ {b = n +> []} x y) with a ≟ n
... | yes refl = gnasd a≢b y
... | no a≢n = gnasd a≢n x 


nasd : ¬ Permutation (4 +> []) (7 +> [])
nasd p = gnasd (λ()) p

count : ℕ -> List -> ℕ
count n [] = 0
count n (x +> l) with x ≟ n
... | yes _ = suc (count n l)
... | no _  = count n l

CPermutation : List -> List -> Set _
CPermutation a b = (n : ℕ) -> count n a ≡ count n b

Perm->CPerm : {a b : List} -> Permutation a b -> CPermutation a b
Perm->CPerm [] c = refl
Perm->CPerm (n +> p) c with n ≟ c
... | yes _ = cong suc (Perm->CPerm p c)
... | no _  = Perm->CPerm p c
Perm->CPerm (n ⇆ m > p) c with n ≟ c in nc | m ≟ c in mc
... | yes _ | yes _ rewrite nc | mc = cong (suc ∘ suc) (Perm->CPerm p c)
... | yes _ | no  _ rewrite nc | mc = cong suc (Perm->CPerm p c)
... | no  _ | yes _ rewrite nc | mc = cong suc (Perm->CPerm p c)
... | no  _ | no  _ rewrite nc | mc = Perm->CPerm p c
Perm->CPerm (p || q) c = trans (Perm->CPerm p c) (Perm->CPerm q c)

¬CPerm->¬Perm : {a b : List} -> ¬ CPermutation a b -> ¬ Permutation a b
¬CPerm->¬Perm ¬CP P =  ¬CP (Perm->CPerm P)
