{-# OPTIONS --safe #-}
module InsertSort where
open import Data.Nat
open import Data.Empty
open import Data.Nat.Properties
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function


data List : Set where
  [] : List
  _+>_ : ℕ -> List -> List

infixr 20 _+>_

_++_ : List -> List -> List
[] ++ b = b
(x +> a) ++ b = x +> (a ++ b)

data Sorted : List -> Set where
  [] : Sorted []
  [-] : {n : ℕ} -> Sorted (n +> [])
  _+>_ : {l : List} {n m : ℕ} -> (n ≤ m) -> Sorted (m +> l) -> Sorted (n +> m +> l)

count : ℕ -> List -> ℕ
count n [] = 0
count n (x +> l) with n ≟ x
... | yes _ = 1 + count n l
... | no  _ = count n l

count-skip : (a b : ℕ) (l : List) -> a ≢ b -> count a (b +> l) ≡ count a l
count-skip a b l N with a ≟ b
... | yes p = ⊥-elim (N p)
... | no np = refl

count-step : (a : ℕ) (l : List) -> count a (a +> l) ≡ suc (count a l)
count-step a l with a ≟ a
... | yes p = refl
... | no np = ⊥-elim (np refl)

open import Relation.Binary

Perm : Rel List _
Perm a b = ∀ n -> count n a ≡ count n b


insert : ℕ -> List -> List
insert n [] = n +> []
insert n (x +> l) with n ≤? x
... | yes _ = n +> x +> l
... | no  _ = x +> insert n l

insertList : List -> List -> List
insertList [] o = o
insertList (x +> i) o = insertList i (insert x o)

insertSort : List -> List
insertSort i = insertList i []

Sorted-insert : (n : ℕ) (l : List) -> Sorted l -> Sorted (insert n l)
Sorted-insert n [] S = [-]
Sorted-insert n (x +> []) S with n ≤? x
... | yes p = p +> [-]
... | no np = (≰⇒≥ np) +> [-]
Sorted-insert n (x +> y +> l) (s +> S) with n ≤? x
... | yes p = p +> s +> S
... | no np with Sorted-insert n (y +> l) S
...         | IH with n ≤? y
...              | yes _ = (≰⇒≥ np) +> IH
...              | no  _ = s +> IH

Sorted-insertList : (i : List) (o : List) -> Sorted o -> Sorted (insertList i o)
Sorted-insertList [] o S = S
Sorted-insertList (x +> i) o S = Sorted-insertList i (insert x o) (Sorted-insert x o S)

Sorted-insertSort : (l : List) -> Sorted (insertSort l)
Sorted-insertSort l = Sorted-insertList l [] []

count-swap : (a b n : ℕ) (l : List) → count n (a +> b +> l) ≡ count n (b +> a +> l)
count-swap a b n l with n ≟ a | n ≟ b
...               | yes p | yes q rewrite p | q = refl
...               | yes p | no nq rewrite p | count-skip a b l nq | count-step a l = refl
...               | no np | yes q rewrite q | count-skip b a l np | count-step b l = refl
...               | no np | no nq rewrite count-skip n b l nq | count-skip n a l np = refl

Perm-refl : {a : List} -> Perm a a
Perm-refl = λ n → refl

Perm-insert : (n : ℕ) (l : List) -> Perm (insert n l) (n +> l)
Perm-insert n [] m = refl
Perm-insert n (x +> l) m with n ≤? x
... | yes p = refl
... | no np rewrite count-swap n x m l with m ≟ x
...            | yes q = cong suc (Perm-insert n l m)
...            | no nq = Perm-insert n l m

Perm-sym : {a b : List} -> Perm a b -> Perm b a
Perm-sym x n = sym (x n)

Perm-trans : {a b c : List} -> Perm a b -> Perm b c -> Perm a c
Perm-trans x y = λ n → trans (x n) (y n)

open ≡-Reasoning
open import Relation.Binary

++[] : (l : List) -> l ++ [] ≡ l
++[] [] = refl
++[] (x +> l) = x +> (l ++ []) ≡⟨ cong (λ a -> x +> a) (++[] l) ⟩ x +> l ∎

Perm-++swap : (u v : List) -> Perm (u ++ v) (v ++ u)
Perm-++swap [] y n = count n ([] ++ y) ≡⟨ cong (count n) (sym $ ++[] y) ⟩ count n (y ++ []) ∎
Perm-++swap x [] n = count n (x ++ []) ≡⟨ cong (count n) (++[] x) ⟩ count n ([] ++ x) ∎
Perm-++swap (x +> a) (y +> b) n
  with ayb <- Perm-++swap a (y +> b) n
     | xab <- Perm-++swap (x +> a) b n
     | ba <- Perm-++swap b a n
     | n ≟ x | n ≟ y
...      | yes p | yes q
              = cong suc $
                    count n (a ++ (y +> b)) ≡⟨ ayb ⟩
                    suc (count n (b ++ a))  ≡⟨ cong suc ba ⟩
                    suc (count n (a ++ b))  ≡⟨ xab ⟩
                    count n (b ++ (x +> a)) ∎
...      | no np | yes q
              = count n (a ++ (y +> b))       ≡⟨ ayb ⟩
                suc (count n (b ++ a))        ≡⟨ cong suc ba ⟩
                suc (count n (a ++ b))        ≡⟨ cong suc xab ⟩
                suc (count n (b ++ (x +> a))) ∎
...      | yes p | no nq
              = suc (count n (a ++ (y +> b))) ≡⟨ cong suc ayb ⟩
                suc (count n (b ++ a))        ≡⟨ cong suc ba ⟩
                suc (count n (a ++ b))        ≡⟨ xab ⟩
                count n (b ++ (x +> a))       ∎
...      | no np | no nq
              = count n (a ++ (y +> b)) ≡⟨ ayb ⟩
                count n (b ++ a) ≡⟨ ba ⟩
                count n (a ++ b) ≡⟨ xab ⟩
                count n (b ++ (x +> a)) ∎

wsum : ℕ -> ℕ -> ℕ
wsum 0 0 = 0
wsum x 0 = x
wsum 0 y = y
wsum (suc x) (suc y) = wsum (suc x) y + wsum x (suc y)

Perm-part : {a b : List} -> (c : List) -> Perm a b -> Perm (c ++ a) (c ++ b)
Perm-part [] p = p
Perm-part (x +> c) p n with n ≟ x
... | yes _ = cong suc (Perm-part c p n)
... | no  _ = Perm-part c p n

Perm-rpart : {a b : List} -> (c : List) -> Perm a b -> Perm (a ++ c) (b ++ c)
Perm-rpart {a} {b} c p n = count n (a ++ c) ≡⟨ Perm-++swap a c n ⟩
        count n (c ++ a) ≡⟨ Perm-part c p n ⟩
        count n (c ++ b) ≡⟨ Perm-++swap c b n ⟩
        count n (b ++ c) ∎

Perm-skip : {a b : List} {n : ℕ} -> Perm (n +> a) (n +> b) -> Perm a b
Perm-skip {n = n} c m
    with cc <- c m
       | m ≟ n
...  | yes _ = suc-injective cc
...  | no  _ = cc

Perm-cons : {a b : List} {n : ℕ} -> Perm a b -> Perm (n +> a) (n +> b)
Perm-cons {n = n} c m
    with cc <- c m
       | m ≟ n
...   | yes _ = cong suc cc
...   | no  _ = cc

Perm-insertList : (i o : List) -> Perm (insertList i o) (i ++ o)
Perm-insertList [] o n = refl
Perm-insertList (x +> i) o n =
                count n (insertList i (insert x o)) ≡⟨ Perm-insertList i (insert x o) n ⟩
                count n (i ++ insert x o) ≡⟨ Perm-rpart {a = {!!}} i (Perm-insert x o) n ⟩
                count n (x +> (o ++ i)) ≡⟨ Perm-part (x +> []) (Perm-++swap o i) n ⟩
                count n (x +> (i ++ o)) ∎

Perm-insertSort : (i : List) -> Perm (insertSort i) i
Perm-insertSort i n = count n (insertSort i) ≡⟨⟩
                      count n (insertList i []) ≡⟨ Perm-insertList i [] n ⟩
                      count n (i ++ []) ≡⟨ cong (count n) (++[] i) ⟩
                      count n i ∎

testl : List
testl = 4 +> 0 +> 43 +> 11 +> []
tests = insertSort testl
testS = Sorted-insertSort testl
testP = Perm-insertSort testl
