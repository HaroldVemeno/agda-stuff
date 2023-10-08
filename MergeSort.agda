module MergeSort where
open import Data.Nat
open import Data.Empty
open import Data.Nat.Properties
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product

infixr 3 _||_
infixr 4 _<<_
infixr 5 _++_
infixr 6 _+>_
infixr 6 _⇆_>_

data List : Set where
  [] : List
  _+>_ : ℕ -> List -> List

_++_ : List -> List -> List
[] ++ b = b
(x +> a) ++ b = x +> (a ++ b)

++[] : (l : List) -> l ++ [] ≡ l
++[] [] = refl
++[] (x +> l) = cong (λ a -> x +> a) (++[] l)

data Forall : (ℕ -> Set) -> List -> Set where
  [] : {f : ℕ -> Set} -> Forall f []
  _+>_ : {f : ℕ -> Set} -> {a : ℕ} -> {b : List} -> f a -> Forall f b -> Forall f (a +> b)

data StronglySorted : List -> Set where
  [] : StronglySorted []
  _+>_ : {l : List} {n : ℕ} -> Forall (λ m -> n ≤ m) l -> StronglySorted l -> StronglySorted (n +> l)

fdsa : StronglySorted (2 +> 3 +> 5 +> [])
fdsa = (s≤s (s≤s z≤n) +> s≤s (s≤s z≤n) +> []) +> (s≤s (s≤s (s≤s z≤n)) +> []) +> [] +> []

data Sorted : List -> Set where
  [] : Sorted []
  [-] : {n : ℕ} -> Sorted (n +> [])
  _+>_ : {l : List} {n m : ℕ} -> (n ≤ m) -> Sorted (m +> l) -> Sorted (n +> m +> l)

fufu : Sorted (2 +> 3 +> 5 +> [])
fufu = (s≤s (s≤s z≤n)) +> (s≤s (s≤s (s≤s z≤n)) +> [-])

map-forall : {l : List}{f g : ℕ -> Set} -> Forall f l -> ((n : ℕ) -> f n -> g n) -> Forall g l
map-forall [] mp = []
map-forall (x +> fa) mp = mp _ x +> map-forall fa mp

sorted->strong : {l : List} -> Sorted l -> StronglySorted l
sorted->strong [] = []
sorted->strong [-] = [] +> []
sorted->strong (x +> s) with sorted->strong s
... | fa +> ssl = (x +> map-forall fa λ n m≤n → ≤-trans x m≤n) +> fa +> ssl

strong->sorted : {l : List} -> StronglySorted l -> Sorted l
strong->sorted [] = []
strong->sorted ([] +> ss) = [-]
strong->sorted ((n≤a +> _) +> ss) = n≤a +> strong->sorted ss

ss-app : {l : List}{m : ℕ} (n : ℕ) -> StronglySorted (m +> l) -> n ≤ m -> StronglySorted (n +> m +> l)
ss-app n ss n≤m = sorted->strong (n≤m +> (strong->sorted ss))

nunu = sorted->strong fufu

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

split : List -> List × List
split [] = [] , []
split (e +> []) = e +> [] , []
split (e +> o +> t) = let (es , os) = split t in e +> es , o +> os

perm-++-float : (a b : List) (n : ℕ) -> Permutation (a ++ (n +> b)) (n +> a ++ b)
perm-++-float [] b n = perm-refl (n +> b)
perm-++-float (x +> a) b n = (x +> (perm-++-float a b n)) || (x ⇆ n > (perm-refl (a ++ b)))

perm-++-swap : (a b : List) -> Permutation (a ++ b) (b ++ a)
perm-++-swap [] b rewrite ++[] b = perm-refl b
perm-++-swap (x +> a) b = x +> (perm-++-swap a b) || perm-sym (perm-++-float b a x)

split-perm : (l : List) -> let (es , os) = split l in Permutation l (es ++ os)
split-perm [] = []
split-perm (e +> []) = e +> []
split-perm (e +> o +> l) = (e +> o +> split-perm l) || (e +> (perm-sym (perm-++-float (proj₁ (split l)) (proj₂ (split l)) o)))

data _<<_ : List -> List -> Set where
     z<<x : {x : ℕ}{a : List} -> [] << x +> a
     s<<s : {x y : ℕ}{a b : List} -> a << b -> x +> a << y +> b

k<<s : {x : ℕ}{a b : List} -> a << b -> a << x +> b
k<<s z<<x = z<<x
k<<s (s<<s a<<b) = s<<s (k<<s a<<b)

<<trans : {a b c : List}{n : ℕ} -> a << n +> b -> b << c -> a << c
<<trans z<<x z<<x = z<<x
<<trans z<<x (s<<s b<<c) = z<<x
<<trans (s<<s a<<b) (s<<s b<<c) = s<<s (<<trans a<<b b<<c )

<<appy : (l : List)(n : ℕ) -> l << n +> l
<<appy [] n = z<<x
<<appy (x +> l) n = s<<s (<<appy l x)

list-strind : (A : List -> Set) ->
              ((l : List) -> ((r : List) -> r << l -> A r) -> A l)
              -> (l : List) -> A l
list-strind A f l = lsi-imp A f (0 +> l) l (<<appy l 0)
  where lsi-imp : (A : List -> Set) ->
              ((l : List) -> ((r : List) -> r << l -> A r) -> A l)
              -> (l : List) -> (r : List) -> r << l -> A r
        lsi-imp A f .(_ +> _) .[] z<<x = f [] (λ _ ())
        lsi-imp A f .(_ +> _) .(_ +> _) (s<<s r<<l) = f (_ +> _) λ r r<<x -> lsi-imp A f _ _ (<<trans r<<x r<<l)

split-shorter : (l : List)(n m : ℕ) -> let (es , os) = split (n +> m +> l) in es << (n +> m +> l) × os << (n +> m +> l)
proj₁ (split-shorter [] n m) = s<<s z<<x
proj₁ (split-shorter (x +> []) n m) = s<<s (s<<s z<<x)
proj₁ (split-shorter (x +> y +> l) n m) = s<<s (k<<s (proj₁ (split-shorter l x y)))
proj₂ (split-shorter [] n m) = s<<s z<<x
proj₂ (split-shorter (x +> []) n m) = s<<s z<<x
proj₂ (split-shorter (x +> y +> l) n m) = s<<s (k<<s (proj₂ (split-shorter l x y)))


split-ind : (A : List -> Set) ->
            A [] -> ((n : ℕ) -> A (n +> [])) ->
            ((l : List) ->
            let (es , os) = split l in
                A es × A os -> A l
            ) -> (l : List) -> A l
split-ind A a0 a1 sf l = list-strind A sif l
  where sif : (x : List) (f : (y : List) (y<<x : y << x) → A y) → A x
        sif [] f = a0
        sif (x +> []) f = a1 x
        sif (x +> y +> l) f = let (es<< , os<<) = split-shorter l x y in sf (x +> y +> l) ((f _ es<<) , (f _ os<<))

split-rec : (A : Set) -> A -> (ℕ -> A) -> (A × A -> A) -> List -> A
split-rec A a0 a1 as = split-ind (λ _ -> A) a0 a1 (λ _ -> as)

merge : List -> List -> List
merge [] os = os
merge (e +> es) [] = e +> es
merge (e +> es) (o +> os) with e ≤? o | merge es (o +> os) | merge (e +> es) os
... | yes _ | r | _ = e +> r
... | no _  | _ | r = o +> r

merge-sorted : {a b : List} -> Sorted a -> Sorted b -> Sorted (merge a b)
merge-sorted [] sb = sb
merge-sorted [-] [] = [-]
merge-sorted {n +> []} {m +> []} [-] [-] with n ≤? m
... | yes n≤m = n≤m +> [-]
... | no  n≰m = ≰⇒≥ n≰m +> [-]
merge-sorted {n +> []} {m +> k +> l} [-] (m≤k +> sb) with n ≤? m
... | yes n≤m = n≤m +> m≤k +> sb
... | no  n≰m with n ≤? k | merge-sorted ([-] {n}) sb
...   | yes n≤k | _ = ≰⇒≥ n≰m +> n≤k +> sb
...   | no  n≰k | r = m≤k +> r
merge-sorted (n≤m +> sa) [] = n≤m +> sa
merge-sorted {n +> k +> l} {m +> []} (n≤k +> sa) [-] with n ≤? m
... | no  n≰m = ≰⇒≥ n≰m +> n≤k +> sa
... | yes n≤m with k ≤? m | merge-sorted sa ([-] {m})
...   | yes k≤m | r = n≤k +> r
...   | no  k≰m | _ = n≤m +> ≰⇒≥ k≰m +> sa
merge-sorted {n +> p +> l} {m +> q +> r} (n≤p +> sa) (m≤q +> sb) with n ≤? m
                                                                    | merge-sorted sa (m≤q +> sb)
                                                                    | merge-sorted (n≤p +> sa) sb
... | yes n≤m | i | _ with p ≤? m
...    | yes p≤m = n≤p +> i
...    | no  p≰m = n≤m +> i
merge-sorted {n +> p +> l} {m +> q +> r} (n≤p +> sa) (m≤q +> sb)
    | no  n≰m | _ | i with n ≤? q
...    | yes  n≤q = (≰⇒≥ n≰m) +> i
...    | no   n≰q = m≤q +> i

merge-perm : (a b : List) -> Permutation (a ++ b) (merge a b)
merge-perm [] b = perm-refl _
merge-perm (x +> a) [] rewrite ++[] a = perm-refl _
merge-perm (x +> a) (y +> b) with x ≤? y | merge-perm a (y +> b) | merge-perm (x +> a) b
... | yes x≤y | r | _ = x +> r
... | no  x≰y | _ | r = (x +> perm-++-float a b y) || (x ⇆ y > perm-refl _) || y +> r

forall-perm : {a b : List}{f : ℕ -> Set} -> Permutation a b -> Forall f a -> Forall f b
forall-perm [] fa = fa
forall-perm (n +> p) (fn +> fa) = fn +> forall-perm p fa
forall-perm (n ⇆ m > p) (fn +> fm +> fa) = fm +> fn +> forall-perm p fa
forall-perm (p || q) fa = forall-perm q (forall-perm p fa)

forall-++ : {a b : List}{f : ℕ -> Set} -> Forall f a -> Forall f b -> Forall f (a ++ b)
forall-++ [] fb = fb
forall-++ (x +> fa) fb = x +> forall-++ fa fb

merge-ssorted : {a b : List} -> StronglySorted a -> StronglySorted b -> StronglySorted (merge a b)
merge-ssorted [] ssb = ssb
merge-ssorted (xs +> ssa) [] = xs +> ssa
merge-ssorted {x +> a} {y +> b} (xs +> ssa) (ys +> ssb)
  with x ≤? y | merge-ssorted ssa (ys +> ssb) | merge-ssorted (xs +> ssa) ssb
... | yes x≤y | r | _ = forall-perm (merge-perm a (y +> b)) (forall-++ xs (x≤y +> (map-forall ys λ n -> ≤-trans x≤y))) +> r
... | no  x≰y | _ | r = forall-perm (merge-perm (x +> a) b) ((≰⇒≥ x≰y) +> forall-++ (map-forall xs (λ n -> ≤-trans (≰⇒≥ x≰y))) ys) +> r


merge-sort : List -> List
merge-sort = split-rec List [] (_+> []) (λ(a , b) -> merge a b)

uuuu = merge-sort (5 +> 3 +> 7 +> 8 +> 4 +> 3 +> 7 +> 1 +> 7 +> [])

merge-sort-perm : (l : List) -> Permutation l (merge-sort l)
merge-sort-perm = split-ind (λ l -> Permutation l (merge-sort l)) [] (λ n -> n +> [] ) msj
  where
    msj : (l : List) →
           Permutation (proj₁ (split l)) (merge-sort (proj₁ (split l))) ×
           Permutation (proj₂ (split l)) (merge-sort (proj₂ (split l))) →
           Permutation l (merge-sort l)
    msj [] (pl , pr) = []
    msj (x +> []) (pl , pr) = perm-refl _
    msj (x +> y +> l) (pl , pr) = {!!}

merge-sort-sorted : (l : List) -> StronglySorted (merge-sort l)
merge-sort-sorted = split-ind (λ l -> StronglySorted (merge-sort l)) [] (λ n → [] +> []) msj
  where
    msj : (l : List) →
        StronglySorted (merge-sort (proj₁ (split l))) ×
        StronglySorted (merge-sort (proj₂ (split l))) →
        StronglySorted (merge-sort l)
    msj [] (ml , mr) = {!!}
    msj (x +> []) (ml , mr) = {!!}
    msj (x +> x₁ +> l) (ml , mr) = {!!}
