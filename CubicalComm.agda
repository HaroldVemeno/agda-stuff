{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Data.Nat

infixr 4 _,_

data UPair (A : Set) : Set where
  _,_ : A -> A -> UPair A
  comm : (a b : A) -> (a , b) ≡ (b , a)

th : UPair ℕ
th = 6 , 4

+-comm : (a b : ℕ) -> a + b ≡ b + a
+-comm zero zero = refl
+-comm zero (suc b) i = suc (+-comm zero b i)
+-comm (suc a) zero i = suc (+-comm a zero i)
+-comm (suc a) (suc b) = cong suc ( +-comm a (suc b) ∙∙ cong suc (+-comm b a) ∙∙ +-comm (suc a) b)

add : UPair ℕ -> ℕ
add (x , y) = x + y
add (comm a b i) = +-comm a b i

unorderize : {A O : Set} -> (f : A -> A -> O) -> ((a b : A) -> f a b ≡ f b a) -> (UPair A -> O)
unorderize f p (x , y) = f x y
unorderize f p (comm a b i) = p a b i

add' : UPair ℕ -> ℕ
add' = unorderize _+_ +-comm

infixr 5 _∷_

+-assoc : (a b c : ℕ) -> a + b + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

data UList (A : Set) : Set where
  [] : UList A
  _∷_ : A -> UList A -> UList A
  comm : (a b : A) (l : UList A) -> a ∷ b ∷ l ≡ b ∷ a ∷ l

sum : UList ℕ -> ℕ
sum [] = 0
sum (x ∷ a) = x + sum a
sum (comm a b l i) = (sym (+-assoc a b (sum l)) ∙∙ cong (_+ sum l) (+-comm a b) ∙∙ +-assoc b a (sum l)) i
