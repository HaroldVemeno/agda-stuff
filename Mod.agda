{-# OPTIONS --safe #-}
module Mod where

open import Function
open import Data.Fin
open import Data.Nat as ℕ
  using (ℕ; zero; suc; z≤n; s≤s)

private variable k : ℕ

last : Fin (suc k)
last {k = zero} = zero
last {k = suc _} = suc last

subt'' : Fin k -> ℕ -> Fin k
subt'' zero zero = zero
subt'' {k = suc zero} zero (suc m) = zero
subt'' {k = suc (suc k')} zero (suc m) = suc (subt'' last m)
subt'' (suc n) zero = suc n
subt'' {k = suc (suc k')} (suc n) (suc m) = (subt'' (inject₁ n) m)

subt : Fin k -> Fin k -> Fin k
subt n m = subt'' n (toℕ m)

negate : Fin k -> Fin k
negate zero = zero
negate {k = suc (suc k')} (suc n) = suc  (subt last n)

add : Fin k -> Fin k -> Fin k
add n m = subt n (negate m)

mult' : ℕ -> Fin k -> Fin k
mult' {k = zero} n ()
mult' {k = suc _} zero m = zero
mult' (suc n) m = add m (mult' n m)

mult : Fin k -> Fin k -> Fin k
mult n m = mult' (toℕ n) m

zer : Fin 5
zer = zero
one : Fin 5
one = suc zero
two : Fin 5
two = suc (suc zero)
three : Fin 5
three = suc (suc (suc zero))
four : Fin 5
four = suc (suc (suc (suc zero)))
