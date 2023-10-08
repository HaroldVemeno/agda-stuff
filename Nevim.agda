
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

S-inj : (n m : Nat) -> suc n ≡ suc m -> n ≡ m
S-inj n .n refl = refl
