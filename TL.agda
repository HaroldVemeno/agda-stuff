{-# OPTIONS --safe #-}
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Data.List.Properties
open import Data.Nat
open import Data.List
open import Data.Nat.Tactic.RingSolver

data Expr : Set where
  const : ℕ → Expr
  plus : Expr → Expr → Expr

eval-expr : Expr → ℕ
eval-expr (const n) = n
eval-expr (plus e1 e2) = eval-expr e1 + eval-expr e2

eval-expr-tail' : Expr → ℕ → ℕ
eval-expr-tail' (const n) acc = n + acc
eval-expr-tail' (plus e1 e2) acc = eval-expr-tail' e2 (eval-expr-tail' e1 acc)

eval-expr-tail : Expr → ℕ
eval-expr-tail e = eval-expr-tail' e 0

eval-expr-cont' : {A : Set} → Expr → (ℕ → A) → A
eval-expr-cont' (const n) k = k n
eval-expr-cont' (plus e1 e2) k = eval-expr-cont' e2 λ n2 →
                                 eval-expr-cont' e1 λ n1 → k (n1 + n2)

eval-expr-cont : Expr → ℕ
eval-expr-cont e = eval-expr-cont' e (λ n → n)

data Instr : Set where
  push : ℕ → Instr
  add : Instr

Prog = List Instr

Stack = List ℕ

run : Prog → Stack → Stack
run [] s = s
run (push n ∷ p) s = run p (n ∷ s)
run (add ∷ p) (a1 ∷ a2 ∷ s) = run p (a1 + a2 ∷ s)
run (add ∷ p) s = run p s

compile : Expr → Prog
compile (const n) = push n ∷ []
compile (plus e1 e2) = compile e1 ++ compile e2 ++ add ∷ []

-- Task 1 - 1. Prove that eval-expr-tail is equivalent to eval-expr.

eet'+n-correct : (e : Expr) (n : ℕ) -> eval-expr-tail' e n ≡ (eval-expr e) + n
eet'+n-correct (const x) n = refl
eet'+n-correct (plus e f) n
    rewrite eet'+n-correct e n
          | eet'+n-correct f (eval-expr e + n)
    with eval-expr f | eval-expr e
... | a | b = solve (a ∷ b ∷ n ∷ [])

unfold-eet : ∀ e → eval-expr-tail e ≡ eval-expr-tail' e 0
unfold-eet e = refl

eet'-c : ∀ e → eval-expr-tail' e 0 ≡ eval-expr e
eet'-c (const x) rewrite (+-comm x 0) = refl
eet'-c (plus e f)
  rewrite eet'+n-correct e 0
        | eet'+n-correct f (eval-expr e + 0)
    with eval-expr f | eval-expr e
... | a | b = solve (a ∷ b ∷ [])

eval-expr-tail-correct : ∀ e → eval-expr-tail e ≡ eval-expr e
eval-expr-tail-correct = eet'-c

-- Task 1 - 2. Prove that eval-expr-cont is equivalent to eval-expr.
--
eec'k-c : ∀ e k → eval-expr-cont' e k ≡ k (eval-expr e)
eec'k-c (const x) k = refl
eec'k-c (plus e f) k
    = trans (eec'k-c f (λ n2 -> eval-expr-cont' e (λ n1 → k (n1 + n2)))) (
      trans (eec'k-c e (λ n1 -> k (n1 + eval-expr f))) refl)

eec'-c : ∀ e → eval-expr-cont' e (λ n -> n) ≡ eval-expr e
eec'-c e = eec'k-c e (λ n -> n)

eval-expr-cont-correct : ∀ e → eval-expr-cont e ≡ eval-expr e
eval-expr-cont-correct = eec'-c

-- Task 2. Prove that you get the expected result when you compile and run the program.

run-app : ∀ a b s -> run a (run b s) ≡ run (a ++ b) s
run-app [] b s = refl
run-app (push x ∷ a) b s
  rewrite sym (run-app a b (x ∷ s))= {!!}
run-app (add ∷ a) b s = {!!}

compile-correct : ∀ e → run (compile e) [] ≡ eval-expr e ∷ []
compile-correct (const x) = refl
compile-correct (plus e f) = {!!}
