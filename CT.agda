{-# OPTIONS --safe #-}
module CT where

data Type : Set where
  Ans : Type
  _⇒_ : Type → Type → Type
infixr 10 _⇒_

data Context : Set where
  ∅ : Context
  _◂_ : Context → Type → Context
infixl 5 _◂_

variable
  Γ Δ : Context
  σ τ δ : Type

infix 4 _∋_ -- Variables
data _∋_ : Context → Type → Set where
  𝕫  :         Γ ◂ σ ∋ σ
  𝕤_ : Γ ∋ τ → Γ ◂ σ ∋ τ

infix 4 _⊢_ -- Terms
data _⊢_ : Context → Type → Set where
  ^_  : Γ ◂ σ ⊢ τ → Γ ⊢ σ ⇒ τ
  _∙_ : Γ ⊢ σ ⇒ τ → Γ ⊢ σ → Γ ⊢ τ
  𝕧_ : Γ ∋ σ → Γ ⊢ σ
infixr 100 𝕤_ 𝕧_
infixl 10 _∙_
infixr 9 ^_

data [_] : Type → Set where  -- Combinators
  𝑺 : [ (δ ⇒ σ ⇒ τ) ⇒ (δ ⇒ σ) ⇒ (δ ⇒ τ) ]
  𝑲 : [ σ ⇒ τ ⇒ σ ]
  _∙_ : [ σ ⇒ τ ] → [ σ ] → [ τ ]


translate : ∅ ⊢ σ → [ σ ]
translate t = ?