
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Relation.Nullary

dneg : ∀ {A} -> A -> ¬ ¬ A
dneg a na = na a

tnegel : ∀ {A} -> ¬ ¬ ¬ A -> ¬ A
tnegel nnna a = nnna (dneg a)

exp : ∀ {A} -> ⊥ -> A
exp ()


postulate Pierce : ∀ {A} -> (¬ A -> A) -> A

dnegel : ∀ {A} -> ¬ ¬ A -> A
dnegel nna = Pierce λ na → exp (nna na)

xum : ∀ {A} -> A ⊎ ¬ A
xum = Pierce λ napem → inj₂ λ a → napem (inj₁ a)

nnpem : ∀ {A} -> ¬ ¬ (A ⊎ ¬ A)
nnpem napem = napem (inj₂ (λ a → napem (inj₁ a)))

ux : ∀ {A B} -> A ⊎ B -> ¬ (¬ A × ¬ B)
ux (inj₁ a) (na , nb) = na a
ux (inj₂ b) (na , nb) = nb b

xu : ∀ {A B} -> ¬ (¬ A × ¬ B) -> ¬ ¬ (A ⊎ B)
xu nnanb naub = nnanb ((λ a → naub (inj₁ a)) , (λ b → naub (inj₂ b)))

pp : ∀ {A B} -> ¬ (A ⊎ B) -> ¬ A × ¬ B
proj₁ (pp naub) a = naub (inj₁ a)
proj₂ (pp naub) b = naub (inj₂ b)

nnpempp : ∀ {A} -> ¬ ¬ (A ⊎ ¬ A)
nnpempp napem with pp napem
... | na , nna = nna na

bad : ∀ {A} -> ¬ (¬ A × A)
bad (fst , snd) = fst snd
