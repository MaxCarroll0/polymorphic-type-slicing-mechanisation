module Core.Typ.Precision where

open import Relation.Binary using (IsPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)

open import Core.Typ.Base

-- Slices (Precision)
data _⊑t_ : Typ → Typ → Set where
  ⊑?   : ∀ {τ}             →                         □       ⊑t τ
  ⊑*   :                                             *       ⊑t *
  ⊑Var : ∀ {n}             →                         ⟨ n ⟩   ⊑t ⟨ n ⟩
  ⊑+   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ + τ₂ ⊑t τ₁' + τ₂'
  ⊑×   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ × τ₂ ⊑t τ₁' × τ₂'
  ⊑⇒   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ ⇒ τ₂ ⊑t τ₁' ⇒ τ₂'
  ⊑∀   : ∀ {τ τ'}          → τ ⊑t τ'               → ∀· τ    ⊑t ∀· τ'

infix 4 _⊑t_

-- Slices form a partial order
⊑t-refl : Reflexive _⊑t_
⊑t-refl {⟨ _ ⟩}   = ⊑Var
⊑t-refl {*}       = ⊑*
⊑t-refl {□}       = ⊑?
⊑t-refl {_ + _}   = ⊑+ ⊑t-refl ⊑t-refl
⊑t-refl {_ × _}   = ⊑× ⊑t-refl ⊑t-refl
⊑t-refl {_ ⇒ _}   = ⊑⇒ ⊑t-refl ⊑t-refl
⊑t-refl {∀· _}    = ⊑∀ ⊑t-refl

⊑t-trans : Transitive _⊑t_
⊑t-trans ⊑? _              = ⊑?
⊑t-trans ⊑* ⊑*             = ⊑*
⊑t-trans ⊑Var ⊑Var         = ⊑Var
⊑t-trans (⊑+ p q) (⊑+ r s) = ⊑+ (⊑t-trans p r) (⊑t-trans q s)
⊑t-trans (⊑× p q) (⊑× r s) = ⊑× (⊑t-trans p r) (⊑t-trans q s)
⊑t-trans (⊑⇒ p q) (⊑⇒ r s) = ⊑⇒ (⊑t-trans p r) (⊑t-trans q s)
⊑t-trans (⊑∀ p) (⊑∀ q)     = ⊑∀ (⊑t-trans p q)

⊑t-antisym : Antisymmetric _≡_ _⊑t_
⊑t-antisym ⊑? ⊑?             = refl
⊑t-antisym ⊑* ⊑*             = refl
⊑t-antisym ⊑Var ⊑Var         = refl
⊑t-antisym (⊑+ p q) (⊑+ r s) = cong₂ _+_ (⊑t-antisym p r) (⊑t-antisym q s)
⊑t-antisym (⊑× p q) (⊑× r s) = cong₂ _×_ (⊑t-antisym p r) (⊑t-antisym q s)
⊑t-antisym (⊑⇒ p q) (⊑⇒ r s) = cong₂ _⇒_ (⊑t-antisym p r) (⊑t-antisym q s)
⊑t-antisym (⊑∀ p) (⊑∀ q)     = cong ∀· (⊑t-antisym p q)

⊑t-isPartialOrder : IsPartialOrder _≡_ _⊑t_
⊑t-isPartialOrder = record
  { isPreorder = record
    { isEquivalence = Eq.isEquivalence
    ; reflexive = λ where refl → ⊑t-refl
    ; trans = ⊑t-trans
    }
  ; antisym = ⊑t-antisym
  }
