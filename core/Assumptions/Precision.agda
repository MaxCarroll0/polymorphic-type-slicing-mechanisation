module core.Assumptions.Precision where

open import Data.List using (List; []; _∷_; length)
open import Relation.Binary using (IsPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong₂)

open import core.Typ using (Typ; □)
open import core.Typ.Precision using (_⊑t_; ⊑?; ⊑t-refl; ⊑t-trans; ⊑t-antisym)
open import core.Assumptions.Base

-- Pointwise precision relation (only defined for equal-length lists)
data _⊑Γ_ : Assumptions → Assumptions → Set where
  ⊑[]  :                                             []       ⊑Γ []
  ⊑∷   : ∀ {τ τ' Γ Γ'} → τ ⊑t τ' → Γ ⊑Γ Γ' →         (τ ∷ Γ)  ⊑Γ (τ' ∷ Γ')

infix 4 _⊑Γ_

-- Reflexivity
⊑Γ-refl : Reflexive _⊑Γ_
⊑Γ-refl {[]}    = ⊑[]
⊑Γ-refl {_ ∷ _} = ⊑∷ ⊑t-refl ⊑Γ-refl

-- Transitivity
⊑Γ-trans : Transitive _⊑Γ_
⊑Γ-trans ⊑[]        ⊑[]        = ⊑[]
⊑Γ-trans (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊑t-trans p₁ p₂) (⊑Γ-trans q₁ q₂)

-- Antisymmetry
⊑Γ-antisym : Antisymmetric _≡_ _⊑Γ_
⊑Γ-antisym ⊑[]        ⊑[]        = refl
⊑Γ-antisym (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = cong₂ _∷_ (⊑t-antisym p₁ p₂) (⊑Γ-antisym q₁ q₂)

-- Partial order
⊑Γ-isPartialOrder : IsPartialOrder _≡_ _⊑Γ_
⊑Γ-isPartialOrder = record
  { isPreorder = record
    { isEquivalence = Eq.isEquivalence
    ; reflexive     = λ where refl → ⊑Γ-refl
    ; trans         = ⊑Γ-trans
    }
  ; antisym = ⊑Γ-antisym
  }

-- □Γ n is the minimum for any same-length list
□Γ-min : ∀ Γ → □Γ (length Γ) ⊑Γ Γ
□Γ-min []      = ⊑[]
□Γ-min (_ ∷ Γ) = ⊑∷ ⊑? (□Γ-min Γ)
