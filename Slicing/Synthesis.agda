open import Core
open import Semantics.Statics

module Slicing.Synthesis where

-- Slicing
data SynSlice {Γ : Assms} {e : Exp} {τ : Typ} : (syn : Γ ⊢ e ↦ τ)
              → (γ : ⌊ Γ ⌋) → (s : ⌊ e ⌋) → (υ : ⌊ τ ⌋) → Set where
  is : ∀ {syn γ s υ} γ .↓ ⊢ s .↓ ↦ υ .↓ → SynSlice syn γ s υ
       

-- min: {syn} → minSynSlice syn γ s υ → SynSlice syn γ' s' υ' → (γ ⊑Assm γ', s ⊑e s', υ ⊑t υ')

-- join: SynSlice
-- join = ⨆_{min: minSynSlice} min
