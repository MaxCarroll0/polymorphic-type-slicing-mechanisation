module Core.Assms.BiasedPrecision where

open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (yes; no)

open import Core.Instances
open import Core.Typ.Base using () renaming (□ to □t)
open import Core.Typ hiding (□)
open import Core.Assms.Base
open import Core.Assms.Precision
open import Core.Assms.Lattice

-- 'Biased' precision: pointwise precision on the domain of the RHS
-- Corresponds to the idea of available assumptions being used at least as much as available

-- This NOT a partial order or preorder.
-- - □ ≼ τ and τ ≼ □ but □ ≢ τ
-- - * ≼ □ ≼ ⟨0⟩ but * ⋠ ⟨0⟩

data _≼a_ : Assms → Assms → Set where
  ≼[]   :                                              []       ≼a []
  ≼∷    : ∀ {τ τ' Γ Γ'} → τ ⊑ τ' → τ ≢ □t → Γ ≼a Γ'  → (τ ∷ Γ)  ≼a (τ' ∷ Γ')
  ≼□L∷  : ∀ {τ' Γ Γ'}                      → Γ ≼a Γ' → (□t ∷ Γ) ≼a (τ' ∷ Γ')
  ≼□R∷  : ∀ {τ Γ Γ'}                       → Γ ≼a Γ' → (τ ∷ Γ)  ≼a (□t ∷ Γ')

infix 4 _≼a_

≼-refl : ∀ {Γ} → Γ ≼a Γ
≼-refl {[]}    = ≼[]
≼-refl {τ ∷ Γ} with τ ≟ □t
... | yes refl = ≼□L∷ ≼-refl
... | no  ne   = ≼∷ (⊑.refl {Typ}) ne ≼-refl

_≼ₛ_ : ∀ {Γ : Assms} → ⌊ Γ ⌋ → ⌊ Γ ⌋ → Set
_≼ₛ_ s₁ s₂ = s₁ .↓ ≼a s₂ .↓

infix 4 _≼ₛ_

≼ₛ-refl : ∀ {Γ : Assms} {s : ⌊ Γ ⌋} → s ≼ₛ s
≼ₛ-refl = ≼-refl


-- join-closure (right side)
postulate
  ≼ₛ-⊔ₛ-closed : ∀ {Γ : Assms} (lb s₁ s₂ : ⌊ Γ ⌋)
                 → lb ≼ₛ s₁ → lb ≼ₛ s₂
                 → lb ≼ₛ (s₁ ⊔ₛ s₂)

-- Weakening
⊑-≼-trans : ∀ {A B γ : Assms} → A ⊑a B → B ≼a γ → A ≼a γ
⊑-≼-trans ⊑[] ≼[] = ≼[]
⊑-≼-trans (⊑∷ {τ = a} a⊑b rest) (≼∷ b⊑γ b≢□ q) with a ≟ □t
... | yes refl = ≼□L∷ (⊑-≼-trans rest q)
... | no  a≢□  = ≼∷ (⊑.trans {A = Typ} a⊑b b⊑γ) a≢□ (⊑-≼-trans rest q)
⊑-≼-trans (⊑∷ _ rest) (≼□R∷ q) = ≼□R∷ (⊑-≼-trans rest q)
⊑-≼-trans (⊑∷ ⊑□ rest) (≼□L∷ q) = ≼□L∷ (⊑-≼-trans rest q)

≼ₛ-weaken-⊔ₛᵣ : ∀ {Γ : Assms} (X A B : ⌊ Γ ⌋)
                → (X ⊔ₛ A) ≼ₛ B → A ≼ₛ B
≼ₛ-weaken-⊔ₛᵣ X A B h = ⊑-≼-trans (⊑ₛLat.y⊑ₛx⊔ₛy X A) h

≼ₛ-weaken-⊔ₛₗ : ∀ {Γ : Assms} (A X B : ⌊ Γ ⌋)
                → (A ⊔ₛ X) ≼ₛ B → A ≼ₛ B
≼ₛ-weaken-⊔ₛₗ A X B h = ⊑-≼-trans (⊑ₛLat.x⊑ₛx⊔ₛy A X) h
