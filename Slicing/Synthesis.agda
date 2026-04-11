open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (Σ-syntax; _,_) renaming (_×_ to _∧_)
open import Core
open import Semantics.Statics

module Slicing.Synthesis where

-- Synthesis slice: slice assums and exp while still synthesising
-- a given type slice υ. Indexed by the original derivation D.
record SynSlice {n : ℕ} {Γ : Assms} {e : Exp} {τ : Typ}
                (D : n ； Γ ⊢ e ↦ τ) (υ : ⌊ τ ⌋) : Set where
  field
    γ     : ⌊ Γ ⌋
    σ     : ⌊ e ⌋
    valid : n ； γ .↓ ⊢ σ .↓ ↦ υ .↓

_⊑syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
            SynSlice D υ → SynSlice D υ → Set
s₁ ⊑syn s₂ = (SynSlice.σ s₁ ⊑ₛ SynSlice.σ s₂)
            ∧ (SynSlice.γ s₁ ⊑ₛ SynSlice.γ s₂)

⊥-syn : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} → SynSlice D ⊥ₛ
⊥-syn = record { γ = ⊥ₛ ; σ = ⊥ₛ ; valid = ↦□ }

⊤-syn : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) → SynSlice D ⊤ₛ
⊤-syn D = record { γ = ⊤ₛ ; σ = ⊤ₛ ; valid = D }

-- Join closure: the join of two SynSlices for the same υ is a SynSlice
postulate
  ⊔syn-valid : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
               → (s₁ s₂ : SynSlice D υ)
               → n ； (SynSlice.γ s₁ ⊔ₛ SynSlice.γ s₂) .↓
                   ⊢ (SynSlice.σ s₁ ⊔ₛ SynSlice.σ s₂) .↓ ↦ υ .↓

_⊔syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
            SynSlice D υ → SynSlice D υ → SynSlice D υ
s₁ ⊔syn s₂ = record
  { γ = SynSlice.γ s₁ ⊔ₛ SynSlice.γ s₂
  ; σ = SynSlice.σ s₁ ⊔ₛ SynSlice.σ s₂
  ; valid = ⊔syn-valid s₁ s₂
  }

-- Join-semilattice properties
⊔syn-ub₁ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → (s₁ s₂ : SynSlice D υ) → s₁ ⊑syn (s₁ ⊔syn s₂)
⊔syn-ub₁ s₁ s₂ = ⊑ₛLat.x⊑ₛx⊔ₛy (SynSlice.σ s₁) (SynSlice.σ s₂)
                , ⊑ₛLat.x⊑ₛx⊔ₛy (SynSlice.γ s₁) (SynSlice.γ s₂)

⊔syn-ub₂ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → (s₁ s₂ : SynSlice D υ) → s₂ ⊑syn (s₁ ⊔syn s₂)
⊔syn-ub₂ s₁ s₂ = ⊑ₛLat.y⊑ₛx⊔ₛy (SynSlice.σ s₁) (SynSlice.σ s₂)
                , ⊑ₛLat.y⊑ₛx⊔ₛy (SynSlice.γ s₁) (SynSlice.γ s₂)

⊔syn-lub : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → (s s₁ s₂ : SynSlice D υ)
            → s₁ ⊑syn s → s₂ ⊑syn s
            → (s₁ ⊔syn s₂) ⊑syn s
⊔syn-lub {Γ = Γ} {e = e} s s₁ s₂ (p₁ , q₁) (p₂ , q₂) =
    ⊑ₛLat.⊔ₛ-least {A = Exp} {a = e}
      {x = SynSlice.σ s₁} {y = SynSlice.σ s₂} {z = SynSlice.σ s}
      p₁ p₂
  , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ}
      {x = SynSlice.γ s₁} {y = SynSlice.γ s₂} {z = SynSlice.γ s}
      q₁ q₂

-- Minimality
IsMinimal : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} → SynSlice D υ → Set
IsMinimal s = ∀ s' → s' ⊑syn s → s ⊑syn s'

postulate
  minExists : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) υ
             → Σ[ m ∈ SynSlice D υ ] IsMinimal m

_⊑extract_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂} →
               SynSlice D υ₁ → SynSlice D υ₂ → Set
s₁ ⊑extract s₂ = (SynSlice.σ s₁ ⊑ₛ SynSlice.σ s₂)
               ∧ (SynSlice.γ s₁ ⊑ₛ SynSlice.γ s₂)
               
-- Monotonicity: more precise type slice → more precise minimal slice
postulate
  mono : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂ : ⌊ τ ⌋}
         → υ₁ ⊑ₛ υ₂
         → (m₂ : SynSlice D υ₂) → IsMinimal m₂
         → Σ[ m₁ ∈ SynSlice D υ₁ ] IsMinimal m₁ ∧ m₁ ⊑extract m₂
