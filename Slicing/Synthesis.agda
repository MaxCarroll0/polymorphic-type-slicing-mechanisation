open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsEquivalence; IsDecEquivalence)
open import Relation.Binary.Lattice using (IsJoinSemilattice)
open import Core
open import Semantics.Statics

module Slicing.Synthesis where

-- Synthesis slice: sliced assumptions and expression that still synthesize
-- a given type slice υ. Indexed by the original derivation D.
record SynSlice {n : ℕ} {Γ : Assms} {e : Exp} {τ : Typ}
                (D : n ； Γ ⊢ e ↦ τ) (υ : ⌊ τ ⌋) : Set where
  field
    γ     : ⌊ Γ ⌋
    σ     : ⌊ e ⌋
    valid : n ； γ .↓ ⊢ σ .↓ ↦ υ .↓

private
-- Precision polymorphic in υ
  _⊑syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂} →
             SynSlice D υ₁ → SynSlice D υ₂ → Set
  s₁ ⊑syn s₂ = (SynSlice.σ s₁ ⊑ₛ SynSlice.σ s₂)
             ∧ (SynSlice.γ s₁ ⊑ₛ SynSlice.γ s₂)

  _≈syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂} →
              SynSlice D υ₁ → SynSlice D υ₂ → Set
  s₁ ≈syn s₂ = (SynSlice.σ s₁ ≈ₛ SynSlice.σ s₂)
             ∧ (SynSlice.γ s₁ ≈ₛ SynSlice.γ s₂)

  postulate
    ⊑syn-isDecPartialOrder : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
                                IsDecPartialOrder (_≈syn_ {D = D} {υ₁ = υ} {υ₂ = υ})
                                                  _⊑syn_

⊥-syn : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} → SynSlice D ⊥ₛ
⊥-syn = record { γ = ⊥ₛ ; σ = ⊥ₛ ; valid = ↦□ }

⊤-syn : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) → SynSlice D ⊤ₛ
⊤-syn D = record { γ = ⊤ₛ ; σ = ⊤ₛ ; valid = D }

-- Join closure
private 
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
              → {s : SynSlice D υ} (s₁ s₂ : SynSlice D υ)
              → s₁ ⊑syn s → s₂ ⊑syn s
              → (s₁ ⊔syn s₂) ⊑syn s
  ⊔syn-lub {Γ = Γ} {e = e} {s = s} s₁ s₂ (p₁ , q₁) (p₂ , q₂) =
      ⊑ₛLat.⊔ₛ-least {A = Exp} {a = e}
        {x = SynSlice.σ s₁} {y = SynSlice.σ s₂} {z = SynSlice.σ s}
        p₁ p₂
    , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ}
        {x = SynSlice.γ s₁} {y = SynSlice.γ s₂} {z = SynSlice.γ s}
        q₁ q₂

  ⊔syn-isJoinSemilattice : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
                              IsJoinSemilattice (_≈syn_ {D = D} {υ₁ = υ} {υ₂ = υ})
                                                _⊑syn_
                                                _⊔syn_
  ⊔syn-isJoinSemilattice = record
    { isPartialOrder = IsDecPartialOrder.isPartialOrder ⊑syn-isDecPartialOrder
    ; supremum       = λ s₁ s₂ → ⊔syn-ub₁ s₁ s₂ , ⊔syn-ub₂ s₁ s₂ , λ s → ⊔syn-lub {s = s} s₁ s₂
    }

instance
  synSlice-precision : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
                         HasPrecision (SynSlice D υ)
  synSlice-precision = record
    { _≈_               = _≈syn_
    ; _⊑_               = _⊑syn_
    ; isDecPartialOrder = ⊑syn-isDecPartialOrder
    }

  synSlice-join : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
                    HasJoin (SynSlice D υ)
  synSlice-join = record
    { _⊔_     = _⊔syn_
    ; closure = λ {s₁} {s₂} {s} p q → ⊔syn-lub {s = s} s₁ s₂ p q
    }

  synSlice-joinSemilattice : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
                               HasJoinSemilattice (SynSlice D υ)
  synSlice-joinSemilattice = record { isJoinSemilattice = ⊔syn-isJoinSemilattice }

-- Minimality
IsMinimal : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} → SynSlice D υ → Set
IsMinimal {D = D} {υ = υ} s = ∀ (s' : SynSlice D υ) → s' ⊑syn s → s ⊑syn s'

-- Every derivation and type slice has a minimal SynSlice
postulate
  minExists : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) υ
             → ∃[ m ] IsMinimal {D = D} {υ = υ} m

-- Monotonicity: more precise type slice → more precise minimal slice
postulate
  mono : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂ : ⌊ τ ⌋}
         → υ₁ ⊑ₛ υ₂
         → (m₂ : SynSlice D υ₂) → IsMinimal m₂
         → Σ[ m₁ ∈ SynSlice D υ₁ ] IsMinimal m₁ ∧ m₁ ⊑syn m₂
