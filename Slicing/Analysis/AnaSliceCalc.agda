open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List using (_∷_)
open import Core
open import Semantics.Statics
open import Slicing.Synthesis.Synthesis using (SynSlice_◂_)
open import Slicing.Synthesis.SynSliceCalc using (_⊢_◂_↦_⊣_)
open import Slicing.Analysis.Analysis

module Slicing.Analysis.AnaSliceCalc where

-- Minimal analysis slice derivation.
-- Unlike MinSyn where the type slice decomposes through each rule,
-- here the type slice υ passes through unchanged — the CONTEXT slice
-- decomposes at each level.
data MinAna : ∀ {n Γ₀ C n_f Γ τ p}
            → (Cls : n ； Γ₀ ⊢ C at p ▷ n_f ； Γ [ ⇐mode τ ]) → ⌊ τ ⌋ → Set where

  -- Bottom slice
  min□       : ∀ {n Γ₀ C n_f Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ n_f ； Γ [ ⇐mode τ ]}
             → MinAna Cls ⊥ₛ

  minA○      : ∀ {n Γ τ}
             → (υ : ⌊ τ ⌋)
             → MinAna (a○ {n = n} {Γ = Γ} {τ = τ}) υ

  -- Subsumption: now carries consistency witness
  minASub    : ∀ {n Γ n_f Γ' C τ₀ τ' τ}
                 {Cls' : n ； Γ ⊢ C at synPos τ' ▷ n_f ； Γ' [ ⇐mode τ ]}
                 {con : τ₀ ~ τ'}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (aSub {τ = τ₀} Cls' con) υ

  -- Synthesis position rules (enriched with sibling evidence)

  minSλ:     : ∀ {n Γ n_f Γ' τ₁ C τ₂ τ}
                 {wf : n ⊢wf τ₁}
                 {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at synPos τ₂ ▷ n_f ； Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋} → (υ₁ : ⌊ τ₁ ⌋)
             → MinAna Cls' υ
             → MinAna (sλ: wf Cls') υ

  minS∘₁     : ∀ {n Γ n_f Γ' C e τ_func τ₁ τ₂ τ}
                 {Cls' : n ； Γ ⊢ C at synPos τ_func ▷ n_f ； Γ' [ ⇐mode τ ]}
                 {eq : τ_func ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                 {d₂ : n ； Γ ⊢ e ↤ τ₁}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (s∘₁ Cls' eq d₂) υ

  -- Application argument: function's synthesis slice explains domain
  -- (THE KEY CASE)
  minS∘₂     : ∀ {n Γ n_f Γ' e₁ C τ₀ τ₁ τ₂ τ}
                 {D₁ : n ； Γ ⊢ e₁ ↦ τ₀} {eq : τ₀ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                 {Cls' : n ； Γ ⊢ C at anaPos τ₁ ▷ n_f ； Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋} → {Γᵢ : ⌊ Γ ⌋} {Φ : ⌊ Γ ⌋} {ψ : ⌊ τ₀ ⌋} → (υ₁ : ⌊ τ₁ ⌋)
             → Γᵢ ⊢ D₁ ◂ (unmatch⇒ eq υ₁ ⊥ₛ) ↦ ψ ⊣ Φ
             → MinAna Cls' υ
             → MinAna (s∘₂ D₁ eq Cls') υ

  minS<>₁    : ∀ {n Γ n_f Γ' C τ_inner τ_fa σ τ}
                 {Cls' : n ； Γ ⊢ C at synPos τ_inner ▷ n_f ； Γ' [ ⇐mode τ ]}
                 {eq : τ_inner ⊔ ∀· □ ≡ ∀· τ_fa}
                 {wf : n ⊢wf σ}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (s<>₁ Cls' eq wf) υ

  minS&₁     : ∀ {n Γ n_f Γ' C e τ₁ τ₂ τ}
                 {Cls' : n ； Γ ⊢ C at synPos τ₁ ▷ n_f ； Γ' [ ⇐mode τ ]}
                 {d₂ : n ； Γ ⊢ e ↦ τ₂}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (s&₁ Cls' d₂) υ

  minS&₂     : ∀ {n Γ n_f Γ' C e τ₁ τ₂ τ}
                 {d₁ : n ； Γ ⊢ e ↦ τ₁}
                 {Cls' : n ； Γ ⊢ C at synPos τ₂ ▷ n_f ； Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (s&₂ d₁ Cls') υ

  minScase₁  : ∀ {n Γ n_f Γ' e C e' τ₀ τ₁ τ₂ τ₁' τ₂' τ}
                 {D : n ； Γ ⊢ e ↦ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                 {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at synPos τ₁' ▷ n_f ； Γ' [ ⇐mode τ ]}
                 {d₂ : n ； (τ₂ ∷ Γ) ⊢ e' ↦ τ₂'}
                 {con : τ₁' ~ τ₂'}
             → {υ : ⌊ τ ⌋} → {Γᵢ : ⌊ Γ ⌋} {Φ : ⌊ Γ ⌋} {ψ : ⌊ τ₀ ⌋} → (υ₁ : ⌊ τ₁ ⌋)
             → Γᵢ ⊢ D ◂ (unmatch+ eq υ₁ ⊥ₛ) ↦ ψ ⊣ Φ
             → MinAna Cls' υ
             → MinAna (scase₁ D eq Cls' d₂ con) υ

  minScase₂  : ∀ {n Γ n_f Γ' e e' C τ₀ τ₁ τ₂ τ₁' τ₂' τ}
                 {D : n ； Γ ⊢ e ↦ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                 {d₁ : n ； (τ₁ ∷ Γ) ⊢ e' ↦ τ₁'}
                 {Cls' : n ； (τ₂ ∷ Γ) ⊢ C at synPos τ₂' ▷ n_f ； Γ' [ ⇐mode τ ]}
                 {con : τ₁' ~ τ₂'}
             → {υ : ⌊ τ ⌋} → {Γᵢ : ⌊ Γ ⌋} {Φ : ⌊ Γ ⌋} {ψ : ⌊ τ₀ ⌋} → (υ₂ : ⌊ τ₂ ⌋)
             → Γᵢ ⊢ D ◂ (unmatch+ eq ⊥ₛ υ₂) ↦ ψ ⊣ Φ
             → MinAna Cls' υ
             → MinAna (scase₂ D eq d₁ Cls' con) υ

  minSπ₁     : ∀ {n Γ n_f Γ' C τ_inner τ₁ τ₂ τ}
                 {Cls' : n ； Γ ⊢ C at synPos τ_inner ▷ n_f ； Γ' [ ⇐mode τ ]}
                 {eq : τ_inner ⊔ □ × □ ≡ τ₁ × τ₂}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (sπ₁ Cls' eq) υ

  minSπ₂     : ∀ {n Γ n_f Γ' C τ_inner τ₁ τ₂ τ}
                 {Cls' : n ； Γ ⊢ C at synPos τ_inner ▷ n_f ； Γ' [ ⇐mode τ ]}
                 {eq : τ_inner ⊔ □ × □ ≡ τ₁ × τ₂}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (sπ₂ Cls' eq) υ

  minSΛ      : ∀ {n Γ n_f Γ' C τ_body τ}
                 {Cls' : suc n ； shiftΓ (suc zero) Γ ⊢ C at synPos τ_body ▷ n_f ； Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (sΛ Cls') υ

  minSdef₁   : ∀ {n Γ n_f Γ' C e τ' τ_body τ}
                 {Cls' : n ； Γ ⊢ C at synPos τ' ▷ n_f ； Γ' [ ⇐mode τ ]}
                 {d₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ_body}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (sdef₁ Cls' d₂) υ

  minSdef₂   : ∀ {n Γ n_f Γ' e C τ' τ_body τ}
                 {D : n ； Γ ⊢ e ↦ τ'}
                 {Cls' : n ； (τ' ∷ Γ) ⊢ C at synPos τ_body ▷ n_f ； Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋} → {Γᵢ : ⌊ Γ ⌋} {Φ : ⌊ Γ ⌋} {ψ : ⌊ τ' ⌋} → (υ' : ⌊ τ' ⌋)
             → Γᵢ ⊢ D ◂ υ' ↦ ψ ⊣ Φ
             → MinAna Cls' υ
             → MinAna (sdef₂ D Cls') υ

  -- Analysis position rules (enriched with sibling evidence where needed)

  minAλ:     : ∀ {n Γ n_f Γ' C τ τ₁ τ₂ τ'}
                 {c : τ ~ τ₁ ⇒ □} {eq : τ ⊔ τ₁ ⇒ □ ≡ τ₁ ⇒ τ₂}
                 {wf : n ⊢wf τ₁}
                 {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ n_f ； Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋} → (υ₁ : ⌊ τ₁ ⌋)
             → MinAna Cls' υ
             → MinAna (aλ: c eq wf Cls') υ

  minAλ⇒     : ∀ {n Γ n_f Γ' C τ τ₁ τ₂ τ'}
                 {eq : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                 {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ n_f ； Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋}
             → MinAna Cls' υ
             → MinAna (aλ⇒ {τ = τ} eq Cls') υ

  minA&₁     : ∀ {n Γ n_f Γ' C e τ τ₁ τ₂ τf}
                 {eq : τ ⊔ □ × □ ≡ τ₁ × τ₂}
                 {Cls' : n ； Γ ⊢ C at anaPos τ₁ ▷ n_f ； Γ' [ ⇐mode τf ]}
                 {d₂ : n ； Γ ⊢ e ↤ τ₂}
             → {υ : ⌊ τf ⌋}
             → MinAna Cls' υ
             → MinAna (a&₁ {τ = τ} eq Cls' d₂) υ

  minA&₂     : ∀ {n Γ n_f Γ' C e τ τ₁ τ₂ τ'}
                 {eq : τ ⊔ □ × □ ≡ τ₁ × τ₂}
                 {d₁ : n ； Γ ⊢ e ↤ τ₁}
                 {Cls' : n ； Γ ⊢ C at anaPos τ₂ ▷ n_f ； Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋}
             → MinAna Cls' υ
             → MinAna (a&₂ {τ = τ} eq d₁ Cls') υ

  minAι₁     : ∀ {n Γ n_f Γ' C τ τ₁ τ₂ τ'}
                 {eq : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                 {Cls' : n ； Γ ⊢ C at anaPos τ₁ ▷ n_f ； Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋}
             → MinAna Cls' υ
             → MinAna (aι₁ {τ = τ} eq Cls') υ

  minAι₂     : ∀ {n Γ n_f Γ' C τ τ₁ τ₂ τ'}
                 {eq : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                 {Cls' : n ； Γ ⊢ C at anaPos τ₂ ▷ n_f ； Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋}
             → MinAna Cls' υ
             → MinAna (aι₂ {τ = τ} eq Cls') υ

  minAcase₁  : ∀ {n Γ n_f Γ' e C e' τ τ₀ τ₁ τ₂ τ'}
                 {D : n ； Γ ⊢ e ↦ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                 {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at anaPos τ ▷ n_f ； Γ' [ ⇐mode τ' ]}
                 {d₂ : n ； (τ₂ ∷ Γ) ⊢ e' ↤ τ}
             → {υ : ⌊ τ' ⌋} → {Γᵢ : ⌊ Γ ⌋} {Φ : ⌊ Γ ⌋} {ψ : ⌊ τ₀ ⌋} → (υ₁ : ⌊ τ₁ ⌋)
             → Γᵢ ⊢ D ◂ (unmatch+ eq υ₁ ⊥ₛ) ↦ ψ ⊣ Φ
             → MinAna Cls' υ
             → MinAna (acase₁ D eq Cls' d₂) υ

  minAcase₂  : ∀ {n Γ n_f Γ' e e' C τ τ₀ τ₁ τ₂ τ'}
                 {D : n ； Γ ⊢ e ↦ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                 {d₁ : n ； (τ₁ ∷ Γ) ⊢ e' ↤ τ}
                 {Cls' : n ； (τ₂ ∷ Γ) ⊢ C at anaPos τ ▷ n_f ； Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋} → {Γᵢ : ⌊ Γ ⌋} {Φ : ⌊ Γ ⌋} {ψ : ⌊ τ₀ ⌋} → (υ₂ : ⌊ τ₂ ⌋)
             → Γᵢ ⊢ D ◂ (unmatch+ eq ⊥ₛ υ₂) ↦ ψ ⊣ Φ
             → MinAna Cls' υ
             → MinAna (acase₂ D eq d₁ Cls') υ

  minAdef₁   : ∀ {n Γ n_f Γ' C e τ τ' τ''}
                 {Cls' : n ； Γ ⊢ C at synPos τ' ▷ n_f ； Γ' [ ⇐mode τ'' ]}
                 {d₂ : n ； (τ' ∷ Γ) ⊢ e ↤ τ}
             → {υ : ⌊ τ'' ⌋}
             → MinAna Cls' υ
             → MinAna (adef₁ Cls' d₂) υ

  minAdef₂   : ∀ {n Γ n_f Γ' e C τ τ' τ''}
                 {D : n ； Γ ⊢ e ↦ τ'}
                 {Cls' : n ； (τ' ∷ Γ) ⊢ C at anaPos τ ▷ n_f ； Γ' [ ⇐mode τ'' ]}
             → {υ : ⌊ τ'' ⌋} → {Γᵢ : ⌊ Γ ⌋} {Φ : ⌊ Γ ⌋} {ψ : ⌊ τ' ⌋} → (υ' : ⌊ τ' ⌋)
             → Γᵢ ⊢ D ◂ υ' ↦ ψ ⊣ Φ
             → MinAna Cls' υ
             → MinAna (adef₂ D Cls') υ

-- Soundness: extract an AnaSlice from a MinAna
postulate
  extract : ∀ {n Γ₀ C n_f Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ n_f ； Γ [ ⇐mode τ ]} {υ}
            → MinAna Cls υ → Σ[ m ∈ AnaSlice Cls υ ] IsMinimal m

-- Completeness: every minimal AnaSlice arises from some MinAna
  complete : ∀ {n Γ₀ C n_f Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ n_f ； Γ [ ⇐mode τ ]} {υ}
             → (s : AnaSlice Cls υ) → IsMinimal s
             → Σ[ m ∈ MinAna Cls υ ] ((extract m) .proj₁) ≈ s
