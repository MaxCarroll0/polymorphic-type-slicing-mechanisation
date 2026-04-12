open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List using (_∷_)
open import Core
open import Semantics.Statics
open import Slicing.Synthesis using (SynSlice)
open import Slicing.SynSliceCalc using (MinSyn; unmatch⇒; unmatch+; unmatch×)
open import Slicing.Analysis

module Slicing.AnaSliceCalc where

-- Minimal analysis slice derivation.
-- Unlike MinSyn where the type slice decomposes through each rule,
-- here the type slice υ passes through unchanged — the CONTEXT slice
-- decomposes at each level.
data MinAna : ∀ {n Γ₀ C Γ τ p}
            → (Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]) → ⌊ τ ⌋ → Set where

  -- Synthesis position
  min□       : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]}
             → MinAna Cls ⊥ₛ

  minA○      : ∀ {n Γ τ}
             → (υ : ⌊ τ ⌋)
             → MinAna (a○ {n = n} {Γ = Γ} {τ = τ}) υ

  minASub    : ∀ {n Γ Γ' C τ₀ τ}
                 {Cls' : n ； Γ ⊢ C at synPos ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (aSub {τ = τ₀} Cls') υ

  minSλ:     : ∀ {n Γ Γ' τ₁ C τ}
                 {wf : n ⊢wf τ₁}
                 {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at synPos ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋} → (υ₁ : ⌊ τ₁ ⌋)
             → MinAna Cls' υ
             → MinAna (sλ: wf Cls') υ

  minS∘₁     : ∀ {n Γ Γ' C e τ}
                 {Cls' : n ； Γ ⊢ C at synPos ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (s∘₁ {e = e} Cls') υ

  -- Application argument: function's synthesis slice explains domain
  -- (THE KEY CASE)
  minS∘₂     : ∀ {n Γ Γ' e₁ C τ₀ τ₁ τ₂ τ}
                 {D₁ : n ； Γ ⊢ e₁ ↦ τ₀} {eq : τ₀ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                 {Cls' : n ； Γ ⊢ C at anaPos τ₁ ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋} → (υ₁ : ⌊ τ₁ ⌋)
             → MinSyn D₁ (unmatch⇒ eq υ₁ ⊥ₛ)
             → MinAna Cls' υ
             → MinAna (s∘₂ D₁ eq Cls') υ

  minS<>₁    : ∀ {n Γ Γ' C σ τ}
                 {Cls' : n ； Γ ⊢ C at synPos ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (s<>₁ {τ = σ} Cls') υ

  minS&₁     : ∀ {n Γ Γ' C e τ}
                 {Cls' : n ； Γ ⊢ C at synPos ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (s&₁ {e = e} Cls') υ

  minS&₂     : ∀ {n Γ Γ' C e τ}
                 {Cls' : n ； Γ ⊢ C at synPos ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (s&₂ {e = e} Cls') υ

  minScase₁  : ∀ {n Γ Γ' e C e' τ₀ τ₁ τ₂ τ}
                 {D : n ； Γ ⊢ e ↦ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                 {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at synPos ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋} → (υ₁ : ⌊ τ₁ ⌋)
             → MinSyn D (unmatch+ eq υ₁ ⊥ₛ)
             → MinAna Cls' υ
             → MinAna (scase₁ {e' = e'} D eq Cls') υ

  minScase₂  : ∀ {n Γ Γ' e e' C τ₀ τ₁ τ₂ τ}
                 {D : n ； Γ ⊢ e ↦ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                 {Cls' : n ； (τ₂ ∷ Γ) ⊢ C at synPos ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋} → (υ₂ : ⌊ τ₂ ⌋)
             → MinSyn D (unmatch+ eq ⊥ₛ υ₂)
             → MinAna Cls' υ
             → MinAna (scase₂ {e' = e'} D eq Cls') υ

  minSπ₁     : ∀ {n Γ Γ' C τ}
                 {Cls' : n ； Γ ⊢ C at synPos ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (sπ₁ Cls') υ

  minSπ₂     : ∀ {n Γ Γ' C τ}
                 {Cls' : n ； Γ ⊢ C at synPos ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (sπ₂ Cls') υ

  minSΛ      : ∀ {n Γ Γ' C τ}
                 {Cls' : suc n ； shiftΓ (suc zero) Γ ⊢ C at synPos ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (sΛ Cls') υ

  minSdef₁   : ∀ {n Γ Γ' C e τ}
                 {Cls' : n ； Γ ⊢ C at synPos ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋}
             → MinAna Cls' υ
             → MinAna (sdef₁ {e = e} Cls') υ

  minSdef₂   : ∀ {n Γ Γ' e C τ' τ}
                 {D : n ； Γ ⊢ e ↦ τ'}
                 {Cls' : n ； (τ' ∷ Γ) ⊢ C at synPos ▷ Γ' [ ⇐mode τ ]}
             → {υ : ⌊ τ ⌋} → (υ' : ⌊ τ' ⌋)
             → MinSyn D υ'
             → MinAna Cls' υ
             → MinAna (sdef₂ D Cls') υ

  -- Analysis position

  minAλ:     : ∀ {n Γ Γ' C τ τ₁ τ₂ τ'}
                 {c : τ ~ τ₁ ⇒ □} {eq : τ ⊔ τ₁ ⇒ □ ≡ τ₁ ⇒ τ₂}
                 {wf : n ⊢wf τ₁}
                 {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋} → (υ₁ : ⌊ τ₁ ⌋)
             → MinAna Cls' υ
             → MinAna (aλ: c eq wf Cls') υ

  minAλ⇒     : ∀ {n Γ Γ' C τ τ₁ τ₂ τ'}
                 {eq : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                 {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋}
             → MinAna Cls' υ
             → MinAna (aλ⇒ {τ = τ} eq Cls') υ

  minA&₁     : ∀ {n Γ Γ' C e τ τ₁ τ₂ τ'}
                 {eq : τ ⊔ □ × □ ≡ τ₁ × τ₂}
                 {Cls' : n ； Γ ⊢ C at anaPos τ₁ ▷ Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋}
             → MinAna Cls' υ
             → MinAna (a&₁ {e = e} {τ = τ} eq Cls') υ

  minA&₂     : ∀ {n Γ Γ' C e τ τ₁ τ₂ τ'}
                 {eq : τ ⊔ □ × □ ≡ τ₁ × τ₂}
                 {Cls' : n ； Γ ⊢ C at anaPos τ₂ ▷ Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋}
             → MinAna Cls' υ
             → MinAna (a&₂ {e = e} {τ = τ} eq Cls') υ

  minAι₁     : ∀ {n Γ Γ' C τ τ₁ τ₂ τ'}
                 {eq : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                 {Cls' : n ； Γ ⊢ C at anaPos τ₁ ▷ Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋}
             → MinAna Cls' υ
             → MinAna (aι₁ {τ = τ} eq Cls') υ

  minAι₂     : ∀ {n Γ Γ' C τ τ₁ τ₂ τ'}
                 {eq : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                 {Cls' : n ； Γ ⊢ C at anaPos τ₂ ▷ Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋}
             → MinAna Cls' υ
             → MinAna (aι₂ {τ = τ} eq Cls') υ

  minAcase₁  : ∀ {n Γ Γ' e C e' τ τ₀ τ₁ τ₂ τ'}
                 {D : n ； Γ ⊢ e ↦ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                 {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at anaPos τ ▷ Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋} → (υ₁ : ⌊ τ₁ ⌋)
             → MinSyn D (unmatch+ eq υ₁ ⊥ₛ)
             → MinAna Cls' υ
             → MinAna (acase₁ {e' = e'} D eq Cls') υ

  minAcase₂  : ∀ {n Γ Γ' e e' C τ τ₀ τ₁ τ₂ τ'}
                 {D : n ； Γ ⊢ e ↦ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                 {Cls' : n ； (τ₂ ∷ Γ) ⊢ C at anaPos τ ▷ Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋} → (υ₂ : ⌊ τ₂ ⌋)
             → MinSyn D (unmatch+ eq ⊥ₛ υ₂)
             → MinAna Cls' υ
             → MinAna (acase₂ {e' = e'} D eq Cls') υ

  minAdef₁   : ∀ {n Γ Γ' C e τ τ'}
                 {Cls' : n ； Γ ⊢ C at synPos ▷ Γ' [ ⇐mode τ' ]}
             → {υ : ⌊ τ' ⌋}
             → MinAna Cls' υ
             → MinAna (adef₁ {e = e} {τ = τ} Cls') υ

  minAdef₂   : ∀ {n Γ Γ' e C τ τ' τ''}
                 {D : n ； Γ ⊢ e ↦ τ'}
                 {Cls' : n ； (τ' ∷ Γ) ⊢ C at anaPos τ ▷ Γ' [ ⇐mode τ'' ]}
             → {υ : ⌊ τ'' ⌋} → (υ' : ⌊ τ' ⌋)
             → MinSyn D υ'
             → MinAna Cls' υ
             → MinAna (adef₂ D Cls') υ

-- Soundness: extract an AnaSlice from a MinAna
postulate
  extract : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ}
            → MinAna Cls υ → Σ[ m ∈ AnaSlice Cls υ ] IsMinimal m

-- Completeness: every minimal AnaSlice arises from some MinAna
  complete : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ}
             → (s : AnaSlice Cls υ) → IsMinimal s
             → Σ[ m ∈ MinAna Cls υ ] ((extract m) .proj₁) ≈ s
