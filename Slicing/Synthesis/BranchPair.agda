open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax) renaming (_×_ to _∧_)
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core
open import Semantics.Statics

module Slicing.Synthesis.BranchPair where

-- Head minimality local to the scrutinee's synthesis lattice
record IsCaseBranchPairMin
       {n : ℕ} {Γ : Assms} {e₀ e₁ e₂ : Exp}
       {τ τ₁ τ₂ τ₁' τ₂' : Typ}
       (D  : n ； Γ ⊢ e₀ ↦ τ)
       (m  : τ ⊔ □ + □ ≡ τ₁ + τ₂)
       (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
       (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
       (σ₀ : ⌊ e₀ ⌋) (σ₁ : ⌊ e₁ ⌋) (σ₂ : ⌊ e₂ ⌋)
       (υ  : ⌊ τ₁' ⊔ τ₂' ⌋)
       (ψ₀ : ⌊ τ ⌋) : Set where
  constructor mkHeadMin
  field
    head-min-witness
      : ∀ {σ₀' τ₀' τa τb τ-c₁ τ-c₂}
      → σ₀' ⊑ σ₀ .↓
      → n ； Γ ⊢ σ₀' ↦ τ₀'
      → τ₀' ⊔ □ + □ ≡ τa + τb
      → n ； (τa ∷ Γ) ⊢ σ₁ .↓ ↦ τ-c₁
      → n ； (τb ∷ Γ) ⊢ σ₂ .↓ ↦ τ-c₂
      → υ .↓ ⊑ τ-c₁ ⊔ τ-c₂
      → (τa ≡ (fst+ₛ' ψ₀ m) .↓) ∧ (τb ≡ (snd+ₛ' ψ₀ m) .↓)

open IsCaseBranchPairMin public

-- A minimal context for a case expression
record CaseCover {n : ℕ} {Γ : Assms} {e₀ e₁ e₂ : Exp}
                 {τ τ₁ τ₂ τ₁' τ₂' : Typ}
                 (D  : n ； Γ ⊢ e₀ ↦ τ)
                 (m  : τ ⊔ □ + □ ≡ τ₁ + τ₂)
                 (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
                 (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
                 (σ₀ : ⌊ e₀ ⌋) (σ₁ : ⌊ e₁ ⌋) (σ₂ : ⌊ e₂ ⌋)
                 (υ  : ⌊ τ₁' ⊔ τ₂' ⌋) : Set where
  field
    γ-out : ⌊ Γ ⌋
    τ-scr : Typ
    d-scr : n ； γ-out .↓ ⊢ σ₀ .↓ ↦ τ-scr
    τ-h₁  : Typ
    τ-h₂  : Typ
    m-h   : τ-scr ⊔ □ + □ ≡ τ-h₁ + τ-h₂
    τ-c₁  : Typ
    τ-c₂  : Typ
    d-br₁ : n ； (τ-h₁ ∷ γ-out .↓) ⊢ σ₁ .↓ ↦ τ-c₁
    d-br₂ : n ； (τ-h₂ ∷ γ-out .↓) ⊢ σ₂ .↓ ↦ τ-c₂
    valid : υ .↓ ⊑ τ-c₁ ⊔ τ-c₂

open CaseCover public

-- γ-out minimality for the entire case: any sub-context Γ' that admits a
-- covering case typing (scrutinee + branches at scrutinee's projection heads)
-- must extend γ-out.
IsMinCaseCover
  : ∀ {n : ℕ} {Γ : Assms} {e₀ e₁ e₂ : Exp} {τ τ₁ τ₂ τ₁' τ₂' : Typ}
      {D  : n ； Γ ⊢ e₀ ↦ τ}
      {m  : τ ⊔ □ + □ ≡ τ₁ + τ₂}
      {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'}
      {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
      {σ₀ : ⌊ e₀ ⌋} {σ₁ : ⌊ e₁ ⌋} {σ₂ : ⌊ e₂ ⌋}
      {υ : ⌊ τ₁' ⊔ τ₂' ⌋}
  → CaseCover D m D₁ D₂ σ₀ σ₁ σ₂ υ → Set
IsMinCaseCover {n = n} {Γ = Γ}
               {σ₀ = σ₀} {σ₁ = σ₁} {σ₂ = σ₂}
               {υ = υ} cov =
  ∀ {Γ' τ-scr' τ-h₁' τ-h₂' τ-c₁' τ-c₂'}
  → Γ' ⊑ Γ
  → n ； Γ' ⊢ σ₀ .↓ ↦ τ-scr'
  → τ-scr' ⊔ □ + □ ≡ τ-h₁' + τ-h₂'
  → n ； (τ-h₁' ∷ Γ') ⊢ σ₁ .↓ ↦ τ-c₁'
  → n ； (τ-h₂' ∷ Γ') ⊢ σ₂ .↓ ↦ τ-c₂'
  → υ .↓ ⊑ τ-c₁' ⊔ τ-c₂'
  → cov .γ-out .↓ ⊑ Γ'

MinCaseCover
  : ∀ {n : ℕ} {Γ : Assms} {e₀ e₁ e₂ : Exp} {τ τ₁ τ₂ τ₁' τ₂' : Typ}
  → (D  : n ； Γ ⊢ e₀ ↦ τ)
  → (m  : τ ⊔ □ + □ ≡ τ₁ + τ₂)
  → (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
  → (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
  → (σ₀ : ⌊ e₀ ⌋) → (σ₁ : ⌊ e₁ ⌋) → (σ₂ : ⌊ e₂ ⌋)
  → (υ  : ⌊ τ₁' ⊔ τ₂' ⌋)
  → Set
MinCaseCover D m D₁ D₂ σ₀ σ₁ σ₂ υ =
  Σ[ cov ∈ CaseCover D m D₁ D₂ σ₀ σ₁ σ₂ υ ] IsMinCaseCover cov

-- Existence of a minimal case cover
postulate
  min-case-cover
    : ∀ {n : ℕ} {Γ : Assms} {e₀ e₁ e₂ : Exp} {τ τ₁ τ₂ τ₁' τ₂' : Typ}
    → (D  : n ； Γ ⊢ e₀ ↦ τ)
    → (m  : τ ⊔ □ + □ ≡ τ₁ + τ₂)
    → (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
    → (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
    → (σ₀ : ⌊ e₀ ⌋) → (σ₁ : ⌊ e₁ ⌋) → (σ₂ : ⌊ e₂ ⌋)
    → (υ  : ⌊ τ₁' ⊔ τ₂' ⌋)
    → MinCaseCover D m D₁ D₂ σ₀ σ₁ σ₂ υ
