open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax) renaming (_×_ to _∧_)
open import Data.Sum using (_⊎_)
open import Data.List using (_∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core
open import Semantics.Statics

module Slicing.Synthesis.BranchPair where

-- Pointwise head minimality at (ς₁, ς₂)
record IsCaseBranchPairMin
       {n : ℕ} {Γ : Assms} {e₁ e₂ : Exp} {τ₁ τ₂ τ₁' τ₂' : Typ}
       (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
       (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
       (σ₁ : ⌊ e₁ ⌋) (σ₂ : ⌊ e₂ ⌋)
       (υ : ⌊ τ₁' ⊔ τ₂' ⌋)
       (ς₁ : ⌊ τ₁ ⌋) (ς₂ : ⌊ τ₂ ⌋) : Set where
  constructor mkHeadMin
  field
    head-min-witness
      : ∀ {τa τb τ-c1 τ-c2}
      → τa ⊑ ς₁ .↓ → τb ⊑ ς₂ .↓
      → n ； (τa ∷ Γ) ⊢ σ₁ .↓ ↦ τ-c1
      → n ； (τb ∷ Γ) ⊢ σ₂ .↓ ↦ τ-c2
      → υ .↓ ⊑ τ-c1 ⊔ τ-c2
      → (τa ≡ ς₁ .↓) ∧ (τb ≡ ς₂ .↓)

open IsCaseBranchPairMin public

-- a Γ-tail γ together with branch typings of σ₁, σ₂ at
-- fixed heads (ς₁, ς₂) over γ, whose synthesised type covers υ
record BranchPairCover {n : ℕ} {Γ : Assms} {e₁ e₂ : Exp}
                       {τ₁ τ₂ τ₁' τ₂' : Typ}
                       (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
                       (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
                       (σ₁ : ⌊ e₁ ⌋) (σ₂ : ⌊ e₂ ⌋)
                       (ς₁ : ⌊ τ₁ ⌋) (ς₂ : ⌊ τ₂ ⌋)
                       (υ : ⌊ τ₁' ⊔ τ₂' ⌋) : Set where
  field
    γ-tail : ⌊ Γ ⌋
    τ-c1   : Typ
    τ-c2   : Typ
    syn₁   : n ； (ς₁ .↓ ∷ γ-tail .↓) ⊢ σ₁ .↓ ↦ τ-c1
    syn₂   : n ； (ς₂ .↓ ∷ γ-tail .↓) ⊢ σ₂ .↓ ↦ τ-c2
    valid  : υ .↓ ⊑ τ-c1 ⊔ τ-c2

open BranchPairCover public

-- γ-tail minimality at the cover's fixed heads (ς₁, ς₂)
IsMinBranchPairCover
  : ∀ {n : ℕ} {Γ : Assms} {e₁ e₂ : Exp} {τ₁ τ₂ τ₁' τ₂' : Typ}
      {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'}
      {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
      {σ₁ : ⌊ e₁ ⌋} {σ₂ : ⌊ e₂ ⌋}
      {ς₁ : ⌊ τ₁ ⌋} {ς₂ : ⌊ τ₂ ⌋}
      {υ : ⌊ τ₁' ⊔ τ₂' ⌋}
  → BranchPairCover D₁ D₂ σ₁ σ₂ ς₁ ς₂ υ → Set
IsMinBranchPairCover {n = n} {Γ = Γ}
                     {σ₁ = σ₁} {σ₂ = σ₂}
                     {ς₁ = ς₁} {ς₂ = ς₂}
                     {υ = υ} cov =
  ∀ {Γ' τ-c1' τ-c2'}
  → Γ' ⊑ Γ
  → n ； (ς₁ .↓ ∷ Γ') ⊢ σ₁ .↓ ↦ τ-c1'
  → n ； (ς₂ .↓ ∷ Γ') ⊢ σ₂ .↓ ↦ τ-c2'
  → υ .↓ ⊑ τ-c1' ⊔ τ-c2'
  → cov .γ-tail .↓ ⊑ Γ'

-- A minimal branch-pair cover
MinBranchPairCover
  : ∀ {n : ℕ} {Γ : Assms} {e₁ e₂ : Exp} {τ₁ τ₂ τ₁' τ₂' : Typ}
  → (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
  → (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
  → (σ₁ : ⌊ e₁ ⌋) → (σ₂ : ⌊ e₂ ⌋)
  → (ς₁ : ⌊ τ₁ ⌋) → (ς₂ : ⌊ τ₂ ⌋)
  → (υ : ⌊ τ₁' ⊔ τ₂' ⌋)
  → Set
MinBranchPairCover D₁ D₂ σ₁ σ₂ ς₁ ς₂ υ =
  Σ[ cov ∈ BranchPairCover D₁ D₂ σ₁ σ₂ ς₁ ς₂ υ ] IsMinBranchPairCover cov

-- Existence of a minimal branch-pair cover
postulate
  min-branch-pair-cover
    : ∀ {n : ℕ} {Γ : Assms} {e₁ e₂ : Exp} {τ₁ τ₂ τ₁' τ₂' : Typ}
    → (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
    → (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
    → (σ₁ : ⌊ e₁ ⌋) → (σ₂ : ⌊ e₂ ⌋)
    → (ς₁ : ⌊ τ₁ ⌋) → (ς₂ : ⌊ τ₂ ⌋)
    → (γ₁ : ⌊ τ₁ ∷ Γ ⌋) → (γ₂ : ⌊ τ₂ ∷ Γ ⌋)
    → (υ : ⌊ τ₁' ⊔ τ₂' ⌋)
    → MinBranchPairCover D₁ D₂ σ₁ σ₂ ς₁ ς₂ υ

