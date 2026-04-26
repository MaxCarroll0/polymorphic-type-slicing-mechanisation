open import Data.Nat using (ℕ; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Core

module Slicing.MinSub where

-- Given a query on a substituted type [ zero ↦ σ ] τ', extract the
-- minimal slice of σ needed to explain the query through the substitution.
postulate
  min-sub : ∀ {τ' σ : Typ} → ⌊ [ zero ↦ σ ] τ' ⌋ → ⌊ σ ⌋

-- min-sub together with unsub explains the query:
-- the query is ⊑ the substitution of min-sub into unsub
postulate
  min-sub-valid : ∀ {τ' σ : Typ} (υ : ⌊ [ zero ↦ σ ] τ' ⌋)
    → υ ⊑ₛ subₛ {τ' = τ'} {σ = σ} (min-sub {τ'} {σ} υ) (unsub {τ'} {σ} υ)

-- min-sub is minimal: any other ϕ satisfying the above is ⊒ min-sub
postulate
  min-sub-minimal : ∀ {τ' σ : Typ} (υ : ⌊ [ zero ↦ σ ] τ' ⌋)
    (ϕ : ⌊ σ ⌋) (υ' : ⌊ τ' ⌋)
    → υ ⊑ₛ subₛ {τ' = τ'} {σ = σ} ϕ υ'
    → min-sub {τ'} {σ} υ ⊑ₛ ϕ

-- unsub preserves non-triviality
postulate
  unsub-non□ : ∀ {τ' σ : Typ} (υ : ⌊ [ zero ↦ σ ] τ' ⌋)
    → υ .↓ ≢ □
    → (unsub {τ'} {σ} υ) .↓ ≢ □

-- unsub body is below any ∀-body of a type ⊑ τ
postulate
  unsub-⊑-body : ∀ {τ' σ τ : Typ} (υ : ⌊ [ zero ↦ σ ] τ' ⌋)
    → ∀ {τ₃} → τ₃ ⊑ τ
    → ∀ {τ₃'} → τ₃ ⊔ ∀· □ ≡ ∀· τ₃'
    → (unsub {τ'} {σ} υ) .↓ ⊑ τ₃'
