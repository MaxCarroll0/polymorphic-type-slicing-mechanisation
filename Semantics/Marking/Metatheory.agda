module Semantics.Marking.Metatheory where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (∃; Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core
open import Core.MExp
open import Semantics.Statics.Typing
open import Semantics.Marking.Judgment
open import Semantics.Marking.Erasure

-- Totality: every expression can be marked
postulate
  mark-total-syn : ∀ (n : ℕ) (Γ : Assms) (e : Exp) →
    ∃ λ ě → ∃ λ τ → n ； Γ ⊢ e ↬ ě ⇑ τ

  mark-total-ana : ∀ (n : ℕ) (Γ : Assms) (e : Exp) (τ : Typ) →
    ∃ λ ě → n ； Γ ⊢ e ↬ ě ⇓ τ

-- Unicity: marking is deterministic. Note: I'm not sure this will hold with my formalisation
postulate
  mark-unique-syn : ∀ {n Γ e ě₁ ě₂ τ₁ τ₂} →
    n ； Γ ⊢ e ↬ ě₁ ⇑ τ₁ →
    n ； Γ ⊢ e ↬ ě₂ ⇑ τ₂ →
    ě₁ ≡ ě₂ × τ₁ ≡ τ₂

  mark-unique-ana : ∀ {n Γ e ě₁ ě₂ τ} →
    n ； Γ ⊢ e ↬ ě₁ ⇓ τ →
    n ； Γ ⊢ e ↬ ě₂ ⇓ τ →
    ě₁ ≡ ě₂
