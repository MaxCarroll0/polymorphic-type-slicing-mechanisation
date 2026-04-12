module Semantics.Metatheory where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (∃; Σ; _,_) renaming (_×_ to _∧_)
open import Core
open import Core.IntExp
open import Semantics.Statics.Typing
open import Semantics.Dynamics.Typing as IT
open import Semantics.Dynamics.Values
open import Semantics.Dynamics.EvalCtx
open import Semantics.Dynamics.Step
open import Semantics.Elaboration

-- Type Safety
postulate
  preservation : ∀ {n Γ d d' τ} →
    n IT.； Γ ⊢ d ∶ τ → d ↦ d' → n IT.； Γ ⊢ d' ∶ τ

  progress : ∀ {d τ} →
    zero IT.； [] ⊢ d ∶ τ → Final d ⊎ (∃ λ d' → d ↦ d')

-- Elaboration Soundness
postulate
  elab-sound-syn : ∀ {n Γ e τ d} →
    n ； Γ ⊢ e ⇑ τ ↝ d → n IT.； Γ ⊢ d ∶ τ

  elab-sound-ana : ∀ {n Γ e τ d} →
    n ； Γ ⊢ e ⇓ τ ↝ d → ∃ λ τ' → (n IT.； Γ ⊢ d ∶ τ')

-- Elaboration Completeness
postulate
  elab-complete-syn : ∀ {n Γ e τ} →
    n ； Γ ⊢ e ↦ τ → ∃ λ d → n ； Γ ⊢ e ⇑ τ ↝ d

  elab-complete-ana : ∀ {n Γ e τ} →
    n ； Γ ⊢ e ↤ τ → ∃ λ d → n ； Γ ⊢ e ⇓ τ ↝ d

-- Gradual Guarantee (synthesis)
-- Given a more precise derivation, a less precise one exists with less precise type
postulate
  static-gradual-syn : ∀ {n Γ₁ Γ₂ e₁ e₂ τ₂} →
    Γ₁ ⊑ Γ₂ → e₁ ⊑ e₂ →
    n ； Γ₂ ⊢ e₂ ↦ τ₂ →
    Σ Typ (λ τ₁ → (n ； Γ₁ ⊢ e₁ ↦ τ₁) ∧ (τ₁ ⊑ τ₂))

-- Synthesis precision: less precise terms synthesize less precise types
-- (follows from above via synthesis unicity)
postulate
  syn-precision : ∀ {n Γ₁ Γ₂ e₁ e₂ τ₁ τ₂} →
    Γ₁ ⊑ Γ₂ → e₁ ⊑ e₂ →
    n ； Γ₂ ⊢ e₂ ↦ τ₂ → n ； Γ₁ ⊢ e₁ ↦ τ₁ → τ₁ ⊑ τ₂

-- Analysis gradual guarantee:
-- all slices still analyse against any less (or equally) precise type
postulate
  static-gradual-ana : ∀ {n Γ₁ Γ₂ e₁ e₂ τ₁ τ₂} →
    Γ₁ ⊑ Γ₂ → e₁ ⊑ e₂ → τ₁ ⊑ τ₂ →
    n ； Γ₂ ⊢ e₂ ↤ τ₂ →
    n ； Γ₁ ⊢ e₁ ↤ τ₁
