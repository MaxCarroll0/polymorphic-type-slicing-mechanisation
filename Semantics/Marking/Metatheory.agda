module Semantics.Marking.Metatheory where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (∃; Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Core
open import Core.MExp
open import Semantics.Statics.Typing
open import Semantics.Marking.Judgment
open import Semantics.Marking.Erasure

-- Well-formedness: erasure recovers original expression
mutual
  mark-wf-syn : ∀ {n Γ e ě τ} →
    n ； Γ ⊢ e ↬ ě ⇑ τ → erase ě ≡ e
  mark-wf-syn mark↦*                          = refl
  mark-wf-syn mark↦□                          = refl
  mark-wf-syn (mark↦Var _)                    = refl
  mark-wf-syn (mark↦Var⇑ _)                   = refl
  mark-wf-syn (mark↦λ: _ d)                   = cong (Exp.λ: _ ⇒_) (mark-wf-syn d)
  mark-wf-syn (mark↦Λ d)                      = cong Exp.Λ (mark-wf-syn d)
  mark-wf-syn (mark↦∘ d₁ _ d₂)                = cong₂ Exp._∘_ (mark-wf-syn d₁) (mark-wf-ana d₂)
  mark-wf-syn (mark↦∘⇑ d₁ _ d₂)               = cong₂ Exp._∘_ (mark-wf-syn d₁) (mark-wf-ana d₂)
  mark-wf-syn (mark↦<> d _ _)                 = cong (Exp._< _ >) (mark-wf-syn d)
  mark-wf-syn (mark↦<>⇑ d _ _)                = cong (Exp._< _ >) (mark-wf-syn d)
  mark-wf-syn (mark↦& d₁ d₂)                  = cong₂ Exp._&_ (mark-wf-syn d₁) (mark-wf-syn d₂)
  mark-wf-syn (mark↦def d₁ d₂)                = cong₂ (Exp.def_⊢_) (mark-wf-syn d₁) (mark-wf-syn d₂)
  mark-wf-syn (mark↦π₁ d _)                   = cong Exp.π₁ (mark-wf-syn d)
  mark-wf-syn (mark↦π₁⇑ d _)                  = cong Exp.π₁ (mark-wf-syn d)
  mark-wf-syn (mark↦π₂ d _)                   = cong Exp.π₂ (mark-wf-syn d)
  mark-wf-syn (mark↦π₂⇑ d _)                  = cong Exp.π₂ (mark-wf-syn d)
  mark-wf-syn (mark↦case d _ d₁ d₂ _)
    rewrite mark-wf-syn d | mark-wf-syn d₁ | mark-wf-syn d₂ = refl
  mark-wf-syn (mark↦case⇑ d _ d₁ d₂)
    rewrite mark-wf-syn d | mark-wf-syn d₁ | mark-wf-syn d₂ = refl

  mark-wf-ana : ∀ {n Γ e ě τ} →
    n ； Γ ⊢ e ↬ ě ⇓ τ → erase ě ≡ e
  mark-wf-ana (mark↤sub d _)                  = mark-wf-syn d
  mark-wf-ana (mark↤sub⇑ d _)                 = mark-wf-syn d
  mark-wf-ana (mark↤λ _ d)                    = cong Exp.λ⇒_ (mark-wf-ana d)
  mark-wf-ana (mark↤λ⇑ _ d)                   = cong Exp.λ⇒_ (mark-wf-ana d)
  mark-wf-ana (mark↤λ: _ _ _ d)               = cong (Exp.λ: _ ⇒_) (mark-wf-ana d)
  mark-wf-ana (mark↤ι₁ _ d)                   = cong Exp.ι₁ (mark-wf-ana d)
  mark-wf-ana (mark↤ι₂ _ d)                   = cong Exp.ι₂ (mark-wf-ana d)
  mark-wf-ana (mark↤& _ d₁ d₂)                = cong₂ Exp._&_ (mark-wf-ana d₁) (mark-wf-ana d₂)
  mark-wf-ana (mark↤def d₁ d₂)                = cong₂ (Exp.def_⊢_) (mark-wf-syn d₁) (mark-wf-ana d₂)
  mark-wf-ana (mark↤case d _ d₁ d₂)
    rewrite mark-wf-syn d | mark-wf-ana d₁ | mark-wf-ana d₂ = refl
  mark-wf-ana (mark↤case⇑ d _ d₁ d₂)
    rewrite mark-wf-syn d | mark-wf-ana d₁ | mark-wf-ana d₂ = refl

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
