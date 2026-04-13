module Semantics.Marking.Judgment where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)
open import Core
open import Core.MExp
open import Semantics.Statics.Typing using (_；_⊢_↦_; _；_⊢_↤_)

mutual
  -- Synthesis marking: n ； Γ ⊢ e ↬ ě ⇑ τ
  infix 4 _；_⊢_↬_⇑_

  data _；_⊢_↬_⇑_ : ℕ → Assms → Exp → MExp → Typ → Set where
    mark↦*     : ∀ {n Γ} →
                   n ； Γ ⊢ * ↬ * ⇑ *

    mark↦□     : ∀ {n Γ} →
                   n ； Γ ⊢ □ ↬ □ ⇑ □

    mark↦Var   : ∀ {n Γ k τ} →
                   Γ at k ≡ just τ →
                   n ； Γ ⊢ ⟨ k ⟩ ↬ ⟨ k ⟩ ⇑ τ

    mark↦Var⇑  : ∀ {n Γ k} →
                   Γ at k ≡ nothing →
                   n ； Γ ⊢ ⟨ k ⟩ ↬ ⟨ k ⟩⇑ ⇑ □

    mark↦λ:    : ∀ {n Γ e ě τ₁ τ₂} →
                   n ⊢wf τ₁ →
                   n ； (τ₁ ∷ Γ) ⊢ e ↬ ě ⇑ τ₂ →
                   n ； Γ ⊢ λ: τ₁ ⇒ e ↬ λ: τ₁ ⇒ ě ⇑ τ₁ ⇒ τ₂

    mark↦Λ     : ∀ {n Γ e ě τ} →
                   suc n ； shiftΓ (suc zero) Γ ⊢ e ↬ ě ⇑ τ →
                   n ； Γ ⊢ Λ e ↬ Λ ě ⇑ ∀· τ

    mark↦∘     : ∀ {n Γ e₁ e₂ ě₁ ě₂ τ τ₁ τ₂} →
                   n ； Γ ⊢ e₁ ↬ ě₁ ⇑ τ →
                   τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂ →
                   n ； Γ ⊢ e₂ ↬ ě₂ ⇓ τ₁ →
                   n ； Γ ⊢ e₁ ∘ e₂ ↬ ě₁ ∘ ě₂ ⇑ τ₂

    mark↦∘⇑    : ∀ {n Γ e₁ e₂ ě₁ ě₂ τ} →
                   n ； Γ ⊢ e₁ ↬ ě₁ ⇑ τ →
                   (∀ {τ₁ τ₂} → τ ⊔ □ ⇒ □ ≢ τ₁ ⇒ τ₂) →
                   n ； Γ ⊢ e₂ ↬ ě₂ ⇓ □ →
                   n ； Γ ⊢ e₁ ∘ e₂ ↬ (ě₁ ⦅▸⇒⦆) ∘ ě₂ ⇑ □

    mark↦<>    : ∀ {n Γ e ě τ τ' σ} →
                   n ； Γ ⊢ e ↬ ě ⇑ τ →
                   τ ⊔ ∀· □ ≡ ∀· τ' →
                   n ⊢wf σ →
                   n ； Γ ⊢ e < σ > ↬ ě < σ > ⇑ [ zero ↦ σ ] τ'

    mark↦<>⇑   : ∀ {n Γ e ě τ σ} →
                   n ； Γ ⊢ e ↬ ě ⇑ τ →
                   (∀ {τ'} → τ ⊔ ∀· □ ≢ ∀· τ') →
                   n ⊢wf σ →
                   n ； Γ ⊢ e < σ > ↬ (ě ⦅▸∀⦆) < σ > ⇑ □

    mark↦&     : ∀ {n Γ e₁ e₂ ě₁ ě₂ τ₁ τ₂} →
                   n ； Γ ⊢ e₁ ↬ ě₁ ⇑ τ₁ →
                   n ； Γ ⊢ e₂ ↬ ě₂ ⇑ τ₂ →
                   n ； Γ ⊢ e₁ & e₂ ↬ ě₁ & ě₂ ⇑ τ₁ × τ₂

    mark↦def   : ∀ {n Γ e' e ě' ě τ' τ} →
                   n ； Γ ⊢ e' ↬ ě' ⇑ τ' →
                   n ； (τ' ∷ Γ) ⊢ e ↬ ě ⇑ τ →
                   n ； Γ ⊢ def e' ⊢ e ↬ def ě' ⊢ ě ⇑ τ

    mark↦π₁    : ∀ {n Γ e ě τ τ₁ τ₂} →
                   n ； Γ ⊢ e ↬ ě ⇑ τ →
                   τ ⊔ □ × □ ≡ τ₁ × τ₂ →
                   n ； Γ ⊢ π₁ e ↬ π₁ ě ⇑ τ₁

    mark↦π₁⇑   : ∀ {n Γ e ě τ} →
                   n ； Γ ⊢ e ↬ ě ⇑ τ →
                   (∀ {τ₁ τ₂} → τ ⊔ □ × □ ≢ τ₁ × τ₂) →
                   n ； Γ ⊢ π₁ e ↬ π₁ (ě ⦅▸×⦆) ⇑ □

    mark↦π₂    : ∀ {n Γ e ě τ τ₁ τ₂} →
                   n ； Γ ⊢ e ↬ ě ⇑ τ →
                   τ ⊔ □ × □ ≡ τ₁ × τ₂ →
                   n ； Γ ⊢ π₂ e ↬ π₂ ě ⇑ τ₂

    mark↦π₂⇑   : ∀ {n Γ e ě τ} →
                   n ； Γ ⊢ e ↬ ě ⇑ τ →
                   (∀ {τ₁ τ₂} → τ ⊔ □ × □ ≢ τ₁ × τ₂) →
                   n ； Γ ⊢ π₂ e ↬ π₂ (ě ⦅▸×⦆) ⇑ □

    mark↦case  : ∀ {n Γ e e₁ e₂ ě ě₁ ě₂ τ τ₁ τ₂ τ₁' τ₂'} →
                   n ； Γ ⊢ e ↬ ě ⇑ τ →
                   τ ⊔ □ + □ ≡ τ₁ + τ₂ →
                   n ； (τ₁ ∷ Γ) ⊢ e₁ ↬ ě₁ ⇑ τ₁' →
                   n ； (τ₂ ∷ Γ) ⊢ e₂ ↬ ě₂ ⇑ τ₂' →
                   τ₁' ~ τ₂' →
                   n ； Γ ⊢ case e of e₁ · e₂ ↬ case ě of ě₁ · ě₂ ⇑ τ₁' ⊔ τ₂'

    mark↦case⇑ : ∀ {n Γ e e₁ e₂ ě ě₁ ě₂ τ τ₁' τ₂'} →
                   n ； Γ ⊢ e ↬ ě ⇑ τ →
                   (∀ {τ₁ τ₂} → τ ⊔ □ + □ ≢ τ₁ + τ₂) →
                   n ； Γ ⊢ e₁ ↬ ě₁ ⇑ τ₁' →
                   n ； Γ ⊢ e₂ ↬ ě₂ ⇑ τ₂' →
                   n ； Γ ⊢ case e of e₁ · e₂ ↬ case (ě ⦅▸+⦆) of ě₁ · ě₂ ⇑ □

    -- Synthesis case with matched sum but inconsistent branch types
    mark↦case≁ : ∀ {n Γ e e₁ e₂ ě ě₁ ě₂ τ τ₁ τ₂ τ₁' τ₂'} →
                   n ； Γ ⊢ e ↬ ě ⇑ τ →
                   τ ⊔ □ + □ ≡ τ₁ + τ₂ →
                   n ； (τ₁ ∷ Γ) ⊢ e₁ ↬ ě₁ ⇑ τ₁' →
                   n ； (τ₂ ∷ Γ) ⊢ e₂ ↬ ě₂ ⇑ τ₂' →
                   ¬ (τ₁' ~ τ₂') →
                   n ； Γ ⊢ case e of e₁ · e₂ ↬ case ě of ě₁ · ě₂ ⇑ □

    -- Analysis-only forms in synthesis position
    mark↦λ⇒   : ∀ {n Γ e ě} →
                   n ； Γ ⊢ e ↬ ě ⇓ □ →
                   n ； Γ ⊢ λ⇒ e ↬ (λ⇒ ě) ⦅~⇒⦆ ⇑ □

    mark↦ι₁    : ∀ {n Γ e ě} →
                   n ； Γ ⊢ e ↬ ě ⇓ □ →
                   n ； Γ ⊢ ι₁ e ↬ (ι₁ ě) ⦅~+⦆ ⇑ □

    mark↦ι₂    : ∀ {n Γ e ě} →
                   n ； Γ ⊢ e ↬ ě ⇓ □ →
                   n ； Γ ⊢ ι₂ e ↬ (ι₂ ě) ⦅~+⦆ ⇑ □

  -- Analysis marking: n ； Γ ⊢ e ↬ ě ⇓ τ
  infix 4 _；_⊢_↬_⇓_

  data _；_⊢_↬_⇓_ : ℕ → Assms → Exp → MExp → Typ → Set where
    mark↤sub   : ∀ {n Γ e ě τ τ'} →
                   n ； Γ ⊢ e ↬ ě ⇑ τ' →
                   τ ~ τ' →
                   n ； Γ ⊢ e ↬ ě ⇓ τ

    mark↤sub⇑  : ∀ {n Γ e ě τ τ'} →
                   n ； Γ ⊢ e ↬ ě ⇑ τ' →
                   ¬ (τ ~ τ') →
                   n ； Γ ⊢ e ↬ ě ⦅≁ τ ⦆ ⇓ τ

    mark↤λ     : ∀ {n Γ e ě τ τ₁ τ₂} →
                   τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂ →
                   n ； (τ₁ ∷ Γ) ⊢ e ↬ ě ⇓ τ₂ →
                   n ； Γ ⊢ λ⇒ e ↬ λ⇒ ě ⇓ τ

    mark↤λ⇑    : ∀ {n Γ e ě τ} →
                   (∀ {τ₁ τ₂} → τ ⊔ □ ⇒ □ ≢ τ₁ ⇒ τ₂) →
                   n ； Γ ⊢ e ↬ ě ⇓ □ →
                   n ； Γ ⊢ λ⇒ e ↬ (λ⇒ ě) ⦅~⇒⦆ ⇓ τ

    mark↤λ:    : ∀ {n Γ e ě τ τ₁ τ₂} →
                   τ ⊔ τ₁ ⇒ □ ≡ τ₁ ⇒ τ₂ →
                   n ⊢wf τ₁ →
                   n ； (τ₁ ∷ Γ) ⊢ e ↬ ě ⇓ τ₂ →
                   n ； Γ ⊢ λ: τ₁ ⇒ e ↬ λ: τ₁ ⇒ ě ⇓ τ

    mark↤ι₁    : ∀ {n Γ e ě τ τ₁ τ₂} →
                   τ ⊔ □ + □ ≡ τ₁ + τ₂ →
                   n ； Γ ⊢ e ↬ ě ⇓ τ₁ →
                   n ； Γ ⊢ ι₁ e ↬ ι₁ ě ⇓ τ

    mark↤ι₂    : ∀ {n Γ e ě τ τ₁ τ₂} →
                   τ ⊔ □ + □ ≡ τ₁ + τ₂ →
                   n ； Γ ⊢ e ↬ ě ⇓ τ₂ →
                   n ； Γ ⊢ ι₂ e ↬ ι₂ ě ⇓ τ

    mark↤&     : ∀ {n Γ e₁ e₂ ě₁ ě₂ τ τ₁ τ₂} →
                   τ ⊔ □ × □ ≡ τ₁ × τ₂ →
                   n ； Γ ⊢ e₁ ↬ ě₁ ⇓ τ₁ →
                   n ； Γ ⊢ e₂ ↬ ě₂ ⇓ τ₂ →
                   n ； Γ ⊢ e₁ & e₂ ↬ ě₁ & ě₂ ⇓ τ

    mark↤def   : ∀ {n Γ e' e ě' ě τ' τ} →
                   n ； Γ ⊢ e' ↬ ě' ⇑ τ' →
                   n ； (τ' ∷ Γ) ⊢ e ↬ ě ⇓ τ →
                   n ； Γ ⊢ def e' ⊢ e ↬ def ě' ⊢ ě ⇓ τ

    mark↤case  : ∀ {n Γ e e₁ e₂ ě ě₁ ě₂ τ τ₀ τ₁ τ₂} →
                   n ； Γ ⊢ e ↬ ě ⇑ τ₀ →
                   τ₀ ⊔ □ + □ ≡ τ₁ + τ₂ →
                   n ； (τ₁ ∷ Γ) ⊢ e₁ ↬ ě₁ ⇓ τ →
                   n ； (τ₂ ∷ Γ) ⊢ e₂ ↬ ě₂ ⇓ τ →
                   n ； Γ ⊢ case e of e₁ · e₂ ↬ case ě of ě₁ · ě₂ ⇓ τ

    mark↤case⇑ : ∀ {n Γ e e₁ e₂ ě ě₁ ě₂ τ τ₀} →
                   n ； Γ ⊢ e ↬ ě ⇑ τ₀ →
                   (∀ {τ₁ τ₂} → τ₀ ⊔ □ + □ ≢ τ₁ + τ₂) →
                   n ； (□ ∷ Γ) ⊢ e₁ ↬ ě₁ ⇓ τ →
                   n ； (□ ∷ Γ) ⊢ e₂ ↬ ě₂ ⇓ τ →
                   n ； Γ ⊢ case e of e₁ · e₂ ↬ case (ě ⦅▸+⦆) of ě₁ · ě₂ ⇓ τ
