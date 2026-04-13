module Semantics.Elaboration where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core
open import Core.IntExp as I
open import Semantics.Statics.Typing

mutual
  -- Synthesis elaboration: n ； Γ ⊢ e ⇑ τ ↝ d
  infix 4 _；_⊢_⇑_↝_

  data _；_⊢_⇑_↝_ : ℕ → Assms → Exp → Typ → IntExp → Set where
    elab↦*   : ∀ {n Γ} →
                 n ； Γ ⊢ Exp.* ⇑ * ↝ I.*

    elab↦□   : ∀ {n Γ} →
                 n ； Γ ⊢ Exp.□ ⇑ □ ↝ I.□

    elab↦Var : ∀ {n Γ k τ} →
                 Γ at k ≡ just τ →
                 n ； Γ ⊢ Exp.⟨ k ⟩ ⇑ τ ↝ I.⟨ k ⟩

    elab↦λ:  : ∀ {n Γ e τ₁ τ₂ d} →
                 n ⊢wf τ₁ →
                 n ； (τ₁ ∷ Γ) ⊢ e ⇑ τ₂ ↝ d →
                 n ； Γ ⊢ Exp.λ: τ₁ ⇒ e ⇑ τ₁ ⇒ τ₂ ↝ I.λ: τ₁ ⇒ d

    elab↦Λ   : ∀ {n Γ e τ d} →
                 suc n ； shiftΓ (suc zero) Γ ⊢ e ⇑ τ ↝ d →
                 n ； Γ ⊢ Exp.Λ e ⇑ ∀· τ ↝ I.Λ d

    elab↦∘   : ∀ {n Γ e₁ e₂ τ τ₁ τ₂ d₁ d₂} →
                 n ； Γ ⊢ e₁ ⇑ τ ↝ d₁ →
                 τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂ →
                 n ； Γ ⊢ e₂ ⇓ τ₁ ↝ d₂ →
                 n ； Γ ⊢ e₁ Exp.∘ e₂ ⇑ τ₂ ↝ (d₁ I.⟪ τ ⇛ τ₁ ⇒ τ₂ ⟫) I.∘ d₂

    elab↦<>  : ∀ {n Γ e τ τ' σ d} →
                 n ； Γ ⊢ e ⇑ τ ↝ d →
                 τ ⊔ ∀· □ ≡ ∀· τ' →
                 n ⊢wf σ →
                 n ； Γ ⊢ e Exp.< σ > ⇑ [ zero ↦ σ ] τ' ↝ (d I.⟪ τ ⇛ ∀· τ' ⟫) I.< σ >

    elab↦&   : ∀ {n Γ e₁ e₂ τ₁ τ₂ d₁ d₂} →
                 n ； Γ ⊢ e₁ ⇑ τ₁ ↝ d₁ →
                 n ； Γ ⊢ e₂ ⇑ τ₂ ↝ d₂ →
                 n ； Γ ⊢ e₁ Exp.& e₂ ⇑ τ₁ × τ₂ ↝ d₁ I.& d₂

    elab↦π₁  : ∀ {n Γ e τ τ₁ τ₂ d} →
                 n ； Γ ⊢ e ⇑ τ ↝ d →
                 τ ⊔ □ × □ ≡ τ₁ × τ₂ →
                 n ； Γ ⊢ Exp.π₁ e ⇑ τ₁ ↝ I.π₁ (d I.⟪ τ ⇛ τ₁ × τ₂ ⟫)

    elab↦π₂  : ∀ {n Γ e τ τ₁ τ₂ d} →
                 n ； Γ ⊢ e ⇑ τ ↝ d →
                 τ ⊔ □ × □ ≡ τ₁ × τ₂ →
                 n ； Γ ⊢ Exp.π₂ e ⇑ τ₂ ↝ I.π₂ (d I.⟪ τ ⇛ τ₁ × τ₂ ⟫)

    elab↦def : ∀ {n Γ e' e τ' τ d' d} →
                 n ； Γ ⊢ e' ⇑ τ' ↝ d' →
                 n ； (τ' ∷ Γ) ⊢ e ⇑ τ ↝ d →
                 n ； Γ ⊢ Exp.def e' ⊢ e ⇑ τ ↝ I.def d' ⊢ d

    elab↦case : ∀ {n Γ e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂' d d₁ d₂} →
                  n ； Γ ⊢ e ⇑ τ ↝ d →
                  τ ⊔ □ + □ ≡ τ₁ + τ₂ →
                  n ； (τ₁ ∷ Γ) ⊢ e₁ ⇑ τ₁' ↝ d₁ →
                  n ； (τ₂ ∷ Γ) ⊢ e₂ ⇑ τ₂' ↝ d₂ →
                  τ₁' ~ τ₂' →
                  n ； Γ ⊢ Exp.case e of e₁ · e₂ ⇑ τ₁' ⊔ τ₂'
                    ↝ I.case (d I.⟪ τ ⇛ τ₁ + τ₂ ⟫) of (d₁ I.⟪ τ₁' ⇛ τ₁' ⊔ τ₂' ⟫) · (d₂ I.⟪ τ₂' ⇛ τ₁' ⊔ τ₂' ⟫)

  -- Analysis elaboration: n ； Γ ⊢ e ⇓ τ ↝ d
  infix 4 _；_⊢_⇓_↝_

  data _；_⊢_⇓_↝_ : ℕ → Assms → Exp → Typ → IntExp → Set where
    elab↤sub  : ∀ {n Γ e τ τ' d} →
                  n ； Γ ⊢ e ⇑ τ' ↝ d →
                  τ ~ τ' →
                  n ； Γ ⊢ e ⇓ τ ↝ d I.⟪ τ' ⇛ τ ⟫

    elab↤λ    : ∀ {n Γ e τ τ₁ τ₂ d} →
                  τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂ →
                  n ； (τ₁ ∷ Γ) ⊢ e ⇓ τ₂ ↝ d →
                  n ； Γ ⊢ Exp.λ⇒ e ⇓ τ ↝ (I.λ: τ₁ ⇒ d) I.⟪ τ₁ ⇒ τ₂ ⇛ τ ⟫

    elab↤λ:   : ∀ {n Γ e τ τ₁ τ₁' τ₂ d} →
                  τ ⊔ τ₁ ⇒ □ ≡ τ₁' ⇒ τ₂ →
                  n ⊢wf τ₁ →
                  n ； (τ₁ ∷ Γ) ⊢ e ⇓ τ₂ ↝ d →
                  n ； Γ ⊢ Exp.λ: τ₁ ⇒ e ⇓ τ ↝ (I.λ: τ₁ ⇒ d) I.⟪ τ₁ ⇒ τ₂ ⇛ τ₁' ⇒ τ₂ ⟫ I.⟪ τ₁' ⇒ τ₂ ⇛ τ ⟫

    elab↤ι₁   : ∀ {n Γ e τ τ₁ τ₂ d} →
                  τ ⊔ □ + □ ≡ τ₁ + τ₂ →
                  n ； Γ ⊢ e ⇓ τ₁ ↝ d →
                  n ； Γ ⊢ Exp.ι₁ e ⇓ τ ↝ (I.ι₁ d) I.⟪ τ₁ + τ₂ ⇛ τ ⟫

    elab↤ι₂   : ∀ {n Γ e τ τ₁ τ₂ d} →
                  τ ⊔ □ + □ ≡ τ₁ + τ₂ →
                  n ； Γ ⊢ e ⇓ τ₂ ↝ d →
                  n ； Γ ⊢ Exp.ι₂ e ⇓ τ ↝ (I.ι₂ d) I.⟪ τ₁ + τ₂ ⇛ τ ⟫

    elab↤&    : ∀ {n Γ e₁ e₂ τ τ₁ τ₂ d₁ d₂} →
                  τ ⊔ □ × □ ≡ τ₁ × τ₂ →
                  n ； Γ ⊢ e₁ ⇓ τ₁ ↝ d₁ →
                  n ； Γ ⊢ e₂ ⇓ τ₂ ↝ d₂ →
                  n ； Γ ⊢ e₁ Exp.& e₂ ⇓ τ ↝ (d₁ I.& d₂) I.⟪ τ₁ × τ₂ ⇛ τ ⟫

    elab↤case : ∀ {n Γ e e₁ e₂ τ τ₀ τ₁ τ₂ d d₁ d₂} →
                  n ； Γ ⊢ e ⇑ τ₀ ↝ d →
                  τ₀ ⊔ □ + □ ≡ τ₁ + τ₂ →
                  n ； (τ₁ ∷ Γ) ⊢ e₁ ⇓ τ ↝ d₁ →
                  n ； (τ₂ ∷ Γ) ⊢ e₂ ⇓ τ ↝ d₂ →
                  n ； Γ ⊢ Exp.case e of e₁ · e₂ ⇓ τ
                    ↝ I.case (d I.⟪ τ₀ ⇛ τ₁ + τ₂ ⟫) of d₁ · d₂

    elab↤def  : ∀ {n Γ e' e τ' τ d' d} →
                  n ； Γ ⊢ e' ⇑ τ' ↝ d' →
                  n ； (τ' ∷ Γ) ⊢ e ⇓ τ ↝ d →
                  n ； Γ ⊢ Exp.def e' ⊢ e ⇓ τ ↝ I.def d' ⊢ d
