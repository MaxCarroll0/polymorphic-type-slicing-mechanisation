module Semantics.Dynamics.Typing where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Core
open import Core.IntExp
open import Semantics.Dynamics.Ground

-- Type assignment for internal expressions (non bidirectional)
infix 4 _；_⊢_∶_

data _；_⊢_∶_ : ℕ → Assms → IntExp → Typ → Set where
  ∶*    : ∀ {n Γ} →
            n ； Γ ⊢ IntExp.* ∶ *

  ∶□    : ∀ {n Γ} →
            n ； Γ ⊢ IntExp.□ ∶ □

  ∶Var  : ∀ {n Γ k τ} →
            Γ at k ≡ just τ →
            n ； Γ ⊢ IntExp.⟨ k ⟩ ∶ τ

  ∶λ    : ∀ {n Γ d τ₁ τ₂} →
            n ⊢wf τ₁ →
            n ； (τ₁ ∷ Γ) ⊢ d ∶ τ₂ →
            n ； Γ ⊢ IntExp.λ: τ₁ ⇒ d ∶ τ₁ ⇒ τ₂

  ∶∘    : ∀ {n Γ d₁ d₂ τ₁ τ₂} →
            n ； Γ ⊢ d₁ ∶ τ₁ ⇒ τ₂ →
            n ； Γ ⊢ d₂ ∶ τ₁ →
            n ； Γ ⊢ d₁ IntExp.∘ d₂ ∶ τ₂

  ∶Λ    : ∀ {n Γ d τ} →
            suc n ； shiftΓ (suc zero) Γ ⊢ d ∶ τ →
            n ； Γ ⊢ IntExp.Λ d ∶ ∀· τ

  ∶<>   : ∀ {n Γ d τ σ} →
            n ； Γ ⊢ d ∶ ∀· τ →
            n ⊢wf σ →
            n ； Γ ⊢ d IntExp.< σ > ∶ [ zero ↦ σ ] τ

  ∶&    : ∀ {n Γ d₁ d₂ τ₁ τ₂} →
            n ； Γ ⊢ d₁ ∶ τ₁ →
            n ； Γ ⊢ d₂ ∶ τ₂ →
            n ； Γ ⊢ d₁ IntExp.& d₂ ∶ τ₁ × τ₂

  ∶ι₁   : ∀ {n Γ d τ₁ τ₂} →
            n ⊢wf τ₂ →
            n ； Γ ⊢ d ∶ τ₁ →
            n ； Γ ⊢ IntExp.ι₁ d ∶ τ₁ + τ₂

  ∶ι₂   : ∀ {n Γ d τ₁ τ₂} →
            n ⊢wf τ₁ →
            n ； Γ ⊢ d ∶ τ₂ →
            n ； Γ ⊢ IntExp.ι₂ d ∶ τ₁ + τ₂

  ∶case : ∀ {n Γ d d₁ d₂ τ₁ τ₂ τ} →
            n ； Γ ⊢ d ∶ τ₁ + τ₂ →
            n ； (τ₁ ∷ Γ) ⊢ d₁ ∶ τ →
            n ； (τ₂ ∷ Γ) ⊢ d₂ ∶ τ →
            n ； Γ ⊢ IntExp.case d of d₁ · d₂ ∶ τ

  ∶π₁   : ∀ {n Γ d τ₁ τ₂} →
            n ； Γ ⊢ d ∶ τ₁ × τ₂ →
            n ； Γ ⊢ IntExp.π₁ d ∶ τ₁

  ∶π₂   : ∀ {n Γ d τ₁ τ₂} →
            n ； Γ ⊢ d ∶ τ₁ × τ₂ →
            n ； Γ ⊢ IntExp.π₂ d ∶ τ₂

  ∶def  : ∀ {n Γ d' d τ' τ} →
            n ； Γ ⊢ d' ∶ τ' →
            n ； (τ' ∷ Γ) ⊢ d ∶ τ →
            n ； Γ ⊢ IntExp.def d' ⊢ d ∶ τ

  ∶cast : ∀ {n Γ d τ₁ τ₂} →
            n ； Γ ⊢ d ∶ τ₁ →
            τ₁ ~ τ₂ →
            n ； Γ ⊢ d ⟪ τ₁ ⇛ τ₂ ⟫ ∶ τ₂

  ∶fail : ∀ {n Γ d τ₁ τ₂} →
            n ； Γ ⊢ d ∶ τ₁ →
            Ground τ₁ → Ground τ₂ →
            τ₁ ≢ τ₂ →
            n ； Γ ⊢ d ⟪ τ₁ ⇛⊥ τ₂ ⟫ ∶ τ₂
