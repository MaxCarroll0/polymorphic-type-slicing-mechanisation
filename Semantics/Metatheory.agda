module Semantics.Metatheory where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (∃; Σ; _,_)
open import Core
open import Core.IntExp as I
open import Semantics.Statics.Typing
open import Semantics.Dynamics.Typing as IT
open import Semantics.Dynamics.Values
open import Semantics.Dynamics.EvalCtx
open import Semantics.Dynamics.Step
open import Semantics.Elaboration

-- Elaboration Completeness
mutual
  elab-complete-syn : ∀ {n Γ e τ} →
    n ； Γ ⊢ e ↦ τ → ∃ λ d → n ； Γ ⊢ e ⇑ τ ↝ d
  elab-complete-syn ↦* =
    I.* , elab↦*
  elab-complete-syn ↦□ =
    I.□ , elab↦□
  elab-complete-syn (↦Var p) =
    I.⟨ _ ⟩ , elab↦Var p
  elab-complete-syn (↦λ: wf D)
    with elab-complete-syn D
  ... | d , ed =
    I.λ: _ ⇒ d , elab↦λ: wf ed
  elab-complete-syn (↦def D₁ D₂)
    with elab-complete-syn D₁ | elab-complete-syn D₂
  ... | d₁ , ed₁ | d₂ , ed₂ =
    I.def d₁ ⊢ d₂ , elab↦def ed₁ ed₂
  elab-complete-syn (↦Λ D)
    with elab-complete-syn D
  ... | d , ed =
    I.Λ d , elab↦Λ ed
  elab-complete-syn (↦∘ D₁ m D₂)
    with elab-complete-syn D₁ | elab-complete-ana D₂
  ... | d₁ , ed₁ | d₂ , ed₂ =
    (d₁ I.⟪ _ ⇛ _ ⟫) I.∘ d₂ , elab↦∘ ed₁ m ed₂
  elab-complete-syn (↦<> D m wf)
    with elab-complete-syn D
  ... | d , ed =
    (d I.⟪ _ ⇛ _ ⟫) I.< _ > , elab↦<> ed m wf
  elab-complete-syn (↦& D₁ D₂)
    with elab-complete-syn D₁ | elab-complete-syn D₂
  ... | d₁ , ed₁ | d₂ , ed₂ =
    d₁ I.& d₂ , elab↦& ed₁ ed₂
  elab-complete-syn (↦π₁ D m)
    with elab-complete-syn D
  ... | d , ed =
    I.π₁ (d I.⟪ _ ⇛ _ ⟫) , elab↦π₁ ed m
  elab-complete-syn (↦π₂ D m)
    with elab-complete-syn D
  ... | d , ed =
    I.π₂ (d I.⟪ _ ⇛ _ ⟫) , elab↦π₂ ed m
  elab-complete-syn (↦case D m D₁ D₂ c)
    with elab-complete-syn D | elab-complete-syn D₁ | elab-complete-syn D₂
  ... | d , ed | d₁ , ed₁ | d₂ , ed₂ =
    I.case (d I.⟪ _ ⇛ _ ⟫) of d₁ · d₂ , elab↦case ed m ed₁ ed₂ c

  elab-complete-ana : ∀ {n Γ e τ} →
    n ； Γ ⊢ e ↤ τ → ∃ λ d → n ； Γ ⊢ e ⇓ τ ↝ d
  elab-complete-ana (↤Sub D c)
    with elab-complete-syn D
  ... | d , ed =
    d I.⟪ _ ⇛ _ ⟫ , elab↤sub ed c
  elab-complete-ana (↤λ m D)
    with elab-complete-ana D
  ... | d , ed =
    I.λ: _ ⇒ d , elab↤λ m ed
  elab-complete-ana (↤case D m D₁ D₂)
    with elab-complete-syn D | elab-complete-ana D₁ | elab-complete-ana D₂
  ... | d , ed | d₁ , ed₁ | d₂ , ed₂ =
    I.case (d I.⟪ _ ⇛ _ ⟫) of d₁ · d₂ , elab↤case ed m ed₁ ed₂
  elab-complete-ana (↤ι₁ m D)
    with elab-complete-ana D
  ... | d , ed =
    I.ι₁ d , elab↤ι₁ m ed
  elab-complete-ana (↤ι₂ m D)
    with elab-complete-ana D
  ... | d , ed =
    I.ι₂ d , elab↤ι₂ m ed
  elab-complete-ana (↤& m D₁ D₂)
    with elab-complete-ana D₁ | elab-complete-ana D₂
  ... | d₁ , ed₁ | d₂ , ed₂ =
    d₁ I.& d₂ , elab↤& m ed₁ ed₂
  elab-complete-ana (↤λ: c m wf D)
    with elab-complete-ana D
  ... | d , ed =
    I.λ: _ ⇒ d , elab↤λ: c m wf ed
  elab-complete-ana (↤def D₁ D₂)
    with elab-complete-syn D₁ | elab-complete-ana D₂
  ... | d₁ , ed₁ | d₂ , ed₂ =
    I.def d₁ ⊢ d₂ , elab↤def ed₁ ed₂

-- Elaboration Soundness
-- TODO: needs helper lemmas (⊔⇒~ for consistency from join, wf from matching)
postulate
  elab-sound-syn : ∀ {n Γ e τ d} →
    n ； Γ ⊢ e ⇑ τ ↝ d → n IT.； Γ ⊢ d ∶ τ

  elab-sound-ana : ∀ {n Γ e τ d} →
    n ； Γ ⊢ e ⇓ τ ↝ d → ∃ λ τ' → (n IT.； Γ ⊢ d ∶ τ')

-- Type Safety
postulate
  preservation : ∀ {n Γ d d' τ} →
    n IT.； Γ ⊢ d ∶ τ → d ↦ d' → n IT.； Γ ⊢ d' ∶ τ

  progress : ∀ {d τ} →
    zero IT.； [] ⊢ d ∶ τ → Final d ⊎ (∃ λ d' → d ↦ d')

-- Gradual Guarantee
postulate
  static-gradual-syn : ∀ {n Γ₁ Γ₂ e₁ e₂ τ₁} →
    e₁ ⊑ e₂ → Γ₁ ⊑ Γ₂ →
    n ； Γ₁ ⊢ e₁ ↦ τ₁ →
    ∃ λ τ₂ → n ； Γ₂ ⊢ e₂ ↦ τ₂
