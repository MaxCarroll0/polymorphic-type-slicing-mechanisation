-- Lifts expression constructors (pairing, projections, λ:, Λ, def, case, ι₁, ι₂) to expression
-- slices, producing a sliced expression from sliced sub-expressions.
-- Dissertation: supports §4.1 Syntax & Relations and §4.2 Lattice Properties.
module Core.Exp.Lift where

open import Core.Typ
open import Core.Exp.Base
open import Core.Exp.Precision
open import Core.Instances

-- Lift expression constructors to slices

_&ₛ_ : ∀ {e₁ e₂ : Exp} → ⌊ e₁ ⌋ → ⌊ e₂ ⌋ → ⌊ e₁ & e₂ ⌋
s₁ &ₛ s₂ = (s₁ .↓ & s₂ .↓) isSlice ⊑& (s₁ .proof) (s₂ .proof)

π₁ₛ : ∀ {e : Exp} → ⌊ e ⌋ → ⌊ π₁ e ⌋
π₁ₛ (σ isSlice σ⊑e) = (π₁ σ) isSlice (⊑π₁ σ⊑e)

π₂ₛ : ∀ {e : Exp} → ⌊ e ⌋ → ⌊ π₂ e ⌋
π₂ₛ (σ isSlice σ⊑e) = (π₂ σ) isSlice (⊑π₂ σ⊑e)

∘ₛ : ∀ {e₁ e₂ : Exp} → ⌊ e₁ ⌋ → ⌊ e₂ ⌋ → ⌊ e₁ ∘ e₂ ⌋
∘ₛ (σ₁ isSlice p₁) (σ₂ isSlice p₂) = (σ₁ ∘ σ₂) isSlice (⊑∘ p₁ p₂)

<>ₛ : ∀ {e : Exp} {τ : Typ} → ⌊ e ⌋ → ⌊ τ ⌋ → ⌊ e < τ > ⌋
<>ₛ (σ isSlice σ⊑e) (τ isSlice τ⊑σ) = (σ < τ >) isSlice (⊑<> σ⊑e τ⊑σ)

<>typₛ : ∀ {e : Exp} {τ : Typ} → ⌊ e < τ > ⌋ → ⌊ τ ⌋
<>typₛ (□ isSlice proof₁) = □ isSlice ⊑□
<>typₛ (_ < υ > isSlice ⊑<> _ υ⊑τ) = υ isSlice υ⊑τ

Λₛ : ∀ {e : Exp} → ⌊ e ⌋ → ⌊ Λ e ⌋
Λₛ (σ isSlice σ⊑e) = (Λ σ) isSlice (⊑Λ σ⊑e)

λ:ₛ : ∀ {τ₁ : Typ} {e : Exp} → ⌊ τ₁ ⌋ → ⌊ e ⌋ → ⌊ λ: τ₁ ⇒ e ⌋
λ:ₛ (τ isSlice τ⊑τ₁) (σ isSlice σ⊑e) = (λ: τ ⇒ σ) isSlice (⊑λ τ⊑τ₁ σ⊑e)

defₛ : ∀ {e' e : Exp} → ⌊ e' ⌋ → ⌊ e ⌋ → ⌊ def e' ⊢ e ⌋
defₛ (σ₁ isSlice σ₁⊑e') (σ₂ isSlice σ₂⊑e) = (def σ₁ ⊢ σ₂) isSlice (⊑def σ₁⊑e' σ₂⊑e)

caseₛ : ∀ {e e₁ e₂ : Exp} → ⌊ e ⌋ → ⌊ e₁ ⌋ → ⌊ e₂ ⌋ → ⌊ case e of e₁ · e₂ ⌋
caseₛ (σ isSlice p) (σ₁ isSlice p₁) (σ₂ isSlice p₂) =
  (case σ of σ₁ · σ₂) isSlice (⊑case p p₁ p₂)
