-- Well-foundedness postulates for strict precision on type slices.
-- The type slice lattice ⌊ τ ⌋ is finite, so both strict orders are well-founded.
module Core.Typ.WellOrder where

open import Induction.WellFounded using (WellFounded)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Core.Typ.Base using (Typ)
open import Core.Typ.Precision
open import Core.Instances

-- Strict downward precision on slices: a ⊏ b means a .↓ ⊏ b .↓
-- Well-founded because ⌊ τ ⌋ is a finite lattice
postulate
  ⊏ₛ-wf : ∀ {τ : Typ} → WellFounded (λ (a b : ⌊ τ ⌋) → a .↓ ⊏ b .↓)

-- Strict upward precision on slices: a ⊐ b means a .↓ ⊐ b .↓
-- Well-founded because ⌊ τ ⌋ is a finite lattice
postulate
  ⊐ₛ-wf : ∀ {τ : Typ} → WellFounded (λ (a b : ⌊ τ ⌋) → a .↓ ⊐ b .↓)

-- Product well-order for iteration state (ψ₁ decreasing, ψ₂ increasing)
-- Used for termination of the Kleene fixed-point iteration.
postulate
  ⊏×⊐-wf : ∀ {τ₁ τ₂ : Typ}
    → WellFounded (λ (p q : ⌊ τ₁ ⌋ × ⌊ τ₂ ⌋) →
        proj₁ p .↓ ⊏ proj₁ q .↓
      × proj₂ p .↓ ⊐ proj₂ q .↓)

-- Triple-product well-order: at least one strict-up component, the
-- others non-decreasing. Used for the case-fixed-point Kleene iteration
-- on (ψ₀, ψ₁p, ψ₂p).
⊐×⊐×⊐-rel
  : ∀ {τ₁ τ₂ τ₃ : Typ}
  → ⌊ τ₁ ⌋ × ⌊ τ₂ ⌋ × ⌊ τ₃ ⌋
  → ⌊ τ₁ ⌋ × ⌊ τ₂ ⌋ × ⌊ τ₃ ⌋ → Set
⊐×⊐×⊐-rel (a₁ , b₁ , c₁) (a₂ , b₂ , c₂) =
    ((a₁ .↓ ⊐ a₂ .↓) × (b₂ .↓ ⊑ b₁ .↓) × (c₂ .↓ ⊑ c₁ .↓))
  ⊎ ((a₂ .↓ ⊑ a₁ .↓) × (b₁ .↓ ⊐ b₂ .↓) × (c₂ .↓ ⊑ c₁ .↓))
  ⊎ ((a₂ .↓ ⊑ a₁ .↓) × (b₂ .↓ ⊑ b₁ .↓) × (c₁ .↓ ⊐ c₂ .↓))

postulate
  ⊐×⊐×⊐-wf : ∀ {τ₁ τ₂ τ₃ : Typ} → WellFounded (⊐×⊐×⊐-rel {τ₁} {τ₂} {τ₃})
