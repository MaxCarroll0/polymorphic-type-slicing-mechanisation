open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; subst)
open import Core
open import Data.List using (_∷_)
open import Semantics.Statics
open import Semantics.Graduality using (static-gradual-syn; syn-precision)
open import Slicing.Synthesis.Synthesis
open import Slicing.Synthesis.BoundedSynthesis
open import Slicing.Synthesis.Decompositions
open import Core.Assms.BiasedPrecision using (_≼a_; _≼ₛ_; ≼ₛ-⊔ₛ-closed; ≼ₛ-weaken-⊔ₛᵣ; ≼ₛ-weaken-⊔ₛₗ; ⊑-≼-trans)

module Slicing.Synthesis.BoundedDecompositions where

open ⊑ {A = Assms} using () renaming (refl to ⊑a-refl)
open ⊑ {A = Exp} using () renaming (refl to ⊑e-refl)

bounded-min-prod-construction
  : ∀ {n Γ e₁ e₂ τ₁ τ₂}
      {D₁ : n ； Γ ⊢ e₁ ↦ τ₁} {D₂ : n ； Γ ⊢ e₂ ↦ τ₂}
      {υ₁ : ⌊ τ₁ ⌋} {υ₂ : ⌊ τ₂ ⌋} {Φ : ⌊ Γ ⌋}
      (m₁ : SynSlice D₁ ◂ υ₁) (m₂ : SynSlice D₂ ◂ υ₂)
    → (_≼ₛ_ {Γ = Γ} (Φ ⊔ₛ (m₂ ↓γₛ)) (m₁ ↓γₛ))
    → (_≼ₛ_ {Γ = Γ} (Φ ⊔ₛ (m₁ ↓γₛ)) (m₂ ↓γₛ))
    → BoundedIsMinimal (Φ ⊔ₛ (m₂ ↓γₛ)) m₁
    → BoundedIsMinimal (Φ ⊔ₛ (m₁ ↓γₛ)) m₂
    → BoundedMinSynSlice (↦& D₁ D₂) (υ₁ ×ₛ υ₂) Φ
bounded-min-prod-construction {D₁ = D₁} {D₂ = D₂} {Φ = Φ} m₁ m₂ Φγ₂≼γ₁ Φγ₁≼γ₂ min₁ min₂
  = m₁ &syn m₂ , Φ≼m×γ , bmin
  where
    γ₁ = m₁ ↓γₛ
    γ₂ = m₂ ↓γₛ

    Φ≼γ₁ : Φ .↓ ≼a m₁ ↓γ
    Φ≼γ₁ = ≼ₛ-weaken-⊔ₛₗ Φ γ₂ γ₁ Φγ₂≼γ₁

    Φ≼γ₂ : Φ .↓ ≼a m₂ ↓γ
    Φ≼γ₂ = ≼ₛ-weaken-⊔ₛₗ Φ γ₁ γ₂ Φγ₁≼γ₂

    -- (m₁ &syn m₂) ↓γ ≡ (γ₁ ⊔ₛ γ₂) .↓ by &syn-↓ρ
    m×γ≡ : (m₁ &syn m₂) ↓γ ≡ (γ₁ ⊔ₛ γ₂) .↓
    m×γ≡ with &syn-↓ρ m₁ m₂
    ... | eq = Eq.cong proj₁ eq

    Φ≼m×γ : Φ .↓ ≼a (m₁ &syn m₂) ↓γ
    Φ≼m×γ = subst (Φ .↓ ≼a_) (Eq.sym m×γ≡) (≼ₛ-⊔ₛ-closed Φ γ₁ γ₂ Φ≼γ₁ Φ≼γ₂)

    bmin : BoundedIsMinimal Φ (m₁ &syn m₂)
    bmin s' Φ≼s'γ s'⊑m×
      with s' .syn | s' .valid | s' ↓σ⊑ | s' ↓ϕ⊑
    ... | ↦□ | () | _ | _
    ... | ↦& d₁' d₂' | ⊑× v₁ v₂ | ⊑& σ₁'⊑ σ₂'⊑ | ⊑× ϕ₁'⊑ ϕ₂'⊑
      with subst (s' ↓ρ ⊑_) (&syn-↓ρ m₁ m₂) s'⊑m×
    ... | s'γ⊑γ⊔ , ⊑& σ₁'⊑m₁σ σ₂'⊑m₂σ
      = let 
            s₁' = ((s' ↓γₛ) ,ₛ (_ isSlice σ₁'⊑)) ⇑ (↑ ϕ₁'⊑) ∈ d₁' ⊒ v₁
            s₂' = ((s' ↓γₛ) ,ₛ (_ isSlice σ₂'⊑)) ⇑ (↑ ϕ₂'⊑) ∈ d₂' ⊒ v₂
            -- Need: s'↓γ ⊑ γᵢ.↓ for sᵢ'⊑mᵢ (γ component)
            -- and σᵢ' ⊑ mᵢ↓σ (σ component, have from ⊑& inversion above)
            -- γ direction: s'↓γ ⊑ (γ₁⊔γ₂).↓ (have) but need s'↓γ ⊑ γ₁.↓
            -- requires (γ₁⊔γ₂).↓ ⊑ γ₁.↓ i.e. γ₂ ⊑ γ₁
            s₁'⊑m₁ : s₁' ⊑ m₁
            s₁'⊑m₁ = {!!}
            s₂'⊑m₂ : s₂' ⊑ m₂
            s₂'⊑m₂ = {!!}
            -- Bound: need (Φ⊔γ₂) ≼ s'↓γ and (Φ⊔γ₁) ≼ s'↓γ
            -- equires γᵢ ≼ s'↓γ which doesn't follow from
            -- s'↓γ ⊑ (γ₁⊔γ₂).↓ (wrong direction for ⊑-≼-trans)
            Φγ₂≼s'γ : (Φ ⊔ₛ γ₂) .↓ ≼a s' ↓γ
            Φγ₂≼s'γ = {!!}
            Φγ₁≼s'γ : (Φ ⊔ₛ γ₁) .↓ ≼a s' ↓γ
            Φγ₁≼s'γ = {!!}
            m₁≈s₁' = min₁ s₁' Φγ₂≼s'γ s₁'⊑m₁
            m₂≈s₂' = min₂ s₂' Φγ₁≼s'γ s₂'⊑m₂
        in ⊑.antisym ⦃ prog-slice-precision ⦄
             (subst (_⊑ s' ↓ρ) (Eq.sym (&syn-↓ρ m₁ m₂))
               (HasJoin.closure assms-join
                 (proj₁ (⊑.reflexive ⦃ prog-slice-precision ⦄ m₁≈s₁'))
                 (proj₁ (⊑.reflexive ⦃ prog-slice-precision ⦄ m₂≈s₂'))
               , ⊑& (proj₂ (⊑.reflexive ⦃ prog-slice-precision ⦄ m₁≈s₁'))
                     (proj₂ (⊑.reflexive ⦃ prog-slice-precision ⦄ m₂≈s₂'))))
             s'⊑m×
