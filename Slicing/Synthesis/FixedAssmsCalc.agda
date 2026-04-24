open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; cong) renaming (refl to ≡refl)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.List using (_∷_)
open import Core
open import Semantics.Statics
open import Slicing.Synthesis.FixedAssmsSynthesis

module Slicing.Synthesis.FixedAssmsCalc where

-- Fixed-context minimal expression slice calculus
-- D ◂ₑ υ ↦ ψ ⊣ γ: derivation D explains type query υ within full free context,
-- actually synthesising ψ (where υ ⊑ₛ ψ), using context entries γ.
--
-- No Φ input: free variables are always fully available.
-- γ output: tracks which context entries the minimal expression uses.
-- No cross-feeding: sub-derivations are independent for free variables.
--
-- ψ connects binding sites: in mindef, D₁'s ψ becomes the bound variable
-- type for D₂; in mincase, the scrutinee's ψ provides bound variable
-- types for branches via fst+ₛ/snd+ₛ.
-- Binder rules decompose γ into bound variable usage + free variable usage.
infix 4 _◂ₑ_↦_⊣_
data _◂ₑ_↦_⊣_ {n : ℕ} {Γ : Assms} : ∀ {e : Exp} {τ : Typ}
          → (D : n ； Γ ⊢ e ↦ τ) → ⌊ τ ⌋ → ⌊ τ ⌋ → ⌊ Γ ⌋ → Set where

  -- Variable: uses full type at position p, nothing else
  minVar   : ∀ {n' τ'} (p : Γ at n' ≡ just τ') {υ : ⌊ τ' ⌋}
             → (υ .↓ ≢ □)
             → ↦Var p ◂ₑ υ ↦ ⊤ₛ ⊣ ⊥ₛ [ p ≔ ⊤ₛ ]ₛ

  min□     : ∀ {e τ} {D : n ； Γ ⊢ e ↦ τ}
             → D ◂ₑ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ

  min*     : ↦* ◂ₑ ⊤ₛ ↦ ⊤ₛ ⊣ ⊥ₛ

  -- Lambda: body's γ decomposes into bound var usage ϕ₁ + free var usage γ
  minλ:    : ∀ {e τ₁ τ₂ υ₁ υ₂ ψ₂ ϕ₁ γ} {wf : n ⊢wf τ₁}
               {D : n ； (τ₁ ∷ Γ) ⊢ e ↦ τ₂}
             → D ◂ₑ υ₂ ↦ ψ₂ ⊣ (ϕ₁ ∷ₛ γ)
             → (↦λ: wf D) ◂ₑ (υ₁ ⇒ₛ υ₂) ↦ ((ϕ₁ ⊔ₛ υ₁) ⇒ₛ ψ₂) ⊣ γ

  minΛ     : ∀ {e τ υ ψ' γ}
               {D : suc n ； shiftΓ 1 Γ ⊢ e ↦ τ}
             → D ◂ₑ υ ↦ ψ' ⊣ (shiftΓₛ γ)
             → (↦Λ D) ◂ₑ (∀·ₛ υ) ↦ (∀·ₛ ψ') ⊣ γ

  -- Product: independent sub-derivations, join of context usage
  min&     : ∀ {e₁ e₂ τ₁ τ₂ υ₁ υ₂ ψ₁ ψ₂ γ₁ γ₂}
               {D₁ : n ； Γ ⊢ e₁ ↦ τ₁} {D₂ : n ； Γ ⊢ e₂ ↦ τ₂}
             → D₁ ◂ₑ υ₁ ↦ ψ₁ ⊣ γ₁ → D₂ ◂ₑ υ₂ ↦ ψ₂ ⊣ γ₂
             → (↦& D₁ D₂) ◂ₑ (υ₁ ×ₛ υ₂) ↦ (ψ₁ ×ₛ ψ₂) ⊣ γ₁ ⊔ₛ γ₂

  -- Application: function sub-derivation only
  min∘     : ∀ {e₁ e₂ τ τ₁ τ₂ ψ₁ γ₁}
               {D₁ : n ； Γ ⊢ e₁ ↦ τ} {m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
               {D₂ : n ； Γ ⊢ e₂ ↤ τ₁}
               {υ ψ : ⌊ τ₂ ⌋}
             → D₁ ◂ₑ (unmatch⇒ m ⊥ₛ υ) ↦ ψ₁ ⊣ γ₁
             → (↦∘ D₁ m D₂) ◂ₑ υ ↦ ψ ⊣ γ₁

  -- Type application
  min<>    : ∀ {e τ τ' σ ψ₁ γ}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ ∀· □ ≡ ∀· τ'} {wf : n ⊢wf σ}
               {υ ψ : ⌊ [ zero ↦ σ ] τ' ⌋} {υ' : ⌊ τ' ⌋} {ϕ₁ : ⌊ σ ⌋}
             → υ ⊑ₛ subₛ ϕ₁ υ'
             → D ◂ₑ (unmatch∀ m υ') ↦ ψ₁ ⊣ γ
             → (↦<> D m wf) ◂ₑ υ ↦ ψ ⊣ γ

  -- Let binding: D₁'s ψ₁ becomes bound variable for D₂
  -- Body's γ decomposes: bound var usage ψ₁ + free var usage γ₂
  mindef   : ∀ {e' e τ' τ υ' υ ψ₁ ψ₂ γ₁ γ₂}
               {D₁ : n ； Γ ⊢ e' ↦ τ'} {D₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ}
             → D₁ ◂ₑ υ' ↦ ψ₁ ⊣ γ₁
             → D₂ ◂ₑ υ ↦ ψ₂ ⊣ (ψ₁ ∷ₛ γ₂)
             → (↦def D₁ D₂) ◂ₑ υ ↦ ψ₂ ⊣ γ₁ ⊔ₛ γ₂

  -- Projections
  minπ₁   : ∀ {e τ τ₁ τ₂ υ ψ₁ γ}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
               {ψ : ⌊ τ₁ ⌋}
             → D ◂ₑ (unmatch× m υ ⊥ₛ) ↦ ψ₁ ⊣ γ
             → (↦π₁ D m) ◂ₑ υ ↦ ψ ⊣ γ

  minπ₂   : ∀ {e τ τ₁ τ₂ υ ψ₁ γ}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
               {ψ : ⌊ τ₂ ⌋}
             → D ◂ₑ (unmatch× m ⊥ₛ υ) ↦ ψ₁ ⊣ γ
             → (↦π₂ D m) ◂ₑ υ ↦ ψ ⊣ γ

  -- Case: scrutinee's ψ provides bound variable types for branches
  mincase  : ∀ {e e₁ e₂ τ₁ τ₂ τ₁' τ₂' ς υ₁ υ₂ ψ₀ ψ₁ ψ₂ γ₀ γ₁ γ₂}
               {D : n ； Γ ⊢ e ↦ τ₁ + τ₂}
               {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
               {c : τ₁' ~ τ₂'}
               {υ ψ : ⌊ τ₁' ⊔ τ₂' ⌋}
             → D ◂ₑ ς ↦ ψ₀ ⊣ γ₀
             → D₁ ◂ₑ υ₁ ↦ ψ₁ ⊣ (fst+ₛ ψ₀ ∷ₛ γ₁)
             → D₂ ◂ₑ υ₂ ↦ ψ₂ ⊣ (snd+ₛ ψ₀ ∷ₛ γ₂)
             → υ .↓ ⊑ υ₁ .↓ ⊔ υ₂ .↓
             → (↦case D (⊔□+□ {τ₁} {τ₂}) D₁ D₂ c) ◂ₑ υ ↦ ψ ⊣ (γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂
