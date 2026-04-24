open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; cong) renaming (refl to ≡refl)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.List using (_∷_)
open import Core
open import Semantics.Statics
open import Semantics.Graduality using (static-gradual-syn)
open import Slicing.Synthesis.Synthesis
open import Slicing.Synthesis.BoundedSynthesis
open import Slicing.Synthesis.Decompositions

module Slicing.Synthesis.SynSliceCalc where

-- Bounded minimal synthesis slice calculus
-- Φ ⊢ D ◂ υ ↦ ψ ⊣ γ represents a BoundedMinSynSlice D υ Φ
--
-- Φ : assumptions available from the surrounding context (lower bound)
-- γ : assumptions of the extracted min slice (may omit elements from Φ)
-- ψ : the actual synthesised type of the sliced term (υ ⊑ₛ ψ)
--
-- For rules with multiple independent sub-derivations, each component's
-- used assumptions γ is mutually-fed into the other's available assumptions Φ
--
-- ψ is used as in MinFixedAssmsSynCalc
infix 4 _⊢_◂_↦_⊣_
data _⊢_◂_↦_⊣_ {n : ℕ} {Γ : Assms} : ∀ {e : Exp} {τ : Typ}
          → ⌊ Γ ⌋ → (D : n ； Γ ⊢ e ↦ τ) → ⌊ τ ⌋ → ⌊ τ ⌋ → ⌊ Γ ⌋ → Set where

  -- Only allow vars to query a LARGER type than already used in Φ
  minVar   : ∀ {n τ} {Φ : ⌊ Γ ⌋} (p : Γ at n ≡ just τ) {υ : ⌊ τ ⌋}
             → (υ .↓ ≢ □)   -- To avoid overlap with min□ rule
             → Φ ⊢ ↦Var p ◂ υ ↦ (Φ atₛ p) ⊔ₛ υ ⊣ Φ [ p ≔ (Φ atₛ p) ⊔ₛ υ ]ₛ

  -- Corresponds to slicing out a redundant term
  min□     : ∀ {e τ} {Φ : ⌊ Γ ⌋} {D : n ； Γ ⊢ e ↦ τ}
             → Φ ⊢ D ◂ ⊥ₛ ↦ ⊥ₛ ⊣ Φ

  min*     : ∀ {Φ : ⌊ Γ ⌋}
             → Φ ⊢ ↦* ◂ ⊤ₛ ↦ ⊤ₛ ⊣ Φ

  -- Body sees minimum annotation in Φ, but may require MORE (ϕ₁)
  -- to fully type the body.
  -- ψ = (ϕ₁ ⊔ₛ υ₁) ⇒ₛ ψ₂: annotation is join of body usage and query
  minλ:    : ∀ {e τ₁ τ₂ υ₁ υ₂ Φ ϕ₁ γ ψ₂} {wf : n ⊢wf τ₁}
               {D : n ； (τ₁ ∷ Γ) ⊢ e ↦ τ₂}
             → (υ₁ ∷ₛ Φ) ⊢ D ◂ υ₂ ↦ ψ₂ ⊣ (ϕ₁ ∷ₛ γ)
             → Φ ⊢ (↦λ: wf D) ◂ (υ₁ ⇒ₛ υ₂) ↦ ((ϕ₁ ⊔ₛ υ₁) ⇒ₛ ψ₂) ⊣ γ

  minΛ     : ∀ {e τ Φ γ υ ψ'}
               {D : suc n ； shiftΓ 1 Γ ⊢ e ↦ τ}
             → (shiftΓₛ Φ) ⊢ D ◂ υ ↦ ψ' ⊣ (shiftΓₛ γ)
             → Φ ⊢ (↦Λ D) ◂ (∀·ₛ υ) ↦ (∀·ₛ ψ') ⊣ γ

  -- Each component sees the other's needed assumptions
  -- This rules out counterexample 3
  min&     : ∀ {e₁ e₂ τ₁ τ₂ υ₁ υ₂ Φ γ₁ γ₂ ψ₁ ψ₂}
               {D₁ : n ； Γ ⊢ e₁ ↦ τ₁} {D₂ : n ； Γ ⊢ e₂ ↦ τ₂}
             → (Φ ⊔ₛ γ₂) ⊢ D₁ ◂ υ₁ ↦ ψ₁ ⊣ γ₁
             → (Φ ⊔ₛ γ₁) ⊢ D₂ ◂ υ₂ ↦ ψ₂ ⊣ γ₂
             → Φ ⊢ (↦& D₁ D₂) ◂ (υ₁ ×ₛ υ₂) ↦ (ψ₁ ×ₛ ψ₂) ⊣ γ₁ ⊔ₛ γ₂

  min∘     : ∀ {e₁ e₂ τ τ₁ τ₂ Φ γ₁ ψ₁}
               {D₁ : n ； Γ ⊢ e₁ ↦ τ} {m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
               {D₂ : n ； Γ ⊢ e₂ ↤ τ₁}
               {υ ψ : ⌊ τ₂ ⌋}
             → Φ ⊢ D₁ ◂ (unmatch⇒ m ⊥ₛ υ) ↦ ψ₁ ⊣ γ₁
             → Φ ⊢ (↦∘ D₁ m D₂) ◂ υ ↦ ψ ⊣ γ₁

  min<>    : ∀ {e τ τ' σ Φ γ ψ₁}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ ∀· □ ≡ ∀· τ'} {wf : n ⊢wf σ}
               {υ ψ : ⌊ [ zero ↦ σ ] τ' ⌋} {υ' : ⌊ τ' ⌋} {ϕ₁ : ⌊ σ ⌋}
             → υ ⊑ₛ subₛ ϕ₁ υ'
             → Φ ⊢ D ◂ (unmatch∀ m υ') ↦ ψ₁ ⊣ γ
             → Φ ⊢ (↦<> D m wf) ◂ υ ↦ ψ ⊣ γ

  -- D₁'s 'realised' type ψ becomes D₂'s bound variable
  mindef   : ∀ {e' e τ' τ Φ γ₁ γ₂ υ₁ υ₂ ψ₁ ψ₂}
               {D₁ : n ； Γ ⊢ e' ↦ τ'} {D₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ}
             → (Φ ⊔ₛ γ₂) ⊢ D₁ ◂ υ₁ ↦ ψ₁ ⊣ γ₁
             → (ψ₁ ∷ₛ (Φ ⊔ₛ γ₁)) ⊢ D₂ ◂ υ₂ ↦ ψ₂ ⊣ (υ₁ ∷ₛ γ₂)
             → Φ ⊢ (↦def D₁ D₂) ◂ υ₂ ↦ ψ₂ ⊣ γ₁ ⊔ₛ γ₂

  minπ₁   : ∀ {e τ τ₁ τ₂ Φ γ υ ψ₁}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
               {ψ : ⌊ τ₁ ⌋}
             → Φ ⊢ D ◂ (unmatch× m υ ⊥ₛ) ↦ ψ₁ ⊣ γ
             → Φ ⊢ (↦π₁ D m) ◂ υ ↦ ψ ⊣ γ

  minπ₂   : ∀ {e τ τ₁ τ₂ Φ γ υ ψ₁}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
               {ψ : ⌊ τ₂ ⌋}
             → Φ ⊢ D ◂ (unmatch× m ⊥ₛ υ) ↦ ψ₁ ⊣ γ
             → Φ ⊢ (↦π₂ D m) ◂ υ ↦ ψ ⊣ γ

  -- ψ₀ provides bound variable types for branches;
  -- branch outputs ς₁, ς₂ form scrutinee query ς₁ +ₛ ς₂
  mincase  : ∀ {e e₁ e₂ τ₁ τ₂ τ₁' τ₂' Φ γ₀ γ₁ γ₂ ς₁ ς₂ υ₁ υ₂ ψ₀ ψ₁ ψ₂}
               {D : n ； Γ ⊢ e ↦ τ₁ + τ₂}
               {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
               {c : τ₁' ~ τ₂'}
               {υ ψ : ⌊ τ₁' ⊔ τ₂' ⌋}
             → ((Φ ⊔ₛ γ₁) ⊔ₛ γ₂) ⊢ D ◂ (ς₁ +ₛ ς₂) ↦ ψ₀ ⊣ γ₀
             → (fst+ₛ ψ₀ ∷ₛ ((Φ ⊔ₛ γ₀) ⊔ₛ γ₂)) ⊢ D₁ ◂ υ₁ ↦ ψ₁ ⊣ (ς₁ ∷ₛ γ₁)
             → (snd+ₛ ψ₀ ∷ₛ ((Φ ⊔ₛ γ₀) ⊔ₛ γ₁)) ⊢ D₂ ◂ υ₂ ↦ ψ₂ ⊣ (ς₂ ∷ₛ γ₂)
             → υ .↓ ⊑ υ₁ .↓ ⊔ υ₂ .↓ -- Non-deterministic split on υ
             → Φ ⊢ (↦case D ⊔□+□ D₁ D₂ c) ◂ υ ↦ ψ ⊣ (γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂

-- □ can only synthesize □
□-syn-inv : ∀ {n Γ τ} → n ； Γ ⊢ □ ↦ τ → τ ≡ □
□-syn-inv ↦□ = ≡refl

⊑□-inv : ∀ {τ : Typ} {υ : ⌊ τ ⌋} → υ .↓ ⊑ □ → υ .↓ ≡ □
⊑□-inv ⊑□ = ≡refl

-- The calculus judgment extracts to a BoundedMinSynSlice
-- CONJECTURES (currently)
postulate
  extract
    : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {Φ υ ψ γ}
      → Φ ⊢ D ◂ υ ↦ ψ ⊣ γ
      → BoundedMinSynSlice D υ Φ

  completeness
    : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {Φ υ}
      → (m : BoundedMinSynSlice D υ Φ)
      → ∃[ γ ] ∃[ ψ ] (Φ ⊢ D ◂ υ ↦ ψ ⊣ γ)
