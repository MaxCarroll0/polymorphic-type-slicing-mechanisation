{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; cong) renaming (refl to ≡refl; sym to ≡sym)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.List using (_∷_)
open import Core
open import Semantics.Statics
open import Semantics.Graduality using (static-gradual-syn)

open import Slicing.Synthesis.FixedAssmsCalc
open import Slicing.Synthesis.FixedAssmsSynthesis

module Slicing.Synthesis.FixedAssmsSlicing where

-- Helper: if υ .↓ ≡ □ then υ ≡ ⊥ₛ
↓□→⊥ₛ : ∀ {τ : Typ} (υ : ⌊ τ ⌋) → υ .↓ ≡ □ → υ ≡ ⊥ₛ {a = τ}
↓□→⊥ₛ (□ isSlice ⊑□) ≡refl = ≡refl

-- Construct a calculus derivation from a typing derivation and type query
slice
  : ∀ {n Γ e τ} → (D : n ； Γ ⊢ e ↦ τ) → (υ : ⌊ τ ⌋)
    → ∃[ σ ] ∃[ ψ ] ∃[ γ ] D ◂ υ ⤳ σ ↦ ψ ⊣ γ

-- □ query: always min□
slice D (□ isSlice ⊑□) = _ , _ , _ , min□

-- ↦*
slice ↦* (.* isSlice ⊑*) = _ , _ , _ , min*

-- Variables
slice (↦Var {τ = τ} p) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦Var p ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ = _ , _ , _ , minVar p υ≢□

-- Lambda
slice (↦λ: {τ₁ = τ₁} wf D) ((._ ⇒ ._) isSlice ⊑⇒ p₁ p₂)
  with slice D (↑ p₂)
... | _ , _ , ((ϕ₁-↓ ∷ γ-↓) isSlice ⊑∷ ϕ₁-⊑ γ-⊑) , sub
  with extract sub | extract-σ sub
... | s | ≡refl
  = let υ₁ = ↑ p₁
        ϕ₁ = ϕ₁-↓ isSlice ϕ₁-⊑
        ann = ϕ₁ ⊔ₛ υ₁
        sgs = static-gradual-syn
                (⊑∷ (ann .proof) (⊑.refl {Assms}))
                (s .expₛ .proof)
                D
        d-ann = proj₁ (proj₂ sgs)
        ψ₂'-⊑ = proj₂ (proj₂ sgs)
    in _ , _ , _ , minλ: {ψ₂' = ↑ ψ₂'-⊑} sub d-ann

-- Type abstraction
slice (↦Λ D) υ = {!!}

-- Pair
slice (↦& D₁ D₂) ((._ × ._) isSlice ⊑× p₁ p₂)
  with slice D₁ (↑ p₁) | slice D₂ (↑ p₂)
... | _ , _ , _ , s₁ | _ , _ , _ , s₂ = _ , _ , _ , min& s₁ s₂

-- Elimination forms
slice (↦∘ D₁ m D₂) υ = {!!}
slice (↦<> D m wf) υ = {!!}
slice (↦π₁ D m) υ = {!!}
slice (↦π₂ D m) υ = {!!}
slice (↦def D₁ D₂) υ = {!!}
slice (↦case D m D₁ D₂ c) υ = {!!}
