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

↓□→⊥ₛ : ∀ {τ : Typ} (υ : ⌊ τ ⌋) → υ .↓ ≡ □ → υ ≡ ⊥ₛ {a = τ}
↓□→⊥ₛ (□ isSlice ⊑□) ≡refl = ≡refl

-- Construct a calculus derivation from a typing derivation and type query
slice
  : ∀ {n Γ e τ} → (D : n ； Γ ⊢ e ↦ τ) → (υ : ⌊ τ ⌋)
    → ∃[ σ ] ∃[ ψ ] ∃[ γ ] D ◂ υ ⤳ σ ↦ ψ ⊣ γ

slice D (□ isSlice ⊑□) = _ , _ , _ , min□
slice ↦* (.* isSlice ⊑*) = _ , _ , _ , min*
slice (↦Var {τ = τ} p) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦Var p ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ = _ , _ , _ , minVar p υ≢□

-- Lambda: use graduality to source the derivations
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
slice (↦Λ D) (.∀· ._ isSlice ⊑∀ p)
  with slice D (↑ p)
... | _ , _ , _ , sub = _ , _ , _ , minΛ sub
slice (↦& D₁ D₂) ((._ × ._) isSlice ⊑× p₁ p₂)
  with slice D₁ (↑ p₁) | slice D₂ (↑ p₂)
... | _ , _ , _ , s₁ | _ , _ , _ , s₂ = _ , _ , _ , min& s₁ s₂

-- Elimination forms
slice (↦∘ D₁ m D₂) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦∘ D₁ m D₂ ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D₁ (unmatch⇒ m ⊥ₛ υ)
...   | _ , _ , _ , sub = _ , _ , _ , min∘ υ≢□ sub

slice (↦<> D m wf) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦<> D m wf ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D (unmatch∀ m (unsub υ))
...   | _ , _ , _ , sub = _ , _ , _ , min<> υ≢□ sub

slice (↦π₁ D m) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦π₁ D m ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D (unmatch× m υ ⊥ₛ)
...   | _ , _ , _ , sub = _ , _ , _ , minπ₁ υ≢□ sub

slice (↦π₂ D m) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦π₂ D m ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D (unmatch× m ⊥ₛ υ)
...   | _ , _ , _ , sub = _ , _ , _ , minπ₂ υ≢□ sub

slice (↦def D₁ D₂) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦def D₁ D₂ ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D₂ υ
...   | _ , _ , ((υ₁-↓ ∷ γ₂-↓) isSlice ⊑∷ υ₁-⊑ γ₂-⊑) , s-body
  with extract s-body | extract-σ s-body
...   | s₂ | ≡refl
  with slice D₁ (υ₁-↓ isSlice υ₁-⊑)
...   | _ , _ , _ , s-def
  with extract s-def | extract-ψ s-def
...   | s₁ | ≡refl
  = let sgs = static-gradual-syn
                (⊑∷ (s₁ ↓ϕ⊑) (⊑.refl {Assms}))
                (s₂ .expₛ .proof)
                D₂
        d-def = proj₁ (proj₂ sgs)
        ψ₂'-⊑ = proj₂ (proj₂ sgs)
    in _ , ↑ ψ₂'-⊑ , _ , mindef {ψ₂' = ↑ ψ₂'-⊑} υ≢□ s-body s-def d-def
slice (↦case D m D₁ D₂ c) υ = {!!}
