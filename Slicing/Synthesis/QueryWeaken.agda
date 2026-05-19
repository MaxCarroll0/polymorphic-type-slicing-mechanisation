{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; cong) renaming (refl to ≡refl; sym to ≡sym; trans to ≡trans)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.List using (_∷_)
open import Core
open import Semantics.Statics

open import Slicing.Synthesis.FixedAssmsCalc

module Slicing.Synthesis.QueryWeaken where

-- Query weakening: raise the query from υ to ψ', keeping the same σ and ψ.
-- The context γ may grow since a larger query may require more context entries.
query-weaken : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → D ◂ υ ⤳ σ ↦ ψ ⊣ γ
    → (ψ' : ⌊ τ ⌋) → υ ⊑ₛ ψ' → ψ' ⊑ₛ ψ
    → ∃[ γ' ] D ◂ ψ' ⤳ σ ↦ ψ ⊣ γ'

-- □ case: ψ must be ⊥ₛ, so ψ' = ⊥ₛ
query-weaken {D = D} min□ (□ isSlice ⊑□) ⊑□ ⊑□ = _ , min□

-- * case: query and output are both ⊤ₛ, ψ' must be ⊤ₛ
query-weaken min* (* isSlice ⊑*) ⊑* ⊑* = _ , min*

-- Var case: output is ⊤ₛ, raise query from υ to ψ'
query-weaken (minVar {τ' = τ'} p {υ = υ} υ≢□) ψ' υ⊑ψ' ψ'⊑ψ
  = _ , minVar p ψ'≢□
  where
    ψ'≢□ : ψ' .↓ ≢ □
    ψ'≢□ eq = υ≢□ (⊑.antisym {Typ} (⊑.trans {Typ} υ⊑ψ' (subst (_⊑ _) (≡sym eq) ⊑□)) ⊑□)

-- Structural cases: recursively weaken sub-derivations
-- Λ: query = ∀· υ, raise to ∀· ψ'body
query-weaken (minΛ sub) (._ isSlice ⊑∀ p') υ⊑ψ' ψ'⊑ψ
  with υ⊑ψ' | ψ'⊑ψ
... | ⊑∀ u⊑p' | ⊑∀ p'⊑ψ
  with query-weaken sub (↑ p') u⊑p' p'⊑ψ
... | γ'' , sub' = _ , minΛ sub'

-- &: query = υ₁ × υ₂
query-weaken (min& sub₁ sub₂) (._ isSlice ⊑× p₁ p₂) υ⊑ψ' ψ'⊑ψ
  with υ⊑ψ' | ψ'⊑ψ
... | ⊑× u₁ u₂ | ⊑× q₁ q₂
  with query-weaken sub₁ (↑ p₁) u₁ q₁ | query-weaken sub₂ (↑ p₂) u₂ q₂
... | _ , sub₁' | _ , sub₂' = _ , min& sub₁' sub₂'

-- Remaining cases
query-weaken (minλ: sub d-ann) ψ' υ⊑ψ' ψ'⊑ψ = {!!}
query-weaken (min∘ υ≢□ sub) ψ' υ⊑ψ' ψ'⊑ψ = {!!}
query-weaken (min<> υ≢□ sub) ψ' υ⊑ψ' ψ'⊑ψ = {!!}
query-weaken (mindef υ≢□ s-body s-def d-def) ψ' υ⊑ψ' ψ'⊑ψ = {!!}
query-weaken (minπ₁ υ≢□ sub) ψ' υ⊑ψ' ψ'⊑ψ = {!!}
query-weaken (minπ₂ υ≢□ sub) ψ' υ⊑ψ' ψ'⊑ψ = {!!}
query-weaken (mincase-cov υ≢□ s₁ s₂ z₁ z₂ υ⊑ s-scr d₁-syn d₂-syn) ψ' υ⊑ψ' ψ'⊑ψ = {!!}
query-weaken (mincase-desc υ≢□ s₁ s₂ z₁ z₂ d₁-syn d₂-syn υ⊑ϕ⊔ s-scr head-min mbpc) ψ' υ⊑ψ' ψ'⊑ψ = {!!}
