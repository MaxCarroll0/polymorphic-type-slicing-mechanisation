open import Data.Nat
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Core
open import Agda.Builtin.FromNat using (Number; fromNat)

module Semantics.Statics.Typing where

infix  4 _⊢_↦_
infix  4 _⊢_↤_
-- TODO: better notation than using ↦ and ↤
mutual
  data _⊢_↦_ : Assms → Exp → Typ → Set where
    ↦*   : ∀ {Γ : Assms} →
             -----------
              Γ ⊢ * ↦ *

    ↦□   : ∀ {Γ : Assms} →
             -----------
             Γ ⊢ □ ↦ □
              
    ↦Var : ∀ {Γ : Assms} {n : ℕ} {τ : Typ} →
              Γ at n ≡ just τ              →
             ------------------
              Γ ⊢ ⟨ n ⟩ ↦ τ

    ↦λ   : ∀ {Γ : Assms} {e : Exp} {τ₁ τ₂ : Typ} →
              (τ₁ ∷ Γ) ⊢ e ↦ τ₂                  →
              -- TODO: inherently well-scoped terms or a well-formedness judgement Γ ⊢ τ
              ------------------
              Γ ⊢ λ· τ₁ ⇒ e ↦ τ₁ ⇒ τ₂

    ↦def : ∀ {Γ : Assms} {e' e : Exp} {τ' τ : Typ} →
              Γ ⊢ e' ↦ τ'                          →
              (τ' ∷ Γ) ⊢ e ↦ τ                     →
              -----------------
              Γ ⊢ def e' ⊢ e ↦ τ

    ↦Γ   : ∀ {Γ : Assms} {e : Exp} {τ : Typ} →
             --(0 ∷ Γ) ⊢ e ↦ τ                → -- Representing type vars by ⟨ 0 ⟩. ALSO, fix instance resolution for 0 to ⟨ 0 ⟩
             ---------------
             Γ ⊢ Λ e ↦ ∀· τ

    ↦∘   : ∀ {Γ : Assms} {e₁ e₂ : Exp} {τ τ₁ τ₂ : Typ} →
              Γ ⊢ e₁ ↦ τ                               →
              τ ~ □ ⇒ □                                → -- TODO: Make join default to □ meaning that this assumption is unneeded (i.e. any inconsistent joins cannot be decomposed)
              τ ⊔t □ ⇒ □ ≡ τ₁ ⇒ τ₂                     →
              Γ ⊢ e₂ ↤ τ₁                              →
              --------------------
              Γ ⊢ e₁ ∘ e₂ ↦ τ₂
              
    -- TODO: Add a second application form e < τ > for type application
    -- ↦Λ : ∀ {Γ : Assms} {e : Exp} {τ τ' σ : Typ} →
    --         Γ ⊢ e ↦ τ ↦
    --         τ ~ ∀· □  ↦ -- TODO: Again same as above have join default to □
    --         τ ⊔t ∀· □ ≡ ∀· τ' ↦
               -----------------
    --         Γ ⊢ e < σ > ↦ τ' [ 0 ↦ σ ] -- TODO: Implement type substitution 
    -- TODO: Sums, Products
  data _⊢_↤_ : Assms → Exp → Typ → Set where
    ↤Sub : ∀ {Γ : Assms} {e : Exp} {τ τ' : Typ} →
              Γ ⊢ e ↦ τ'                        →
              τ ~ τ'                            →
              ----------
              Γ ⊢ e ↤ τ

    -- TODO: Unnannotated lambdas. The only terms that don't synthesise (I think?)
    -- Other compound terms need to pass checking through inner terms to check inner unannotated lambdas
