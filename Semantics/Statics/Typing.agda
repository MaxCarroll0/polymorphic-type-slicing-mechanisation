open import Data.Nat hiding (_+_; _⊔_)
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Core
open import Agda.Builtin.FromNat using (Number; fromNat)

module Semantics.Statics.Typing where

-- TODO: ⇑ and ⇓ syntax and change full width semicolon to a less confusing
infix  4 _；_⊢_↦_
infix  4 _；_⊢_↤_

mutual
  data _；_⊢_↦_ : ℕ → Assms → Exp → Typ → Set where
    ↦*   : ∀ {n : ℕ} {Γ : Assms} →
             -----------
              n ； Γ ⊢ * ↦ *

    ↦□   : ∀ {n : ℕ} {Γ : Assms} →
             -----------
              n ； Γ ⊢ □ ↦ □

    ↦Var : ∀ {n : ℕ} {Γ : Assms} {k : ℕ} {τ : Typ} →
              Γ at k ≡ just τ              →
             ------------------
              n ； Γ ⊢ ⟨ k ⟩ ↦ τ

    ↦λ:  : ∀ {n : ℕ} {Γ : Assms} {e : Exp} {τ₁ τ₂ : Typ} →
              n ⊢wf τ₁                    →
              n ； (τ₁ ∷ Γ) ⊢ e ↦ τ₂      →
              ------------------
              n ； Γ ⊢ λ: τ₁ ⇒ e ↦ τ₁ ⇒ τ₂

    ↦def : ∀ {n : ℕ} {Γ : Assms} {e' e : Exp} {τ' τ : Typ} →
              n ； Γ ⊢ e' ↦ τ'            →
              n ； (τ' ∷ Γ) ⊢ e ↦ τ       →
              -----------------
              n ； Γ ⊢ def e' ⊢ e ↦ τ

    ↦Λ   : ∀ {n : ℕ} {Γ : Assms} {e : Exp} {τ : Typ} →
              suc n ； shiftΓ (suc zero) Γ ⊢ e ↦ τ →
              ---------------
              n ； Γ ⊢ Λ e ↦ ∀· τ

    ↦∘   : ∀ {n : ℕ} {Γ : Assms} {e₁ e₂ : Exp} {τ τ₁ τ₂ : Typ} →
              n ； Γ ⊢ e₁ ↦ τ             →
              τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂         →
              n ； Γ ⊢ e₂ ↤ τ₁            →
              --------------------
              n ； Γ ⊢ e₁ ∘ e₂ ↦ τ₂

    ↦<>  : ∀ {n : ℕ} {Γ : Assms} {e : Exp} {τ τ' σ : Typ} →
              n ； Γ ⊢ e ↦ τ              →
              τ ⊔ ∀· □ ≡ ∀· τ'            →
              n ⊢wf σ                     →
              --------------------------
              n ； Γ ⊢ e < σ > ↦ [ zero ↦ σ ] τ'

    ↦&   : ∀ {n : ℕ} {Γ : Assms} {e₁ e₂ : Exp} {τ₁ τ₂ : Typ} →
              n ； Γ ⊢ e₁ ↦ τ₁            →
              n ； Γ ⊢ e₂ ↦ τ₂            →
              --------------------
              n ； Γ ⊢ e₁ & e₂ ↦ τ₁ × τ₂

    ↦π₁  : ∀ {n : ℕ} {Γ : Assms} {e : Exp} {τ τ₁ τ₂ : Typ} →
              n ； Γ ⊢ e ↦ τ              →
              τ ⊔ □ × □ ≡ τ₁ × τ₂         →
              --------------------
              n ； Γ ⊢ π₁ e ↦ τ₁

    ↦π₂  : ∀ {n : ℕ} {Γ : Assms} {e : Exp} {τ τ₁ τ₂ : Typ} →
              n ； Γ ⊢ e ↦ τ              →
              τ ⊔ □ × □ ≡ τ₁ × τ₂         →
              --------------------
              n ； Γ ⊢ π₂ e ↦ τ₂

    ↦case : ∀ {n : ℕ} {Γ : Assms} {e e₁ e₂ : Exp} {τ τ₁ τ₂ τ₁' τ₂' : Typ} →
              n ； Γ ⊢ e ↦ τ                                →
              τ ⊔ □ + □ ≡ τ₁ + τ₂                           →
              n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'                      →
              n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'                      →
              τ₁' ~ τ₂'                                     →
              ----------------------------------
              n ； Γ ⊢ case e of e₁ · e₂ ↦ τ₁' ⊔ τ₂'

  data _；_⊢_↤_ : ℕ → Assms → Exp → Typ → Set where
    ↤Sub  : ∀ {n : ℕ} {Γ : Assms} {e : Exp} {τ τ' : Typ} →
               n ； Γ ⊢ e ↦ τ'            →
               τ ~ τ'                     →
               ----------
               n ； Γ ⊢ e ↤ τ

    ↤λ    : ∀ {n : ℕ} {Γ : Assms} {e : Exp} {τ τ₁ τ₂ : Typ} →
               τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂       →
               n ； (τ₁ ∷ Γ) ⊢ e ↤ τ₂     →
               --------------------
               n ； Γ ⊢ λ⇒ e ↤ τ

    ↤case : ∀ {n : ℕ} {Γ : Assms} {e e₁ e₂ : Exp} {τ τ₁ τ₂ τ' : Typ} →
               n ； Γ ⊢ e ↦ τ             →
               τ ⊔ □ + □ ≡ τ₁ + τ₂        →
               n ； (τ₁ ∷ Γ) ⊢ e₁ ↤ τ'    →
               n ； (τ₂ ∷ Γ) ⊢ e₂ ↤ τ'    →
               --------------------------
               n ； Γ ⊢ case e of e₁ · e₂ ↤ τ'

    ↤ι₁  : ∀ {n : ℕ} {Γ : Assms} {e : Exp} {τ τ₁ τ₂ : Typ} →
              τ ⊔ □ + □ ≡ τ₁ + τ₂         →
              n ； Γ ⊢ e ↤ τ₁             →
              --------------------
              n ； Γ ⊢ ι₁ e ↤ τ

    ↤ι₂  : ∀ {n : ℕ} {Γ : Assms} {e : Exp} {τ τ₁ τ₂ : Typ} →
              τ ⊔ □ + □ ≡ τ₁ + τ₂         →
              n ； Γ ⊢ e ↤ τ₂             →
              --------------------
              n ； Γ ⊢ ι₂ e ↤ τ

    ↤&   : ∀ {n : ℕ} {Γ : Assms} {e₁ e₂ : Exp} {τ τ₁ τ₂ : Typ} →
              τ ⊔ □ × □ ≡ τ₁ × τ₂         →
              n ； Γ ⊢ e₁ ↤ τ₁            →
              n ； Γ ⊢ e₂ ↤ τ₂            →
              --------------------
              n ； Γ ⊢ e₁ & e₂ ↤ τ

    ↤λ:  : ∀ {n : ℕ} {Γ : Assms} {e : Exp} {τ τ₁ τ₂ : Typ} →
              τ ~ τ₁ ⇒ □                  →
              τ ⊔ τ₁ ⇒ □ ≡ τ₁ ⇒ τ₂        →
              n ⊢wf τ₁                    →
              n ； (τ₁ ∷ Γ) ⊢ e ↤ τ₂      →
              ---------------------
              n ； Γ ⊢ λ: τ₁ ⇒ e ↤ τ

    ↤def : ∀ {n : ℕ} {Γ : Assms} {e' e : Exp} {τ' τ : Typ} →
              n ； Γ ⊢ e' ↦ τ'            →
              n ； (τ' ∷ Γ) ⊢ e ↤ τ       →
              --------------------
              n ； Γ ⊢ def e' ⊢ e ↤ τ
