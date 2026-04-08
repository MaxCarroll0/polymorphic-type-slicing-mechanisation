open import Data.Nat hiding (_+_)
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Core
open import Agda.Builtin.FromNat using (Number; fromNat)

module Semantics.Statics.Typing where

infix  4 _⊢_↦_
infix  4 _⊢_↤_
-- TODO: better notation than using ↦ and ↤. i.e. ⇑ and ⇓
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

    ↦λ:  : ∀ {Γ : Assms} {e : Exp} {τ₁ τ₂ : Typ} →
              (τ₁ ∷ Γ) ⊢ e ↦ τ₂                  →
              -- TODO: inherently well-scoped terms or a well-formedness judgement Γ ⊢ τ
              ------------------
              Γ ⊢ λ: τ₁ ⇒ e ↦ τ₁ ⇒ τ₂

    ↦def : ∀ {Γ : Assms} {e' e : Exp} {τ' τ : Typ} →
              Γ ⊢ e' ↦ τ'                          →
              (τ' ∷ Γ) ⊢ e ↦ τ                     →
              -----------------
              Γ ⊢ def e' ⊢ e ↦ τ

    ↦Λ   : ∀ {Γ : Assms} {e : Exp} {τ : Typ} →
             --(0 ∷ Γ) ⊢ e ↦ τ               → -- Representing type vars by ⟨ 0 ⟩. ALSO, fix instance resolution for 0 to ⟨ 0 ⟩. Also, well scoping needed???
             ---------------
             Γ ⊢ Λ e ↦ ∀· τ

    ↦∘   : ∀ {Γ : Assms} {e₁ e₂ : Exp} {τ τ₁ τ₂ : Typ} →
              Γ ⊢ e₁ ↦ τ                               →
              τ ~ □ ⇒ □                                → -- TODO: Make join default to □ meaning that this assumption is unneeded (i.e. any inconsistent joins cannot be decomposed). For completeness prove that τ ⊔t □ ⇒ □ ≡ τ₁ ⇒ τ₂ if and only if τ ~ □ ⇒ □. And similarly for other compound types.
              τ ⊔t □ ⇒ □ ≡ τ₁ ⇒ τ₂                     →
              Γ ⊢ e₂ ↤ τ₁                              →
              --------------------
              Γ ⊢ e₁ ∘ e₂ ↦ τ₂

    ↦<>  : ∀ {Γ : Assms} {e : Exp} {τ τ' σ : Typ} →
              Γ ⊢ e ↦ τ                           →
              τ ~ ∀· □                            →
              τ ⊔t ∀· □ ≡ ∀· τ'                   →
              --------------------------
              Γ ⊢ e < σ > ↦ [ zero ↦ σ ] τ'

    ↦&   : ∀ {Γ : Assms} {e₁ e₂ : Exp} {τ₁ τ₂ : Typ} →
              Γ ⊢ e₁ ↦ τ₁                              →
              Γ ⊢ e₂ ↦ τ₂                              →
              --------------------
              Γ ⊢ e₁ & e₂ ↦ τ₁ × τ₂

    ↦π₁  : ∀ {Γ : Assms} {e : Exp} {τ τ₁ τ₂ : Typ} →
              Γ ⊢ e ↦ τ                            →
              τ ~ □ × □                            →
              τ ⊔t □ × □ ≡ τ₁ × τ₂                 →
              --------------------
              Γ ⊢ π₁ e ↦ τ₁

    ↦π₂  : ∀ {Γ : Assms} {e : Exp} {τ τ₁ τ₂ : Typ} →
              Γ ⊢ e ↦ τ                            →
              τ ~ □ × □                            →
              τ ⊔t □ × □ ≡ τ₁ × τ₂                 →
              --------------------
              Γ ⊢ π₂ e ↦ τ₂

    ↦case : ∀ {Γ : Assms} {e e₁ e₂ : Exp} {τ τ₁ τ₂ τ₁' τ₂' : Typ} →
              Γ ⊢ e ↦ τ                                           →
              τ ~ □ + □                                           →
              τ ⊔t □ + □ ≡ τ₁ + τ₂                                →
              (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'                                 →
              (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'                                 →
              τ₁' ~ τ₂'                                           →
              ----------------------------------
              Γ ⊢ case e of e₁ · e₂ ↦ τ₁' ⊔t τ₂'

  data _⊢_↤_ : Assms → Exp → Typ → Set where
    ↤Sub  : ∀ {Γ : Assms} {e : Exp} {τ τ' : Typ} →
               Γ ⊢ e ↦ τ'                        →
               τ ~ τ'                            →
               ----------
               Γ ⊢ e ↤ τ

    ↤λ    : ∀ {Γ : Assms} {e : Exp} {τ τ₁ τ₂ : Typ} →
               τ ~ □ ⇒ □                            →
               τ ⊔t □ ⇒ □ ≡ τ₁ ⇒ τ₂                 →
               (τ₁ ∷ Γ) ⊢ e ↤ τ₂                    →
               --------------------
               Γ ⊢ λ⇒ e ↤ τ

    ↤case : ∀ {Γ : Assms} {e e₁ e₂ : Exp} {τ τ₁ τ₂ τ' : Typ} →
               Γ ⊢ e ↦ τ                                     →
               τ ~ □ + □                                     →
               τ ⊔t □ + □ ≡ τ₁ + τ₂                          →
               (τ₁ ∷ Γ) ⊢ e₁ ↤ τ'                            → 
               (τ₂ ∷ Γ) ⊢ e₂ ↤ τ'                            →
               --------------------------
               Γ ⊢ case e of e₁ · e₂ ↤ τ'

    ↤ι₁  : ∀ {Γ : Assms} {e : Exp} {τ τ₁ τ₂ : Typ} →
              τ ~ □ + □                            →
              τ ⊔t □ + □ ≡ τ₁ + τ₂                 →
              Γ ⊢ e ↤ τ₁                           →
              --------------------
              Γ ⊢ ι₁ e ↤ τ

    ↤ι₂  : ∀ {Γ : Assms} {e : Exp} {τ τ₁ τ₂ : Typ} →
              τ ~ □ + □                            →
              τ ⊔t □ + □ ≡ τ₁ + τ₂                 →
              Γ ⊢ e ↤ τ₂                           →
              --------------------
              Γ ⊢ ι₂ e ↤ τ

    ↤&   : ∀ {Γ : Assms} {e₁ e₂ : Exp} {τ τ₁ τ₂ : Typ} →
              τ ~ □ × □                                →
              τ ⊔t □ × □ ≡ τ₁ × τ₂                     →
              Γ ⊢ e₁ ↤ τ₁                              →
              Γ ⊢ e₂ ↤ τ₂                              →
              --------------------
              Γ ⊢ e₁ & e₂ ↤ τ

    ↤λ:  : ∀ {Γ : Assms} {e : Exp} {τ τ₁ τ₂ : Typ} →
              τ ~ τ₁ ⇒ □                           →
              τ ⊔t τ₁ ⇒ □ ≡ τ₁ ⇒ τ₂                →
              (τ₁ ∷ Γ) ⊢ e ↤ τ₂                    →
              ---------------------
              Γ ⊢ λ: τ₁ ⇒ e ↤ τ

    ↤def : ∀ {Γ : Assms} {e' e : Exp} {τ' τ : Typ} →
              Γ ⊢ e' ↦ τ'                          →
              (τ' ∷ Γ) ⊢ e ↤ τ                     →
              --------------------
              Γ ⊢ def e' ⊢ e ↤ τ
