open import Data.Nat
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Core

module Semantics.Statics.Typing where

mutual
  data _⊢_⇒_ : Assms → Exp → Typ → Set where
    ⇒*   : ∀ {Γ : Ctx} →
           -------------
              Γ ⊢ * ⇒ *
              
    ⇒Var : ∀ {Γ : Assms} {n : ℕ} {τ : Typ} →
             (Γ [ n ]) ≡ just τ          →
             ------------------
              Γ ⊢ n ⇒ τ


  data _⊢_⇐_ : Ctx → Exp → Typ → Set where

infix  4 _⊢_⇒_
infix  4 _⊢_⇐_
