-- Zone condition induction lemmas for the Kleene fixed-point iteration.
module Slicing.Synthesis.ZoneInduction where

open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst) renaming (refl to ≡refl; sym to ≡sym)
open import Core
open import Core.Typ.Injection

module ZoneProps {τ₁' τ₂' : Typ} (c : τ₁' ~ τ₂') (υ : ⌊ τ₁' ⊔ τ₂' ⌋) where

  private τ = τ₁' ⊔ τ₂'

  open ⊑ₛLat {a = τ}
  open ⊑ₛ {a = τ}

  -- Given IH: R(ψ₂) ⊑ υ ⊓ ¬L(ψ₁_prev) and L(ψ₁') ⊑ L(ψ₁_prev),
  -- show: R(ψ₂) ⊔ (υ ⊓ ¬L(ψ₁')) ⊑ υ ⊓ ¬L(ψ₁')
  zone₂-inductive : ∀ (ψ₁_prev ψ₁' : ⌊ τ₁' ⌋) (ψ₂ : ⌊ τ₂' ⌋)
    → R c ψ₂ ⊑ₛ (υ ⊓ₛ (¬ₛ (L c ψ₁_prev)))
    → L c ψ₁' ⊑ₛ L c ψ₁_prev
    → (R c ψ₂) ⊔ₛ (υ ⊓ₛ (¬ₛ (L c ψ₁'))) ⊑ₛ (υ ⊓ₛ (¬ₛ (L c ψ₁')))
  zone₂-inductive ψ₁_prev ψ₁' ψ₂ ih ψ₁'⊑prev =
    let rhs = υ ⊓ₛ (¬ₛ (L c ψ₁'))
        Rψ₂⊑υ = begin R c ψ₂                 ⊑⟨ ih ⟩
                      υ ⊓ₛ (¬ₛ (L c ψ₁_prev)) ⊑⟨ x⊓ₛy⊑ₛx υ (¬ₛ (L c ψ₁_prev)) ⟩
                      υ                      ∎
        Rψ₂⊑¬new = begin R c ψ₂                 ⊑⟨ ih ⟩
                         υ ⊓ₛ (¬ₛ (L c ψ₁_prev)) ⊑⟨ x⊓ₛy⊑ₛy υ (¬ₛ (L c ψ₁_prev)) ⟩
                         ¬ₛ (L c ψ₁_prev)        ⊑⟨ ¬ₛ-anti ψ₁'⊑prev ⟩
                         ¬ₛ (L c ψ₁')            ∎
    in ⊔ₛ-least {x = R c ψ₂} {y = rhs} {z = rhs}
      (⊓ₛ-greatest {x = R c ψ₂} {y = υ} {z = ¬ₛ (L c ψ₁')} Rψ₂⊑υ Rψ₂⊑¬new)
      (refl {x = rhs})

  zone₁-direct : ∀ (ψ₂ : ⌊ τ₂' ⌋)
    → (υ ⊓ₛ (¬ₛ (R c ψ₂))) ⊑ₛ (υ ⊓ₛ (¬ₛ (R c ψ₂)))
  zone₁-direct ψ₂ = refl {x = υ ⊓ₛ (¬ₛ (R c ψ₂))}
