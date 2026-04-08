module Core.Typ.Substitution where

open import Data.Nat using (ℕ; zero; suc; _≟_; _<ᵇ_; _∸_)
open import Data.Bool using (true; false)
open import Relation.Nullary using (yes; no)

open import Core.Typ.Base

private
  -- de Bruijn substitution
  sub : ℕ → Typ → Typ → Typ
  sub n σ ⟨ m ⟩     with m ≟ n
  ...                  | yes _ = σ
  ...                  | no  _ with m <ᵇ n
  ...                             | true  = ⟨ m ⟩
  ...                             | false = ⟨ m ∸ 1 ⟩
  sub n σ *         = *
  sub n σ □         = □
  sub n σ (τ₁ + τ₂) = sub n σ τ₁ + sub n σ τ₂
  sub n σ (τ₁ × τ₂) = sub n σ τ₁ × sub n σ τ₂
  sub n σ (τ₁ ⇒ τ₂) = sub n σ τ₁ ⇒ sub n σ τ₂
  sub n σ (∀· τ)    = ∀· (sub (suc n) σ τ)

[_↦_]_ : ℕ → Typ → Typ → Typ
[_↦_]_ = sub
