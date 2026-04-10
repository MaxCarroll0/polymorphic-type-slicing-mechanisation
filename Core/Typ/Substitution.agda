module Core.Typ.Substitution where

open import Data.Nat using (ℕ; zero; suc; _≟_; _<ᵇ_; _∸_) renaming (_+_ to _ℕ+_)
open import Data.Bool using (true; false)
open import Relation.Nullary using (yes; no)

open import Core.Typ.Base

-- Shift free type variables, for use when entering typefuns 
shift : ℕ → ℕ → Typ → Typ
shift c a ⟨ k ⟩     with k <ᵇ c
...                 | true  = ⟨ k ⟩
...                 | false = ⟨ k ℕ+ a ⟩
shift c a *         = *
shift c a □         = □
shift c a (τ₁ + τ₂) = shift c a τ₁ + shift c a τ₂
shift c a (τ₁ × τ₂) = shift c a τ₁ × shift c a τ₂
shift c a (τ₁ ⇒ τ₂) = shift c a τ₁ ⇒ shift c a τ₂
shift c a (∀· τ)    = ∀· (shift (suc c) a τ)

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
