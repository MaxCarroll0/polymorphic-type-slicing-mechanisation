module Core.Typ.Properties where

open import Core.Typ.Base
open import Core.Typ.Consistency
open import Core.Typ.Precision

-- Precision implies consistency
⊑to~ : ∀ {τ τ'} → τ ⊑t τ' → τ ~ τ'
⊑to~ ⊑?         = ~?ₗ
⊑to~ ⊑*         = ~*
⊑to~ ⊑Var       = ~Var
⊑to~ (⊑+ p₁ p₂) = ~+ (⊑to~ p₁) (⊑to~ p₂)
⊑to~ (⊑× p₁ p₂) = ~× (⊑to~ p₁) (⊑to~ p₂)
⊑to~ (⊑⇒ p₁ p₂) = ~⇒ (⊑to~ p₁) (⊑to~ p₂)
⊑to~ (⊑∀ p)     = ~∀ (⊑to~ p)

-- Slices of the same type are consistent
⊑t-consistent : ∀ {τ₁ τ₂ τ} → τ₁ ⊑t τ → τ₂ ⊑t τ → τ₁ ~ τ₂
⊑t-consistent ⊑?             _              = ~?ₗ
⊑t-consistent _              ⊑?             = ~?ᵣ
⊑t-consistent ⊑*             ⊑*             = ~*
⊑t-consistent ⊑Var           ⊑Var           = ~Var
⊑t-consistent (⊑+ p₁ p₂)     (⊑+ q₁ q₂)     = ~+ (⊑t-consistent p₁ q₁) (⊑t-consistent p₂ q₂)
⊑t-consistent (⊑× p₁ p₂)     (⊑× q₁ q₂)     = ~× (⊑t-consistent p₁ q₁) (⊑t-consistent p₂ q₂)
⊑t-consistent (⊑⇒ p₁ p₂)     (⊑⇒ q₁ q₂)     = ~⇒ (⊑t-consistent p₁ q₁) (⊑t-consistent p₂ q₂)
⊑t-consistent (⊑∀ p)         (⊑∀ q)         = ~∀ (⊑t-consistent p q)
