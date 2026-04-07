module Core.Typ.Properties where

open import Core.Typ.Base
open import Core.Typ.Consistency
open import Core.Typ.Precision

-- Precision implies consistency
⊑to~ : ∀ {τ τ'}
     → τ ⊑ τ'     →  τ ~ τ'
⊑to~   ⊑□         =  ~?₂
⊑to~   ⊑*         =  ~*
⊑to~   ⊑Var       =  ~Var
⊑to~  (⊑+ p₁ p₂)  =  ~+ (⊑to~ p₁) (⊑to~ p₂)
⊑to~  (⊑× p₁ p₂)  =  ~× (⊑to~ p₁) (⊑to~ p₂)
⊑to~  (⊑⇒ p₁ p₂)  =  ~⇒ (⊑to~ p₁) (⊑to~ p₂)
⊑to~  (⊑∀ p)      =  ~∀ (⊑to~ p)

-- Slices of the same type are consistent
⊑-consistent : ∀ {τ₁ τ₂ τ}
             → τ₁ ⊑ τ    →  τ₂ ⊑ τ     →  τ₁ ~ τ₂
⊑-consistent   ⊑□           _          =  ~?₂
⊑-consistent   _            ⊑□         =  ~?₁
⊑-consistent   ⊑*           ⊑*         =  ~*
⊑-consistent   ⊑Var         ⊑Var       =  ~Var
⊑-consistent  (⊑+ p₁ p₂)   (⊑+ q₁ q₂)  =  ~+ (⊑-consistent p₁ q₁) (⊑-consistent p₂ q₂)
⊑-consistent  (⊑× p₁ p₂)   (⊑× q₁ q₂)  =  ~× (⊑-consistent p₁ q₁) (⊑-consistent p₂ q₂)
⊑-consistent  (⊑⇒ p₁ p₂)   (⊑⇒ q₁ q₂)  =  ~⇒ (⊑-consistent p₁ q₁) (⊑-consistent p₂ q₂)
⊑-consistent  (⊑∀ p)       (⊑∀ q)      =  ~∀ (⊑-consistent p q)
