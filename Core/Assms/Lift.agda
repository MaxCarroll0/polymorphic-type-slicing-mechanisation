module Core.Assms.Lift where

open import Data.Nat using (ℕ)
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Core.Typ
open import Core.Assms.Base
open import Core.Assms.Precision
open import Core.Instances

-- Head and tail of assumption list slices

hdₛ : ∀ {τ : Typ} {Γ : Assms} → ⌊ τ ∷ Γ ⌋ → ⌊ τ ⌋
hdₛ (_ isSlice (⊑∷ h _)) = _ isSlice h

tlₛ : ∀ {τ : Typ} {Γ : Assms} → ⌊ τ ∷ Γ ⌋ → ⌊ Γ ⌋
tlₛ (_ isSlice (⊑∷ _ t)) = _ isSlice t

-- Head/tail respect precision
hdₛ-⊑ : ∀ {τ Γ τ' Γ'} (γₛ : ⌊ τ ∷ Γ ⌋) → γₛ .↓ ⊑a (τ' ∷ Γ') → hdₛ γₛ .↓ ⊑ τ'
hdₛ-⊑ (_ isSlice (⊑∷ _ _)) (⊑∷ h _) = h

tlₛ-⊑ : ∀ {τ Γ τ' Γ'} (γₛ : ⌊ τ ∷ Γ ⌋) → γₛ .↓ ⊑a (τ' ∷ Γ') → tlₛ γₛ .↓ ⊑a Γ'
tlₛ-⊑ (_ isSlice (⊑∷ _ _)) (⊑∷ _ t) = t

-- Shift/unshift on assumption slices

unshiftΓₛ : ∀ {Γ a} → ⌊ shiftΓ a Γ ⌋ → ⌊ Γ ⌋
unshiftΓₛ {a = a} (γ isSlice γ⊑) = unshiftΓ a γ isSlice unshiftΓ-shiftΓ-⊑ γ⊑

shiftΓₛ : ∀ {Γ a} → ⌊ Γ ⌋ → ⌊ shiftΓ a Γ ⌋
shiftΓₛ {a = a} (γ isSlice γ⊑) = shiftΓ a γ isSlice shiftΓ-⊑ γ⊑

unshift-shiftΓₛ : ∀ {Γ a} (γₛ : ⌊ Γ ⌋) → unshiftΓₛ {a = a} (shiftΓₛ γₛ) ≈ₛ γₛ
unshift-shiftΓₛ (γ isSlice _) = unshiftΓ-shiftΓ γ

shift-unshiftΓ : ∀ {a Γ} (γ : Assms) → γ ⊑a shiftΓ a Γ → shiftΓ a (unshiftΓ a γ) ≡ γ
shift-unshiftΓ = shiftΓ-unshiftΓ

shift-unshiftΓₛ : ∀ {Γ a} (γₛ : ⌊ shiftΓ a Γ ⌋) → shiftΓₛ (unshiftΓₛ γₛ) ≈ₛ γₛ
shift-unshiftΓₛ {a = a} (γ isSlice γ⊑) = shift-unshiftΓ γ γ⊑
