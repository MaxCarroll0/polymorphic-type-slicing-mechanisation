module Core.Assms.Lift where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (_∷_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _∧_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Typ
open import Core.Assms.Base
open import Core.Assms.Precision
open import Core.Assms.Lattice
open import Core.Instances

-- Head and tail of assumption list slices

hdₛ : ∀ {τ : Typ} {Γ : Assms} → ⌊ τ ∷ Γ ⌋ → ⌊ τ ⌋
hdₛ (_ isSlice (⊑∷ h _)) = _ isSlice h

tlₛ : ∀ {τ : Typ} {Γ : Assms} → ⌊ τ ∷ Γ ⌋ → ⌊ Γ ⌋
tlₛ (_ isSlice (⊑∷ _ t)) = _ isSlice t

-- Decomposition: γₛ : ⌊ τ ∷ Γ ⌋ propositionally equals (hd ∷ tl) on the carrier.
-- Used to lift derivations parameterised by γₛ .↓ to ones at (hdₛ γₛ .↓ ∷ tlₛ γₛ .↓).
cons-decompₛ : ∀ {τ : Typ} {Γ : Assms} (γₛ : ⌊ τ ∷ Γ ⌋) → γₛ .↓ ≡ hdₛ γₛ .↓ ∷ tlₛ γₛ .↓
cons-decompₛ (_ isSlice (⊑∷ _ _)) = refl

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

-- Cons a type slice onto an assumption slice
_∷ₛ_ : ∀ {τ : Typ} {Γ : Assms} → ⌊ τ ⌋ → ⌊ Γ ⌋ → ⌊ τ ∷ Γ ⌋
(τ' isSlice τ'⊑τ) ∷ₛ (Γ' isSlice Γ'⊑Γ) = (τ' ∷ Γ') isSlice (⊑∷ τ'⊑τ Γ'⊑Γ)

-- Lookup a type slice from an assumption slice by de Bruijn index
_atₛ_ : ∀ {Γ : Assms} {τ : Typ} {k : ℕ} → ⌊ Γ ⌋ → Γ at k ≡ just τ → ⌊ τ ⌋
_atₛ_ {k = zero}  ((_ ∷ _) isSlice (⊑∷ h _)) refl = _ isSlice h
_atₛ_ {k = suc _} ((_ ∷ _) isSlice (⊑∷ _ t)) eq   = (_ isSlice t) atₛ eq

-- Update a type slice at a de Bruijn index
_[_≔_]ₛ : ∀ {Γ : Assms} {τ : Typ} {k : ℕ} → ⌊ Γ ⌋ → Γ at k ≡ just τ → ⌊ τ ⌋ → ⌊ Γ ⌋
_[_≔_]ₛ {k = zero}  ((_ ∷ γ) isSlice (⊑∷ _ t)) refl (τ' isSlice p) = (τ' ∷ γ) isSlice (⊑∷ p t)
_[_≔_]ₛ {k = suc _} ((τ ∷ γ) isSlice (⊑∷ h t)) eq   υ              = (_ isSlice h) ∷ₛ ((_ isSlice t) [ eq ≔ υ ]ₛ)

-- Updating at k then looking up at k on the underlying data
≔ₛ-↓ : ∀ {Γ : Assms} {τ : Typ} {k : ℕ}
        (Φ : ⌊ Γ ⌋) (p : Γ at k ≡ just τ) (υ : ⌊ τ ⌋)
      → (Φ [ p ≔ υ ]ₛ) .↓ at k ≡ just (υ .↓)
≔ₛ-↓ {k = zero}  ((_ ∷ _) isSlice (⊑∷ _ _)) refl _ = refl
≔ₛ-↓ {k = suc _} ((_ ∷ _) isSlice (⊑∷ _ t)) eq   υ = ≔ₛ-↓ (_ isSlice t) eq υ

-- Update is monotone in the base slice
open ⊑ {A = Typ} using () renaming (refl to ⊑t-refl)

≔ₛ-mono : ∀ {Γ : Assms} {τ : Typ} {k : ℕ}
           (Φ₁ Φ₂ : ⌊ Γ ⌋) (p : Γ at k ≡ just τ) (υ : ⌊ τ ⌋)
         → Φ₁ ⊑ₛ Φ₂ → Φ₁ [ p ≔ υ ]ₛ ⊑ₛ Φ₂ [ p ≔ υ ]ₛ
≔ₛ-mono {k = zero}  (_ isSlice (⊑∷ _ _)) (_ isSlice (⊑∷ _ _)) refl _ (⊑∷ _ t) = ⊑∷ ⊑t-refl t
≔ₛ-mono {k = suc _} ((_ ∷ γ₁) isSlice (⊑∷ _ t₁)) ((_ ∷ γ₂) isSlice (⊑∷ _ t₂)) eq υ (⊑∷ h t)
  = ⊑∷ h (≔ₛ-mono (γ₁ isSlice t₁) (γ₂ isSlice t₂) eq υ t)

-- ⊥ₛ with υ at position k is below any slice with ⊒ υ at position k
⊥ₛ-≔-⊑ : ∀ {Γ : Assms} {τ : Typ} {k : ℕ}
          (γₛ : ⌊ Γ ⌋) (p : Γ at k ≡ just τ) (υ : ⌊ τ ⌋)
        → υ ⊑ₛ (γₛ atₛ p)
        → (⊥ₛ {A = Assms} {a = Γ}) [ p ≔ υ ]ₛ ⊑ₛ γₛ
⊥ₛ-≔-⊑ {Γ = _ ∷ Γ'} {k = zero}  ((_ ∷ _) isSlice (⊑∷ _ t)) refl _ υ⊑ = ⊑∷ υ⊑ (⊑ₛLat.⊥ₛ-min {A = Assms} {a = Γ'} (_ isSlice t))
⊥ₛ-≔-⊑ {Γ = _ ∷ _}  {k = suc _} ((_ ∷ γ) isSlice (⊑∷ h t)) eq   υ υ⊑ = ⊑∷ ⊑□ (⊥ₛ-≔-⊑ (γ isSlice t) eq υ υ⊑)

-- Updating at k then looking up at k gives back the value (slice level)
atₛ-≔ₛ : ∀ {Γ : Assms} {τ : Typ} {k : ℕ}
          (Φ : ⌊ Γ ⌋) (p : Γ at k ≡ just τ) (υ : ⌊ τ ⌋)
        → (Φ [ p ≔ υ ]ₛ) atₛ p ≈ₛ υ
atₛ-≔ₛ {k = zero}  ((_ ∷ _) isSlice (⊑∷ _ _)) refl _ = refl
atₛ-≔ₛ {k = suc _} ((_ ∷ _) isSlice (⊑∷ _ t)) eq   υ = atₛ-≔ₛ (_ isSlice t) eq υ
