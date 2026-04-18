module Core.Assms.Precision where

open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_,_; uncurry) renaming (_×_ to _∧_)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_)
open import Function using (_on_)

open import Core.Instances
open import Core.Typ
open import Core.Assms.Base
open import Core.Assms.Equality

-- Pointwise precision relation (for equal-length lists)
data _⊑a_ : Assms → Assms → Set where
  ⊑[]  :                                    []       ⊑a []
  ⊑∷   : ∀ {τ τ' Γ Γ'} → τ ⊑ τ' → Γ ⊑a Γ' → (τ ∷ Γ)  ⊑a (τ' ∷ Γ')

infix 4 _⊑a_

private
  ⊑-refl : Reflexive _⊑a_
  ⊑-refl {[]}    = ⊑[]
  ⊑-refl {_ ∷ _} = ⊑∷ ⊑.refl ⊑-refl

  ⊑-trans : Transitive _⊑a_
  ⊑-trans ⊑[]        ⊑[]        = ⊑[]
  ⊑-trans (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊑.trans p₁ p₂) (⊑-trans q₁ q₂)

  ⊑-antisym : Antisymmetric _≡_ _⊑a_
  ⊑-antisym ⊑[]        ⊑[]        = refl
  ⊑-antisym (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = cong₂ _∷_ (⊑.antisym p₁ p₂) (⊑-antisym q₁ q₂)

  ⊑-isPartialOrder : IsPartialOrder _≡_ _⊑a_
  ⊑-isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive     = λ where refl → ⊑-refl
      ; trans         = ⊑-trans
      }
    ; antisym = ⊑-antisym
    }

-- Decidable precision
_⊑a?_ : ∀ Γ Γ' → Dec (Γ ⊑a Γ')
[]      ⊑a? []        = yes ⊑[]
[]      ⊑a? (_ ∷ _)   = no λ ()
(_ ∷ _) ⊑a? []        = no λ ()
(τ ∷ Γ) ⊑a? (τ' ∷ Γ') = map′ (uncurry ⊑∷) (λ where (⊑∷ p q) → p , q)
                            (τ ⊑? τ' ×-dec Γ ⊑a? Γ')
private
  ⊑-isDecPartialOrder : IsDecPartialOrder _≡_ _⊑a_
  ⊑-isDecPartialOrder = record
                      { isPartialOrder = ⊑-isPartialOrder
                      ; _≟_            = _≟_
                      ; _≤?_           = _⊑a?_
                      }

instance
  assms-precision : HasPrecision Assms
  assms-precision = record { _≈_ = _≡_ ; _⊑_ = _⊑a_ ; isDecPartialOrder = ⊑-isDecPartialOrder }

-- Lookup preserves precision
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; _,_; ∃-syntax)

lookup-⊑ : ∀ {Γ₁ Γ₂} {k : ℕ} {τ₂}
           → Γ₁ ⊑ Γ₂ → Γ₂ at k ≡ just τ₂ →
           ∃[ τ₁ ] Γ₁ at k ≡ just τ₁ ∧ τ₁ ⊑ τ₂
lookup-⊑ {k = zero}  (⊑∷ p _) refl = _ , refl , p
lookup-⊑ {k = suc _} (⊑∷ _ q) eq   = lookup-⊑ q eq

-- Shifting preserves precision
open import Core.Assms.Base using (shiftΓ; unshiftΓ)

shiftΓ-⊑ : ∀ {a Γ₁ Γ₂} → Γ₁ ⊑ Γ₂ → shiftΓ a Γ₁ ⊑ shiftΓ a Γ₂
shiftΓ-⊑ ⊑[]      = ⊑[]
shiftΓ-⊑ (⊑∷ p q) = ⊑∷ (shift-⊑ 0 _ p) (shiftΓ-⊑ q)

-- Unshifting preserves precision (analogous to shiftΓ-⊑).
unshiftΓ-⊑ : ∀ {a Γ₁ Γ₂} → Γ₁ ⊑ Γ₂ → unshiftΓ a Γ₁ ⊑ unshiftΓ a Γ₂
unshiftΓ-⊑ ⊑[]      = ⊑[]
unshiftΓ-⊑ (⊑∷ p q) = ⊑∷ (unshift-⊑ 0 _ p) (unshiftΓ-⊑ q)

-- unshiftΓ is a left inverse of shiftΓ.
open import Core.Typ.Properties using (unshift-shift; unshift-shift-⊑)

unshiftΓ-shiftΓ : ∀ {a} (Γ : Assms) → unshiftΓ a (shiftΓ a Γ) ≡ Γ
unshiftΓ-shiftΓ []      = refl
unshiftΓ-shiftΓ (τ ∷ Γ) = cong₂ _∷_ (unshift-shift τ) (unshiftΓ-shiftΓ Γ)

-- unshiftΓ is (half) left adjoint to shiftΓ.
unshiftΓ-shiftΓ-⊑ : ∀ {a Γ Γ'} → Γ' ⊑ shiftΓ a Γ → unshiftΓ a Γ' ⊑ Γ
unshiftΓ-shiftΓ-⊑ {Γ = []}    ⊑[]      = ⊑[]
unshiftΓ-shiftΓ-⊑ {Γ = _ ∷ _} (⊑∷ p q) = ⊑∷ (unshift-shift-⊑ p) (unshiftΓ-shiftΓ-⊑ q)
