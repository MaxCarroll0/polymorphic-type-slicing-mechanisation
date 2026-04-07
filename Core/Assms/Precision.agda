module Core.Assms.Precision where

open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_,_; uncurry)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_)
open import Function using (_on_)

open import Core.Typ using (Typ)
  renaming (⊑□ to ⊑t□; _⊑_ to _⊑t_; _⊑?_ to _⊑t?_;
            module ⊑ to ⊑t)
open import Core.Assms.Base
open import Core.Assms.Equality


-- Pointwise precision relation (for equal-length lists)
data _⊑_ : Assms → Assms → Set where
  ⊑[]  :                                    []       ⊑ []
  ⊑∷   : ∀ {τ τ' Γ Γ'} → τ ⊑t τ' → Γ ⊑ Γ' → (τ ∷ Γ)  ⊑ (τ' ∷ Γ')

infix 4 _⊑_

private
  ⊑-refl : Reflexive _⊑_
  ⊑-refl {[]}    = ⊑[]
  ⊑-refl {_ ∷ _} = ⊑∷ ⊑t.refl ⊑-refl

  ⊑-trans : Transitive _⊑_
  ⊑-trans ⊑[]        ⊑[]        = ⊑[]
  ⊑-trans (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊑t.trans p₁ p₂) (⊑-trans q₁ q₂)

  ⊑-antisym : Antisymmetric _≡_ _⊑_
  ⊑-antisym ⊑[]        ⊑[]        = refl
  ⊑-antisym (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = cong₂ _∷_ (⊑t.antisym p₁ p₂) (⊑-antisym q₁ q₂)

  ⊑-isPartialOrder : IsPartialOrder _≡_ _⊑_
  ⊑-isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive     = λ where refl → ⊑-refl
      ; trans         = ⊑-trans
      }
    ; antisym = ⊑-antisym
    }

-- Decidable precision
_⊑?_ : ∀ Γ Γ' → Dec (Γ ⊑ Γ')
[]      ⊑? []        = yes ⊑[]
[]      ⊑? (_ ∷ _)   = no λ ()
(_ ∷ _) ⊑? []        = no λ ()
(τ ∷ Γ) ⊑? (τ' ∷ Γ') = map′ (uncurry ⊑∷) (λ where (⊑∷ p q) → p , q)
                            (τ ⊑t? τ' ×-dec Γ ⊑? Γ')
private 
  ⊑-isDecPartialOrder : IsDecPartialOrder _≡_ _⊑_
  ⊑-isDecPartialOrder = record
                        { isPartialOrder = ⊑-isPartialOrder
                          ; _≟_            = _≟_
                        ; _≤?_           = _⊑?_
                        }

module ⊑ = IsDecPartialOrder ⊑-isDecPartialOrder using (antisym; isPartialOrder; isPreorder; refl; reflexive; trans)

open import Slice ⊑-isDecPartialOrder public
