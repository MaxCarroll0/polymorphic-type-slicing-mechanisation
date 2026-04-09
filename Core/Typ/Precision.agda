module Core.Typ.Precision where

open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; [_])
open import Relation.Nullary using (Dec; yes; no; ¬_; map′)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_,_; uncurry)
open import Function using (_on_)

open import Core.Typ.Base
open import Core.Typ.Equality renaming (_≟_ to _≟t_)
open import Core.Typ.Consistency

-- Precision relation
data _⊑_ : Typ → Typ → Set where
  ⊑□   : ∀ {τ}             →                       □       ⊑ τ
  ⊑*   :                                           *       ⊑ *
  ⊑Var : ∀ {n}             →                       ⟨ n ⟩   ⊑ ⟨ n ⟩
  ⊑+   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑ τ₁' → τ₂ ⊑ τ₂' → τ₁ + τ₂ ⊑ τ₁' + τ₂'
  ⊑×   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑ τ₁' → τ₂ ⊑ τ₂' → τ₁ × τ₂ ⊑ τ₁' × τ₂'
  ⊑⇒   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑ τ₁' → τ₂ ⊑ τ₂' → τ₁ ⇒ τ₂ ⊑ τ₁' ⇒ τ₂'
  ⊑∀   : ∀ {τ τ'}          → τ ⊑ τ'               → ∀· τ    ⊑ ∀· τ'

infix 4 _⊑_

private
  ⊑-refl : Reflexive _⊑_
  ⊑-refl {⟨ _ ⟩}   = ⊑Var
  ⊑-refl {*}       = ⊑*
  ⊑-refl {□}       = ⊑□
  ⊑-refl {_ + _}   = ⊑+ ⊑-refl ⊑-refl
  ⊑-refl {_ × _}   = ⊑× ⊑-refl ⊑-refl
  ⊑-refl {_ ⇒ _}   = ⊑⇒ ⊑-refl ⊑-refl
  ⊑-refl {∀· _}    = ⊑∀ ⊑-refl

  ⊑-trans : Transitive _⊑_
  ⊑-trans ⊑□ _              = ⊑□
  ⊑-trans ⊑* ⊑*             = ⊑*
  ⊑-trans ⊑Var ⊑Var         = ⊑Var
  ⊑-trans (⊑+ p q) (⊑+ r s) = ⊑+ (⊑-trans p r) (⊑-trans q s)
  ⊑-trans (⊑× p q) (⊑× r s) = ⊑× (⊑-trans p r) (⊑-trans q s)
  ⊑-trans (⊑⇒ p q) (⊑⇒ r s) = ⊑⇒ (⊑-trans p r) (⊑-trans q s)
  ⊑-trans (⊑∀ p) (⊑∀ q)     = ⊑∀ (⊑-trans p q)

  ⊑-antisym : Antisymmetric _≡_ _⊑_
  ⊑-antisym ⊑□ ⊑□             = refl
  ⊑-antisym ⊑* ⊑*             = refl
  ⊑-antisym ⊑Var ⊑Var         = refl
  ⊑-antisym (⊑+ p q) (⊑+ r s) = cong₂ _+_ (⊑-antisym p r) (⊑-antisym q s)
  ⊑-antisym (⊑× p q) (⊑× r s) = cong₂ _×_ (⊑-antisym p r) (⊑-antisym q s)
  ⊑-antisym (⊑⇒ p q) (⊑⇒ r s) = cong₂ _⇒_ (⊑-antisym p r) (⊑-antisym q s)
  ⊑-antisym (⊑∀ p) (⊑∀ q)     = cong ∀· (⊑-antisym p q)

  ⊑-isPartialOrder : IsPartialOrder _≡_ _⊑_
  ⊑-isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ where refl → ⊑-refl
      ; trans = ⊑-trans
      }
    ; antisym = ⊑-antisym
    }

  shallow-imprecision : ∀ {τ τ'} → τ ≢ □ → diag τ τ' ≡ diff → ¬(τ ⊑ τ')
  shallow-imprecision τ≢□ _ ⊑□ = τ≢□ refl

_⊑?_ : ∀ τ τ' → Dec (τ ⊑ τ')
τ ⊑? τ'                      with diag τ τ' | Eq.inspect (diag τ) τ'
...                            | kind□   | _    = yes  ⊑□
...                            | kind*   | _    = yes  ⊑*
⟨ m ⟩     ⊑? ⟨ n ⟩             | kindVar | _    = map′ (λ where refl → ⊑Var)
                                                       (λ where ⊑Var → refl) (m ≟ℕ n)
(τ₁ + τ₂) ⊑? (τ₁' + τ₂')       | kind+   | _    = map′ (uncurry ⊑+)
                                                       (λ where (⊑+ p q) → p , q)
                                                       (τ₁ ⊑? τ₁' ×-dec τ₂ ⊑? τ₂')
(τ₁ × τ₂) ⊑? (τ₁' × τ₂')       | kind×   | _    = map′ (uncurry ⊑×)
                                                       (λ where (⊑× p q) → p , q)
                                                       (τ₁ ⊑? τ₁' ×-dec τ₂ ⊑? τ₂')
(τ₁ ⇒ τ₂) ⊑? (τ₁' ⇒ τ₂')       | kind⇒   | _    = map′ (uncurry ⊑⇒)
                                                       (λ where (⊑⇒ p q) → p , q)
                                                       (τ₁ ⊑? τ₁' ×-dec τ₂ ⊑? τ₂')
(∀· τ)    ⊑? (∀· τ')           | kind∀   | _    = map′ ⊑∀ (λ where (⊑∀ p) → p) (τ ⊑? τ')
τ         ⊑? τ'                | diff    | [ as ] with τ ≟t □
...                                                    | yes refl = yes ⊑□
...                                                    | no  τ≢□  = no (shallow-imprecision τ≢□ as)

private 
  ⊑-isDecPartialOrder : IsDecPartialOrder _≡_ _⊑_
  ⊑-isDecPartialOrder = record
                        { isPartialOrder = ⊑-isPartialOrder
                        ; _≟_            = _≟t_
                        ; _≤?_           = _⊑?_
                        }

module ⊑ = IsDecPartialOrder ⊑-isDecPartialOrder
  using (antisym; isPartialOrder; isPreorder; refl; reflexive; trans)
  
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

-- Instantiate generic Slice module for types
open import Core.Slice ⊑-isDecPartialOrder public

import Core.Instances as I
instance typ-precision : I.HasPrecision Typ
         typ-precision = record { _⊑_ = _⊑_ }
