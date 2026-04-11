module Core.Typ.Precision where

open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; [_])
open import Relation.Nullary using (Dec; yes; no; ¬_; map′)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_,_; uncurry)
open import Function using (_on_)

-- TODO: create the lifted instances in Core.Slice to avoid name clashes
open import Core.Instances
open import Core.Typ.Base
open import Core.Typ.Equality
open import Core.Typ.Consistency

-- Precision relation
data _⊑t_ : Typ → Typ → Set where
  ⊑□   : ∀ {τ}             →                       □       ⊑t τ
  ⊑*   :                                           *       ⊑t *
  ⊑Var : ∀ {n}             →                       ⟨ n ⟩   ⊑t ⟨ n ⟩
  ⊑+   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ + τ₂ ⊑t τ₁' + τ₂'
  ⊑×   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ × τ₂ ⊑t τ₁' × τ₂'
  ⊑⇒   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ ⇒ τ₂ ⊑t τ₁' ⇒ τ₂'
  ⊑∀   : ∀ {τ τ'}          → τ ⊑t τ'               → ∀· τ    ⊑t ∀· τ'

infix 4 _⊑t_

private
  ⊑-refl : Reflexive _⊑t_
  ⊑-refl {⟨ _ ⟩}   = ⊑Var
  ⊑-refl {*}       = ⊑*
  ⊑-refl {□}       = ⊑□
  ⊑-refl {_ + _}   = ⊑+ ⊑-refl ⊑-refl
  ⊑-refl {_ × _}   = ⊑× ⊑-refl ⊑-refl
  ⊑-refl {_ ⇒ _}   = ⊑⇒ ⊑-refl ⊑-refl
  ⊑-refl {∀· _}    = ⊑∀ ⊑-refl

  ⊑-trans : Transitive _⊑t_
  ⊑-trans ⊑□ _              = ⊑□
  ⊑-trans ⊑* ⊑*             = ⊑*
  ⊑-trans ⊑Var ⊑Var         = ⊑Var
  ⊑-trans (⊑+ p q) (⊑+ r s) = ⊑+ (⊑-trans p r) (⊑-trans q s)
  ⊑-trans (⊑× p q) (⊑× r s) = ⊑× (⊑-trans p r) (⊑-trans q s)
  ⊑-trans (⊑⇒ p q) (⊑⇒ r s) = ⊑⇒ (⊑-trans p r) (⊑-trans q s)
  ⊑-trans (⊑∀ p) (⊑∀ q)     = ⊑∀ (⊑-trans p q)

  ⊑-antisym : Antisymmetric _≡_ _⊑t_
  ⊑-antisym ⊑□ ⊑□             = refl
  ⊑-antisym ⊑* ⊑*             = refl
  ⊑-antisym ⊑Var ⊑Var         = refl
  ⊑-antisym (⊑+ p q) (⊑+ r s) = cong₂ _+_ (⊑-antisym p r) (⊑-antisym q s)
  ⊑-antisym (⊑× p q) (⊑× r s) = cong₂ _×_ (⊑-antisym p r) (⊑-antisym q s)
  ⊑-antisym (⊑⇒ p q) (⊑⇒ r s) = cong₂ _⇒_ (⊑-antisym p r) (⊑-antisym q s)
  ⊑-antisym (⊑∀ p) (⊑∀ q)     = cong ∀· (⊑-antisym p q)

  ⊑-isPartialOrder : IsPartialOrder _≡_ _⊑t_
  ⊑-isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ where refl → ⊑-refl
      ; trans = ⊑-trans
      }
    ; antisym = ⊑-antisym
    }

  shallow-imprecision : ∀ {τ τ'} → τ ≢ □ → diag τ τ' ≡ diff → ¬(τ ⊑t τ')
  shallow-imprecision τ≢□ _ ⊑□ = τ≢□ refl

  _⊑t?_ : ∀ τ τ' → Dec (τ ⊑t τ')
  τ ⊑t? τ'                      with diag τ τ' | Eq.inspect (diag τ) τ'
  ...                            | kind□   | _    = yes  ⊑□
  ...                            | kind*   | _    = yes  ⊑*
  ⟨ m ⟩     ⊑t? ⟨ n ⟩             | kindVar | _    = map′ (λ where refl → ⊑Var)
                                                          (λ where ⊑Var → refl) (m ≟ℕ n)
  (τ₁ + τ₂) ⊑t? (τ₁' + τ₂')       | kind+   | _    = map′ (uncurry ⊑+)
                                                          (λ where (⊑+ p q) → p , q)
                                                          (τ₁ ⊑t? τ₁' ×-dec τ₂ ⊑t? τ₂')
  (τ₁ × τ₂) ⊑t? (τ₁' × τ₂')       | kind×   | _    = map′ (uncurry ⊑×)
                                                          (λ where (⊑× p q) → p , q)
                                                          (τ₁ ⊑t? τ₁' ×-dec τ₂ ⊑t? τ₂')
  (τ₁ ⇒ τ₂) ⊑t? (τ₁' ⇒ τ₂')       | kind⇒   | _    = map′ (uncurry ⊑⇒)
                                                          (λ where (⊑⇒ p q) → p , q)
                                                          (τ₁ ⊑t? τ₁' ×-dec τ₂ ⊑t? τ₂')
  (∀· τ)    ⊑t? (∀· τ')           | kind∀   | _    = map′ ⊑∀ (λ where (⊑∀ p) → p) (τ ⊑t? τ')
  τ         ⊑t? τ'                | diff    | [ as ] with τ ≟ □
  ...                                                    | yes refl = yes ⊑□
  ...                                                    | no  τ≢□  = no (shallow-imprecision τ≢□ as)

  ⊑-isDecPartialOrder : IsDecPartialOrder _≡_ _⊑t_
  ⊑-isDecPartialOrder = record
                        { isPartialOrder = ⊑-isPartialOrder
                        ; _≟_            = _≟_
                        ; _≤?_           = _⊑t?_
                        }


-- TODO: Move to Typ.Properties
-- Precision implies consistency
⊑to~ : ∀ {τ τ'}
     → τ ⊑t τ'     →  τ ~ τ'
⊑to~   ⊑□         =  ~?₂
⊑to~   ⊑*         =  ~*
⊑to~   ⊑Var       =  ~Var
⊑to~  (⊑+ p₁ p₂)  =  ~+ (⊑to~ p₁) (⊑to~ p₂)
⊑to~  (⊑× p₁ p₂)  =  ~× (⊑to~ p₁) (⊑to~ p₂)
⊑to~  (⊑⇒ p₁ p₂)  =  ~⇒ (⊑to~ p₁) (⊑to~ p₂)
⊑to~  (⊑∀ p)      =  ~∀ (⊑to~ p)

-- Slices of the same type are consistent
⊑-consistent : ∀ {τ₁ τ₂ τ}
             → τ₁ ⊑t τ    →  τ₂ ⊑t τ     →  τ₁ ~ τ₂
⊑-consistent   ⊑□           _          =  ~?₂
⊑-consistent   _            ⊑□         =  ~?₁
⊑-consistent   ⊑*           ⊑*         =  ~*
⊑-consistent   ⊑Var         ⊑Var       =  ~Var
⊑-consistent  (⊑+ p₁ p₂)   (⊑+ q₁ q₂)  =  ~+ (⊑-consistent p₁ q₁) (⊑-consistent p₂ q₂)
⊑-consistent  (⊑× p₁ p₂)   (⊑× q₁ q₂)  =  ~× (⊑-consistent p₁ q₁) (⊑-consistent p₂ q₂)
⊑-consistent  (⊑⇒ p₁ p₂)   (⊑⇒ q₁ q₂)  =  ~⇒ (⊑-consistent p₁ q₁) (⊑-consistent p₂ q₂)
⊑-consistent  (⊑∀ p)       (⊑∀ q)      =  ~∀ (⊑-consistent p q)

instance
  typ-precision : HasPrecision Typ
  typ-precision = record { _≈_ = _≡_ ; _⊑_ = _⊑t_ ; isDecPartialOrder = ⊑-isDecPartialOrder }
