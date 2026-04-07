module Core.Exp.Precision where

open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_,_; uncurry)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; [_])
open import Relation.Nullary using (Dec; yes; no; ¬_; map′)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Function using (_on_)

open import Core.Typ using (Typ)
  renaming (⊑□ to ⊑t□; _⊑_ to _⊑t_; _⊑?_ to _⊑t?_;
            module ⊑ to ⊑t)
open import Core.Exp.Base
open import Core.Exp.Equality renaming (_≟_ to _≟e_)

-- Precision relation for expressions
data _⊑_ : Exp → Exp → Set where
  ⊑□   : ∀ {e}              →                          □           ⊑ e
  ⊑*   :                                               *           ⊑ *
  ⊑Var : ∀ {n}              →                          ⟨ n ⟩       ⊑ ⟨ n ⟩
  ⊑λ   : ∀ {τ τ' e e'}      →  τ  ⊑t τ'  → e  ⊑ e'   → λ· τ ⇒ e    ⊑ λ· τ' ⇒ e'
  ⊑∘   : ∀ {e₁ e₂ e₁' e₂'}  →  e₁ ⊑  e₁' → e₂ ⊑ e₂'  →  e₁ ∘ e₂    ⊑ e₁' ∘ e₂'
  ⊑&   : ∀ {e₁ e₂ e₁' e₂'}  →  e₁ ⊑  e₁' → e₂ ⊑ e₂'  → e₁ & e₂     ⊑ e₁' & e₂'
  ⊑ι₁  : ∀ {e e'}           →  e  ⊑  e'              → ι₁ e        ⊑ ι₁ e'
  ⊑ι₂  : ∀ {e e'}           →  e  ⊑  e'              → ι₂ e        ⊑ ι₂ e'
  ⊑Λ   : ∀ {e e'}           →  e  ⊑  e'              → Λ e         ⊑ Λ e'
  ⊑def : ∀ {e₁ e₂ e₁' e₂'}  →  e₁ ⊑  e₁' → e₂ ⊑ e₂'  → def e₁ ⊢ e₂ ⊑ def e₁' ⊢ e₂'

infix 4 _⊑_

private
  ⊑-refl : Reflexive _⊑_
  ⊑-refl {□}        = ⊑□
  ⊑-refl {*}        = ⊑*
  ⊑-refl {⟨ _ ⟩}    = ⊑Var
  ⊑-refl {λ· _ ⇒ _} = ⊑λ ⊑t.refl ⊑-refl
  ⊑-refl {_ ∘ _}    = ⊑∘ ⊑-refl ⊑-refl
  ⊑-refl {_ & _}    = ⊑& ⊑-refl ⊑-refl
  ⊑-refl {ι₁ _}     = ⊑ι₁ ⊑-refl
  ⊑-refl {ι₂ _}     = ⊑ι₂ ⊑-refl
  ⊑-refl {Λ _}      = ⊑Λ ⊑-refl
  ⊑-refl {def _ ⊢ _}   = ⊑def ⊑-refl ⊑-refl

  ⊑-trans : Transitive _⊑_
  ⊑-trans ⊑□ _                  = ⊑□
  ⊑-trans ⊑* ⊑*                 = ⊑*
  ⊑-trans ⊑Var ⊑Var             = ⊑Var
  ⊑-trans (⊑λ p q) (⊑λ r s)     = ⊑λ (⊑t.trans p r) (⊑-trans q s)
  ⊑-trans (⊑∘ p q) (⊑∘ r s)     = ⊑∘ (⊑-trans p r) (⊑-trans q s)
  ⊑-trans (⊑& p q) (⊑& r s)     = ⊑& (⊑-trans p r) (⊑-trans q s)
  ⊑-trans (⊑ι₁ p) (⊑ι₁ q)       = ⊑ι₁ (⊑-trans p q)
  ⊑-trans (⊑ι₂ p) (⊑ι₂ q)       = ⊑ι₂ (⊑-trans p q)
  ⊑-trans (⊑Λ p) (⊑Λ q)         = ⊑Λ (⊑-trans p q)
  ⊑-trans (⊑def p q) (⊑def r s) = ⊑def (⊑-trans p r) (⊑-trans q s)

  ⊑-antisym : Antisymmetric _≡_ _⊑_
  ⊑-antisym ⊑□ ⊑□                 = refl
  ⊑-antisym ⊑* ⊑*                 = refl
  ⊑-antisym ⊑Var ⊑Var             = refl
  ⊑-antisym (⊑λ p q) (⊑λ r s)     = cong₂ λ·_⇒_ (⊑t.antisym p r) (⊑-antisym q s)
  ⊑-antisym (⊑∘ p q) (⊑∘ r s)     = cong₂ _∘_ (⊑-antisym p r) (⊑-antisym q s)
  ⊑-antisym (⊑& p q) (⊑& r s)     = cong₂ _&_ (⊑-antisym p r) (⊑-antisym q s)
  ⊑-antisym (⊑ι₁ p) (⊑ι₁ q)       = cong ι₁ (⊑-antisym p q)
  ⊑-antisym (⊑ι₂ p) (⊑ι₂ q)       = cong ι₂ (⊑-antisym p q)
  ⊑-antisym (⊑Λ p) (⊑Λ q)         = cong Λ (⊑-antisym p q)
  ⊑-antisym (⊑def p q) (⊑def r s) = cong₂ def_⊢_ (⊑-antisym p r) (⊑-antisym q s)

  ⊑-isPartialOrder : IsPartialOrder _≡_ _⊑_
  ⊑-isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ where refl → ⊑-refl
      ; trans = ⊑-trans
      }
    ; antisym = ⊑-antisym
    }

  shallow-imprecision : ∀ {e e'} → e ≢ □ → diag e e' ≡ diff → ¬(e ⊑ e')
  shallow-imprecision e≢□ _ ⊑□ = e≢□ refl

-- Decidable precision
_⊑?_ : ∀ e e' → Dec (e ⊑ e')
e ⊑? e'                       with diag e e' | Eq.inspect (diag e) e'
...                              | kind□     | _    = yes ⊑□
...                              | kind*     | _    = yes ⊑*
⟨ m ⟩        ⊑? ⟨ n ⟩            | kindVar   | _    = map′ (λ where refl → ⊑Var)
                                                           (λ where ⊑Var → refl) (m ≟ℕ n)
(λ· τ ⇒ e₁)  ⊑? (λ· τ' ⇒ e₁')    | kindλ     | _    = map′ (uncurry ⊑λ)
                                                           (λ where (⊑λ p q) → p , q)
                                                           (τ ⊑t? τ' ×-dec e₁ ⊑? e₁')
(e₁ ∘ e₂)    ⊑? (e₁' ∘ e₂')      | kind∘     | _    = map′ (uncurry ⊑∘)
                                                           (λ where (⊑∘ p q) → p , q)
                                                           (e₁ ⊑? e₁' ×-dec e₂ ⊑? e₂')
(e₁ & e₂)    ⊑? (e₁' & e₂')      | kind&     | _    = map′ (uncurry ⊑&)
                                                           (λ where (⊑& p q) → p , q)
                                                           (e₁ ⊑? e₁' ×-dec e₂ ⊑? e₂')
(ι₁ e₁)      ⊑? (ι₁ e₁')         | kindι₁    | _    = map′ ⊑ι₁ (λ where (⊑ι₁ p) → p) (e₁ ⊑? e₁')
(ι₂ e₁)      ⊑? (ι₂ e₁')         | kindι₂    | _    = map′ ⊑ι₂ (λ where (⊑ι₂ p) → p) (e₁ ⊑? e₁')
(Λ e₁)       ⊑? (Λ e₁')          | kindΛ     | _    = map′ ⊑Λ (λ where (⊑Λ p) → p) (e₁ ⊑? e₁')
(def e₁ ⊢ e₂) ⊑? (def e₁' ⊢ e₂') | kinddef   | _    = map′ (uncurry ⊑def)
                                                           (λ where (⊑def p q) → p , q)
                                                           (e₁ ⊑? e₁' ×-dec e₂ ⊑? e₂')
e            ⊑? e'               | diff      | [ as ] with e ≟e □
...                                                      | yes refl = yes ⊑□
...                                                      | no  e≢□  = no (shallow-imprecision e≢□ as)

private 
  ⊑-isDecPartialOrder : IsDecPartialOrder _≡_ _⊑_
  ⊑-isDecPartialOrder = record
                        { isPartialOrder = ⊑-isPartialOrder
                        ; _≟_            = _≟e_
                        ; _≤?_           = _⊑?_
                        }

module ⊑ = IsDecPartialOrder ⊑-isDecPartialOrder using (antisym; isPartialOrder; isPreorder; refl; reflexive; trans)

-- Instantiate generic Slice module for expressions
open import Slice ⊑-isDecPartialOrder public
