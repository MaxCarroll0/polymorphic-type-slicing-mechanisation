module Core.Exp.Equality where

open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_,_; uncurry)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; inspect; [_])
open import Relation.Nullary using (Dec; yes; no; map′)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Core.Instances
open import Core.Typ
open import Core.Exp.Base

private
  _≟e_ : (e e' : Exp) → Dec (e ≡ e')
e             ≟e e'                     with diag e e' | inspect (diag e) e'
...                                        | kind□     | _    = yes refl
...                                        | kind*     | _    = yes refl
⟨ m ⟩         ≟e ⟨ n ⟩                     | kindVar   | _    = map′ (cong ⟨_⟩)
                                                                    (λ where refl → refl) (m ≟ℕ n)
(λ: τ ⇒ e₁)   ≟e (λ: τ' ⇒ e₁')             | kindλ     | _    = map′ (uncurry (cong₂ λ:_⇒_))
                                                                    (λ where refl → refl , refl)
                                                                    (τ ≟ τ' ×-dec e₁ ≟e e₁')
(λ⇒ e₁)       ≟e (λ⇒ e₁')                  | kindλu    | _    = map′ (cong λ⇒_)
                                                                    (λ where refl → refl) (e₁ ≟e e₁')
e₁ ∘ e₂       ≟e e₁' ∘ e₂'                 | kind∘     | _    = map′ (uncurry (cong₂ _∘_))
                                                                    (λ where refl → refl , refl)
                                                                    (e₁ ≟e e₁' ×-dec e₂ ≟e e₂')
(e₁ < τ >)    ≟e (e₁' < τ' >)              | kind<>    | _    = map′ (uncurry (cong₂ _<_>))
                                                                    (λ where refl → refl , refl)
                                                                    (e₁ ≟e e₁' ×-dec τ ≟ τ')
e₁ & e₂       ≟e e₁' & e₂'                 | kind&     | _    = map′ (uncurry (cong₂ _&_))
                                                                    (λ where refl → refl , refl)
                                                                    (e₁ ≟e e₁' ×-dec e₂ ≟e e₂')
ι₁ e₁         ≟e ι₁ e₁'                    | kindι₁    | _    = map′ (cong ι₁)
                                                                    (λ where refl → refl) (e₁ ≟e e₁')
ι₂ e₁         ≟e ι₂ e₁'                    | kindι₂    | _    = map′ (cong ι₂)
                                                                    (λ where refl → refl) (e₁ ≟e e₁')
(case e of e₁ · e₂) ≟e (case e' of e₁' · e₂') | kindcase | _ =
                                                            map′ (λ where (refl , refl , refl) → refl)
                                                                 (λ where refl → refl , refl , refl)
                                                                 (e ≟e e' ×-dec e₁ ≟e e₁' ×-dec e₂ ≟e e₂')
π₁ e₁         ≟e π₁ e₁'                    | kindπ₁    | _    = map′ (cong π₁)
                                                                    (λ where refl → refl) (e₁ ≟e e₁')
π₂ e₁         ≟e π₂ e₁'                    | kindπ₂    | _    = map′ (cong π₂)
                                                                    (λ where refl → refl) (e₁ ≟e e₁')
Λ e₁          ≟e Λ e₁'                     | kindΛ     | _    = map′ (cong Λ)
                                                                    (λ where refl → refl) (e₁ ≟e e₁')
(def e₁ ⊢ e₂) ≟e (def e₁' ⊢ e₂')           | kinddef   | _    = map′ (uncurry (cong₂ def_⊢_))
                                                                    (λ where refl → refl , refl)
                                                                    (e₁ ≟e e₁' ×-dec e₂ ≟e e₂')
...                                       | diff      | [ as ] = no λ where refl → shallow-disequality as

instance exp-decEq : HasDecEq Exp
         exp-decEq = record { _≟_ = _≟e_ }
