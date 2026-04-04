module Core.Exp.Equality where

open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_,_; uncurry)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; inspect; [_])
open import Relation.Nullary using (Dec; yes; no; map′)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Core.Typ using (Typ; _≟t_)
open import Core.Exp.Base

_≟e_ : (e e' : Exp) → Dec (e ≡ e')
e         ≟e e'         with diag e e'    | inspect (diag e) e'
...                        | kind□        | _     = yes refl
...                        | kind*        | _     = yes refl
< m >     ≟e < n >         | kindVar      | _     = map′ (cong <_>)
                                                         (λ where refl → refl) (m ≟ n)
(λ· τ ⇒ e₁) ≟e (λ· τ' ⇒ e₁') | kindλ      | _     = map′ (uncurry (cong₂ λ·_⇒_))
                                                         (λ where refl → refl , refl)
                                                         (τ ≟t τ' ×-dec e₁ ≟e e₁')
e₁ ∘ e₂   ≟e e₁' ∘ e₂'     | kind∘        | _     = map′ (uncurry (cong₂ _∘_))
                                                         (λ where refl → refl , refl)
                                                         (e₁ ≟e e₁' ×-dec e₂ ≟e e₂')
e₁ & e₂   ≟e e₁' & e₂'     | kind&        | _     = map′ (uncurry (cong₂ _&_))
                                                         (λ where refl → refl , refl)
                                                         (e₁ ≟e e₁' ×-dec e₂ ≟e e₂')
ιₗ e₁     ≟e ιₗ e₁'        | kindιₗ       | _     = map′ (cong ιₗ)
                                                         (λ where refl → refl) (e₁ ≟e e₁')
ιᵣ e₁     ≟e ιᵣ e₁'        | kindιᵣ       | _     = map′ (cong ιᵣ)
                                                         (λ where refl → refl) (e₁ ≟e e₁')
Λ e₁      ≟e Λ e₁'         | kindΛ        | _     = map′ (cong Λ)
                                                         (λ where refl → refl) (e₁ ≟e e₁')
(def e₁ ⊢ e₂) ≟e (def e₁' ⊢ e₂') | kinddef | _     = map′ (uncurry (cong₂ def_⊢_))
                                                         (λ where refl → refl , refl)
                                                         (e₁ ≟e e₁' ×-dec e₂ ≟e e₂')
...                        | diff         | [ as ] = no λ where refl → shallow-disequality as
