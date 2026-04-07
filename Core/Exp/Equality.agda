module Core.Exp.Equality where

open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_,_; uncurry)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; inspect; [_])
open import Relation.Nullary using (Dec; yes; no; map′)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Core.Typ using (Typ) renaming (_≟_ to _≟t_)
open import Core.Exp.Base

_≟_ : (e e' : Exp) → Dec (e ≡ e')
e             ≟ e'           with diag e e' | inspect (diag e) e'
...                             | kind□     | _    = yes refl
...                             | kind*     | _    = yes refl
< m >         ≟ < n >           | kindVar   | _    = map′ (cong <_>)
                                                           (λ where refl → refl) (m ≟ℕ n)
(λ· τ ⇒ e₁)   ≟ (λ· τ' ⇒ e₁')   | kindλ     | _    = map′ (uncurry (cong₂ λ·_⇒_))
                                                           (λ where refl → refl , refl)
                                                           (τ ≟t τ' ×-dec e₁ ≟ e₁')
e₁ ∘ e₂       ≟ e₁' ∘ e₂'       | kind∘     | _    = map′ (uncurry (cong₂ _∘_))
                                                           (λ where refl → refl , refl)
                                                           (e₁ ≟ e₁' ×-dec e₂ ≟ e₂')
e₁ & e₂       ≟ e₁' & e₂'       | kind&     | _    = map′ (uncurry (cong₂ _&_))
                                                           (λ where refl → refl , refl)
                                                           (e₁ ≟ e₁' ×-dec e₂ ≟ e₂')
ι₁ e₁         ≟ ι₁ e₁'          | kindι₁    | _    = map′ (cong ι₁)
                                                           (λ where refl → refl) (e₁ ≟ e₁')
ι₂ e₁         ≟ ι₂ e₁'          | kindι₂    | _    = map′ (cong ι₂)
                                                           (λ where refl → refl) (e₁ ≟ e₁')
Λ e₁          ≟ Λ e₁'           | kindΛ     | _    = map′ (cong Λ)
                                                           (λ where refl → refl) (e₁ ≟ e₁')
(def e₁ ⊢ e₂) ≟ (def e₁' ⊢ e₂') | kinddef   | _    = map′ (uncurry (cong₂ def_⊢_))
                                                           (λ where refl → refl , refl)
                                                           (e₁ ≟ e₁' ×-dec e₂ ≟ e₂')
...                              | diff      | [ as ] = no λ where refl → shallow-disequality as
