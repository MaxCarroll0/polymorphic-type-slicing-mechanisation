module Core.Typ.Equality where

open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_,_; uncurry)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; inspect; [_])
open import Relation.Nullary using (Dec; yes; no; map′)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Core.Typ.Base

_≟t_ : (τ τ' : Typ) → Dec (τ ≡ τ')
τ       ≟t τ' with diag τ τ'   | inspect (diag τ) τ'
...                  | kind*   | _     = yes refl
...                  | kind□   | _     = yes refl
⟨ m ⟩   ≟t ⟨ n ⟩     | kindVar | _     = map′ (cong ⟨_⟩)
                                              (λ where refl → refl) (m ≟ n)
τ₁ + τ₂ ≟t τ₁' + τ₂' | kind+   | _     = map′ (uncurry (cong₂ _+_))
                                              (λ where refl → refl , refl)
                                              (τ₁ ≟t τ₁' ×-dec τ₂ ≟t τ₂')
τ₁ × τ₂ ≟t τ₁' × τ₂' | kind×   | _     = map′ (uncurry (cong₂ _×_))
                                              (λ where refl → refl , refl)
                                              (τ₁ ≟t τ₁' ×-dec τ₂ ≟t τ₂')
τ₁ ⇒ τ₂ ≟t τ₁' ⇒ τ₂' | kind⇒   | _     = map′ (uncurry (cong₂ _⇒_))
                                              (λ where refl → refl , refl)
                                              (τ₁ ≟t τ₁' ×-dec τ₂ ≟t τ₂')
∀· τ    ≟t ∀· τ'     | kind∀   | _     = map′ (cong ∀·)
                                              (λ where refl → refl) (τ ≟t τ')
...                  | diff    | [ as ] = no λ where refl → shallow-disequality as
