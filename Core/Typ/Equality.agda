module Core.Typ.Equality where

open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_,_; uncurry)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; inspect; [_])
open import Relation.Nullary using (Dec; yes; no; map′)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Core.Typ.Base

_≟_ : (τ τ' : Typ) → Dec (τ ≡ τ')
τ       ≟ τ' with diag τ τ'   | inspect (diag τ) τ'
...                  | kind*   | _     = yes refl
...                  | kind□   | _     = yes refl
⟨ m ⟩   ≟ ⟨ n ⟩     | kindVar | _     = map′ (cong ⟨_⟩)
                                              (λ where refl → refl) (m ≟ℕ n)
τ₁ + τ₂ ≟ τ₁' + τ₂' | kind+   | _     = map′ (uncurry (cong₂ _+_))
                                              (λ where refl → refl , refl)
                                              (τ₁ ≟ τ₁' ×-dec τ₂ ≟ τ₂')
τ₁ × τ₂ ≟ τ₁' × τ₂' | kind×   | _     = map′ (uncurry (cong₂ _×_))
                                              (λ where refl → refl , refl)
                                              (τ₁ ≟ τ₁' ×-dec τ₂ ≟ τ₂')
τ₁ ⇒ τ₂ ≟ τ₁' ⇒ τ₂' | kind⇒   | _     = map′ (uncurry (cong₂ _⇒_))
                                              (λ where refl → refl , refl)
                                              (τ₁ ≟ τ₁' ×-dec τ₂ ≟ τ₂')
∀· τ    ≟ ∀· τ'     | kind∀   | _     = map′ (cong ∀·)
                                              (λ where refl → refl) (τ ≟ τ')
...                  | diff    | [ as ] = no λ where refl → shallow-disequality as
