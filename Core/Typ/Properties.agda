module Core.Typ.Properties where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)

open import Core.Typ.Base
open import Core.Typ.Equality
open import Core.Typ.Consistency
open import Core.Typ.Precision
open import Core.Typ.Lattice
open import Core.Instances

-- □ is a zero object
⊔t-zeroₗ : ∀ (τ : Typ) → □ ⊔ τ ≡ τ
⊔t-zeroₗ τ with diag □ τ
⊔t-zeroₗ .□   | kind□ = refl
⊔t-zeroₗ τ    | diff = refl

⊔t-zeroᵣ : ∀ (τ : Typ) → τ ⊔ □ ≡ τ
⊔t-zeroᵣ τ with diag τ □
⊔t-zeroᵣ .□   | kind□ = refl
⊔t-zeroᵣ τ    | diff with τ ≟ □
...                    | yes refl = refl
...                    | no  _    = refl

⊓t-zeroₗ : ∀ (τ : Typ) → □ ⊓ τ ≡ □
⊓t-zeroₗ τ with diag □ τ
⊓t-zeroₗ .□   | kind□ = refl
⊓t-zeroₗ _    | diff  = refl

⊓t-zeroᵣ : ∀ (τ : Typ) → τ ⊓ □ ≡ □
⊓t-zeroᵣ τ with diag τ □
⊓t-zeroᵣ .□   | kind□ = refl
⊓t-zeroᵣ _    | diff  = refl

-- Non-trivial join implies consistency with least specific compound type
⊔-⇒-~ : ∀ {τ τ₁ τ₂} → τ ⊔ (□ ⇒ □) ≡ τ₁ ⇒ τ₂ → τ ~ □ ⇒ □
⊔-⇒-~ {τ} eq with diag τ (□ ⇒ □)
⊔-⇒-~     _     | kind⇒ = ~⇒ ~?₁ ~?₁
⊔-⇒-~ {τ} eq    | diff with τ ≟ □  
...                       | yes refl = ~?₂
⊔-⇒-~     ()    | diff    | no  _    

⊔-+-~ : ∀ {τ τ₁ τ₂} → τ ⊔ (□ + □) ≡ τ₁ + τ₂ → τ ~ □ + □
⊔-+-~ {τ} eq with diag τ (□ + □)
⊔-+-~     _     | kind+ = ~+ ~?₁ ~?₁
⊔-+-~ {τ} eq    | diff with τ ≟ □
...                       | yes refl = ~?₂
⊔-+-~     ()    | diff    | no _

⊔-×-~ : ∀ {τ τ₁ τ₂} → τ ⊔ (□ × □) ≡ τ₁ × τ₂ → τ ~ □ × □
⊔-×-~ {τ} eq with diag τ (□ × □)
⊔-×-~     _     | kind× = ~× ~?₁ ~?₁
⊔-×-~ {τ} eq    | diff with τ ≟ □
...                       | yes refl = ~?₂
⊔-×-~     ()    | diff    | no _

⊔-∀-~ : ∀ {τ τ'} → τ ⊔ (∀· □) ≡ ∀· τ' → τ ~ ∀· □
⊔-∀-~ {τ} eq with diag τ (∀· □)
⊔-∀-~     _     | kind∀ = ~∀ ~?₁
⊔-∀-~ {τ} eq    | diff with τ ≟ □
...                       | yes refl = ~?₂
⊔-∀-~     ()    | diff    | no _
