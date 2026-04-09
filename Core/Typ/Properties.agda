module Core.Typ.Properties where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Core.Typ.Base
open import Core.Typ.Equality
open import Core.Typ.Consistency
open import Core.Typ.Precision
open import Core.Typ.Lattice

-- Decomposable join implies consistency with least specific compound type
⊔-⇒-~ : ∀ {τ τ₁ τ₂} → τ ⊔ (□ ⇒ □) ≡ τ₁ ⇒ τ₂ → τ ~ □ ⇒ □
⊔-⇒-~ {τ} eq with diag τ (□ ⇒ □)
⊔-⇒-~ {_ ⇒ _} _ | kind⇒ = ~⇒ ~?₁ ~?₁
⊔-⇒-~ {τ}    eq | diff with τ ≟ □  | (□ ⇒ □) ≟ □
...                     | yes refl | _       = ~?₂
...                     | no _     | yes ()
...                     | no _     | no _    with eq
...                                             | ()

⊔-+-~ : ∀ {τ τ₁ τ₂} → τ ⊔ (□ + □) ≡ τ₁ + τ₂ → τ ~ □ + □
⊔-+-~ {τ} eq with diag τ (□ + □)
⊔-+-~ {_ + _} _ | kind+ = ~+ ~?₁ ~?₁
⊔-+-~ {τ}    eq | diff with τ ≟ □  | (□ + □) ≟ □
...                     | yes refl | _       = ~?₂
...                     | no _     | yes ()
...                     | no _     | no _    with eq
...                                             | ()

⊔-×-~ : ∀ {τ τ₁ τ₂} → τ ⊔ (□ × □) ≡ τ₁ × τ₂ → τ ~ □ × □
⊔-×-~ {τ} eq with diag τ (□ × □)
⊔-×-~ {_ × _} _ | kind× = ~× ~?₁ ~?₁
⊔-×-~ {τ}    eq | diff with τ ≟ □ | (□ × □) ≟ □
...                    | yes refl | _       = ~?₂
...                    | no _     | yes ()
...                    | no _     | no _    with eq
...                                            | ()

⊔-∀-~ : ∀ {τ τ'} → τ ⊔ (∀· □) ≡ ∀· τ' → τ ~ ∀· □
⊔-∀-~ {τ} eq with diag τ (∀· □)
⊔-∀-~ {∀· _} _ | kind∀ = ~∀ ~?₁
⊔-∀-~ {τ}   eq | diff with τ ≟ □ | (∀· □) ≟ □
...                   | yes refl | _       = ~?₂
...                   | no _     | yes ()
...                   | no _     | no _    with eq
...                                           | ()
