module Core.Assms.Base where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Typ using (Typ)
open import Core.Typ.Base as TypBase using () renaming (□ to □t)
open import Core.Typ.Substitution using (shift; unshift)

Assms : Set
Assms = List Typ

-- TODO: Maybe use vectors?
-- Lookup by de Bruijn index
_at_ : Assms → ℕ → Maybe Typ
[]      at _     = nothing
(τ ∷ _) at zero  = just τ
(_ ∷ Γ) at suc n = Γ at n

□ : ℕ → Assms
□ zero    = []
□ (suc n) = □t ∷ □ n

_[_≔_] : Assms → ℕ → Typ → Assms
[]       [ _     ≔ _ ] = []
(τ ∷ Γ) [ zero  ≔ τ' ] = τ' ∷ Γ
(τ ∷ Γ) [ suc n ≔ τ' ] = τ ∷ (Γ [ n ≔ τ' ])

-- Updating at k and looking up at k gives back the new value
at-≔ : ∀ (Γ : Assms) (k : ℕ) {τ} → (p : Γ at k ≡ just τ) → (τ' : Typ) → (Γ [ k ≔ τ' ]) at k ≡ just τ'
at-≔ (_ ∷ _) zero    refl _ = refl
at-≔ (_ ∷ Γ) (suc k) p    τ' = at-≔ Γ k p τ'

shiftΓ : ℕ → Assms → Assms
shiftΓ a = map (shift 0 a)

unshiftΓ : ℕ → Assms → Assms
unshiftΓ a = map (unshift 0 a)
