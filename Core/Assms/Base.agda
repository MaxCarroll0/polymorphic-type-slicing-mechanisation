module Core.Assms.Base where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)

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

shiftΓ : ℕ → Assms → Assms
shiftΓ a = map (shift 0 a)

unshiftΓ : ℕ → Assms → Assms
unshiftΓ a = map (unshift 0 a)
