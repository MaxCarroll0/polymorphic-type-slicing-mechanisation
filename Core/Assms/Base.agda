module Core.Assms.Base where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)

open import Core.Typ using (Typ)
open import Core.Typ.Base as TypBase using () renaming (□ to □t)

Assms : Set
Assms = List Typ

-- TODO: Maybe use vectors?
-- Lookup by de Bruijn index
_[_] : Assms → ℕ → Maybe Typ
[]       [ _ ]     = nothing
(τ ∷ _)  [ zero ]  = just τ
(_ ∷ Γ)  [ suc n ] = Γ [ n ]

□ : ℕ → Assms
□ zero    = []
□ (suc n) = □t ∷ □ n
