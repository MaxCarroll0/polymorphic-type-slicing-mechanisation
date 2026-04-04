module Core.Assumptions.Base where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)

open import Core.Typ using (Typ; □)

-- Typing assumptions (Γ) are lists of types
Assumptions : Set
Assumptions = List Typ

-- Lookup by de Bruijn index
_[_] : Assumptions → ℕ → Maybe Typ
[]       [ _ ]     = nothing
(τ ∷ _)  [ zero ]  = just τ
(_ ∷ Γ)  [ suc n ] = Γ [ n ]

-- Bottom: list of □s of given length
□Γ : ℕ → Assumptions
□Γ zero    = []
□Γ (suc n) = □ ∷ □Γ n
