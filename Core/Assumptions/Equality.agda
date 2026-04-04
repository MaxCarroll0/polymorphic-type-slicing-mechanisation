module Core.Assumptions.Equality where

open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (≡-dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)

open import Core.Typ using (_≟t_)
open import Core.Assumptions.Base

_≟Γ_ : (Γ Γ' : Assumptions) → Dec (Γ ≡ Γ')
_≟Γ_ = ≡-dec _≟t_
