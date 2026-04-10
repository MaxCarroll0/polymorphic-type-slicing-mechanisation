module Core.Assms.Equality where

open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (≡-dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)

open import Core.Instances
open import Core.Typ
open import Core.Assms.Base

private
  _≟a_ : (Γ Γ' : Assms) → Dec (Γ ≡ Γ')
  _≟a_ = ≡-dec _≟_

instance assms-decEq : HasDecEq Assms
         assms-decEq = record { _≟_ = _≟a_ }
