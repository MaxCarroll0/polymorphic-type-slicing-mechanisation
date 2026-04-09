module Core.Assms.Equality where

open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (≡-dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)

open import Core.Typ using (Typ)
open import Core.Typ.Equality renaming (_≟_ to _≟t_)
open import Core.Assms.Base

_≟_ : (Γ Γ' : Assms) → Dec (Γ ≡ Γ')
_≟_ = ≡-dec _≟t_

import Core.Instances as I
instance assms-decEq : I.HasDecEq Assms
         assms-decEq = record { _≟_ = _≟_ }
