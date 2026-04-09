module Core.Instances where

open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

record HasDecEq (A : Set) : Set where
  field _≟_ : (x y : A) → Dec (x ≡ y)
open HasDecEq ⦃...⦄ public

record HasPrecision (A : Set) : Set₁ where
  field _⊑_ : A → A → Set
open HasPrecision ⦃...⦄ public

record HasMeet (A : Set) : Set where
  field _⊓_ : A → A → A
open HasMeet ⦃...⦄ public

record HasJoin (A : Set) : Set where
  field _⊔_ : A → A → A
open HasJoin ⦃...⦄ public
