module Semantics.Dynamics.Ground where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Core.Typ using (Typ; □; *; _⇒_; _+_; _×_; ∀·)

-- Ground types: the "skeleton" forms — one level of structure with □ leaves
data Ground : Typ → Set where
  ground*  :                Ground *
  ground⇒  :                Ground (□ ⇒ □)
  ground+  :                Ground (□ + □)
  ground×  :                Ground (□ × □)
  ground∀  :                Ground (∀· □)

-- Ground matching: map non-ground, non-□ types to their ground skeleton
data _▸g_ : Typ → Typ → Set where
  match⇒  : ∀ {τ₁ τ₂}  →  τ₁ ⇒ τ₂ ≢ □ ⇒ □  →  τ₁ ⇒ τ₂ ▸g □ ⇒ □
  match+  : ∀ {τ₁ τ₂}  →  τ₁ + τ₂ ≢ □ + □   →  τ₁ + τ₂ ▸g □ + □
  match×  : ∀ {τ₁ τ₂}  →  τ₁ × τ₂ ≢ □ × □   →  τ₁ × τ₂ ▸g □ × □
  match∀  : ∀ {τ}      →  ∀· τ ≢ ∀· □        →  ∀· τ    ▸g ∀· □

infix 4 _▸g_
