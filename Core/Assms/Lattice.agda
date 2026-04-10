open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Maximum; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong₂)
open import Relation.Binary.Lattice.Structures using (IsMeetSemilattice; IsJoinSemilattice; IsLattice; IsBoundedLattice; IsDistributiveLattice)
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum)
open import Function using (_on_)

open import Core.Instances
open import Core.Typ hiding (□)
open import Core.Assms.Base
open import Core.Assms.Precision

module Core.Assms.Lattice where

-- Pointwise meet and join
-- TODO: consider returning Maybe Assms to distinguish meet/join failure from []
private
  _⊓a_ : Assms → Assms → Assms
  []       ⊓a []         = []
  (τ ∷ Γ₁) ⊓a (τ' ∷ Γ₂)  = (τ ⊓ τ') ∷ (Γ₁ ⊓a Γ₂)
  _        ⊓a _          = []

  infixl 6 _⊓a_

  _⊔a_ : Assms → Assms → Assms
  []       ⊔a []         = []
  (τ ∷ Γ₁) ⊔a (τ' ∷ Γ₂)  = (τ ⊔ τ') ∷ (Γ₁ ⊔a Γ₂)
  _        ⊔a _          = []

  infixl 6 _⊔a_

  -- Meet lower bounds
  ⊓-lb₁ : ∀ {γ₁ γ₂ Γ} → γ₁ ⊑ Γ → γ₂ ⊑ Γ → γ₁ ⊓a γ₂ ⊑ γ₁
  ⊓-lb₁  ⊑[]        ⊑[]       = ⊑[]
  ⊓-lb₁ (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊑ₛLat.x⊓ₛy⊑ₛx (↑ p₁) (↑ p₂)) (⊓-lb₁ q₁ q₂)

  ⊓-lb₂ : ∀ {γ₁ γ₂ Γ} → γ₁ ⊑ Γ → γ₂ ⊑ Γ → γ₁ ⊓a γ₂ ⊑ γ₂
  ⊓-lb₂  ⊑[]        ⊑[]       = ⊑[]
  ⊓-lb₂ (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊑ₛLat.x⊓ₛy⊑ₛy (↑ p₁) (↑ p₂)) (⊓-lb₂ q₁ q₂)

  -- Note extra γₙ ⊑ Γ assumptions
  ⊓-glb : ∀ {Γ γ γ₁ γ₂} → γ₁ ⊑ Γ → γ₂ ⊑ Γ → γ ⊑ γ₁ → γ ⊑ γ₂ → γ ⊑ γ₁ ⊓a γ₂
  ⊓-glb  ⊑[]          ⊑[]          ⊑[]        ⊑[]       = ⊑[]
  ⊓-glb (⊑∷ p₁' q₁') (⊑∷ p₂' q₂') (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) =
    ⊑∷ (⊑ₛLat.⊓ₛ-greatest {x = ↑ (⊑.trans {A = Typ} p₁ p₁')} {↑ p₁'} {↑ p₂'} p₁ p₂)
       (⊓-glb q₁' q₂' q₁ q₂)

  -- Join upper bounds
  ⊔-ub₁ : ∀ {γ₁ γ₂ Γ} → γ₁ ⊑ Γ → γ₂ ⊑ Γ → γ₁ ⊑  γ₁ ⊔a γ₂
  ⊔-ub₁  ⊑[]        ⊑[]       = ⊑[]
  ⊔-ub₁ (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊑ₛLat.x⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊔-ub₁ q₁ q₂)

  ⊔-ub₂ : ∀ {γ₁ γ₂ Γ} → γ₁ ⊑ Γ → γ₂ ⊑ Γ → γ₂ ⊑  γ₁ ⊔a γ₂
  ⊔-ub₂  ⊑[]        ⊑[]       = ⊑[]
  ⊔-ub₂ (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊑ₛLat.y⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊔-ub₂ q₁ q₂)

  ⊔-lub : ∀ {Γ γ₁ γ₂} → γ₁ ⊑ Γ → γ₂ ⊑ Γ → γ₁ ⊔a γ₂ ⊑ Γ
  ⊔-lub  ⊑[]        ⊑[]       = ⊑[]
  ⊔-lub (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) =
    ⊑∷ (⊑ₛLat.⊔ₛ-least {x = ↑ p₁} {↑ p₂} {⊤ₛ}  p₁ p₂)
       (⊔-lub q₁ q₂)

-- Register meet/join instances (no HasMeetSemilattice for Assms)
instance
  assms-meet : HasMeet Assms
  assms-meet = record { _⊓_ = _⊓a_ ; closure = λ p q → ⊑.trans {A = Assms} (⊓-lb₁ p q) p }
  assms-join : HasJoin Assms
  assms-join = record { _⊔_ = _⊔a_ ; closure = ⊔-lub }

private
  □-min-slice : ∀ {Γ : Assms} → ⌊ Γ ⌋
  □-min-slice {Γ} = □ (length Γ) isSlice □-min
    where
    □-min : ∀ {Γ : Assms} → □ (length Γ) ⊑ Γ
    □-min {[]}    = ⊑[]
    □-min {_ ∷ Γ} = ⊑∷ ⊑□ □-min

  ⊥ₛ' : ∀ {Γ : Assms} → ⌊ Γ ⌋
  ⊥ₛ' = □-min-slice

  ⊥ₛ-min : ∀ {Γ : Assms} → Minimum (_⊑ₛ_ {A = Assms} {a = Γ}) ⊥ₛ'
  ⊥ₛ-min (_ isSlice ⊑[])     = ⊑[]
  ⊥ₛ-min (_ isSlice (⊑∷ _ q)) = ⊑∷ ⊑□ (⊥ₛ-min (_ isSlice q))

  ⊔ₛ-ub₁ : ∀ {Γ : Assms} (γ₁ γ₂ : ⌊ Γ ⌋) → γ₁ ⊑ₛ (γ₁ ⊔ₛ γ₂)
  ⊔ₛ-ub₁ γ₁ γ₂ = ⊔-ub₁ (γ₁ .proof) (γ₂ .proof)

  ⊔ₛ-ub₂ : ∀ {Γ : Assms} (γ₁ γ₂ : ⌊ Γ ⌋) → γ₂ ⊑ₛ (γ₁ ⊔ₛ γ₂)
  ⊔ₛ-ub₂ γ₁ γ₂ = ⊔-ub₂ (γ₁ .proof) (γ₂ .proof)

  ⊓ₛ-distribˡ-⊔ₛ' : ∀ {Γ : Assms} (υ₁ υ₂ υ₃ : ⌊ Γ ⌋) → (υ₁ ⊓ₛ (υ₂ ⊔ₛ υ₃)) ≈ₛ ((υ₁ ⊓ₛ υ₂) ⊔ₛ (υ₁ ⊓ₛ υ₃))
  ⊓ₛ-distribˡ-⊔ₛ' (_ isSlice ⊑[]) (_ isSlice ⊑[]) (_ isSlice ⊑[]) = refl
  ⊓ₛ-distribˡ-⊔ₛ' (γ₁ isSlice ⊑∷ p₁ q₁) (γ₂ isSlice ⊑∷ p₂ q₂) (γ₃ isSlice ⊑∷ p₃ q₃)
    = cong₂ _∷_ (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ p₁) (↑ p₂) (↑ p₃))
                (⊓ₛ-distribˡ-⊔ₛ' (↑ q₁) (↑ q₂) (↑ q₃))

instance
  assms-sliceLattice : SliceLattice Assms
  assms-sliceLattice = record
    { ⊥ₛ = ⊥ₛ'
    ; ⊥ₛ-min = ⊥ₛ-min
    ; x⊓ₛy⊑ₛx = λ s₁ s₂ → ⊓-lb₁ (s₁ .proof) (s₂ .proof)
    ; x⊓ₛy⊑ₛy = λ s₁ s₂ → ⊓-lb₂ (s₁ .proof) (s₂ .proof)
    ; ⊓ₛ-greatest = λ {_} {s} {s₁} {s₂} p q → ⊓-glb (s₁ .proof) (s₂ .proof) p q
    ; x⊑ₛx⊔ₛy = ⊔ₛ-ub₁
    ; y⊑ₛx⊔ₛy = ⊔ₛ-ub₂
    ; ⊓ₛ-distribˡ-⊔ₛ = ⊓ₛ-distribˡ-⊔ₛ'
    }
