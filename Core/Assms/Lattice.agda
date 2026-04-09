open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Maximum; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong₂)
open import Relation.Binary.Lattice.Structures using (IsMeetSemilattice; IsJoinSemilattice; IsLattice; IsBoundedLattice; IsDistributiveLattice)
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum)
open import Function using (_on_)

open import Core.Typ using (Typ)
  renaming (⊑□ to ⊑t□; _⊑_ to _⊑t_; _⊓_ to _⊓t_; _⊔_ to _⊔t_;
            module ⊑ₛLat to ⊑tₛLat; module ⊑ to ⊑t; module ⊑ₛ to ⊑tₛ;
            _isSlice_ to _isSlicet_; ↑ to ↑t)
open import Core.Assms.Base
open import Core.Assms.Precision renaming (⊤ₛ to ⊤ₛ')

module Core.Assms.Lattice where

-- Pointwise meet and join
-- TODO: consider returning Maybe Assms to distinguish meet/join failure from []
_⊓_ : Assms → Assms → Assms
[]       ⊓ []         = []
(τ ∷ Γ₁) ⊓ (τ' ∷ Γ₂)  = (τ ⊓t τ') ∷ (Γ₁ ⊓ Γ₂)
_        ⊓ _          = []

infixl 6 _⊓_

_⊔_ : Assms → Assms → Assms
[]       ⊔ []         = []
(τ ∷ Γ₁) ⊔ (τ' ∷ Γ₂)  = (τ ⊔t τ') ∷ (Γ₁ ⊔ Γ₂)
_        ⊔ _          = []

infixl 6 _⊔_

private
  -- Meet lower bounds
  ⊓-lb₁ : ∀ {γ₁ γ₂ Γ} → γ₁ ⊑ Γ → γ₂ ⊑ Γ → γ₁ ⊓ γ₂ ⊑ γ₁
  ⊓-lb₁  ⊑[]        ⊑[]       = ⊑[]
  ⊓-lb₁ (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊑tₛLat.x⊓ₛy⊑ₛx (↑t p₁) (↑t p₂)) (⊓-lb₁ q₁ q₂)

  ⊓-lb₂ : ∀ {γ₁ γ₂ Γ} → γ₁ ⊑ Γ → γ₂ ⊑ Γ → γ₁ ⊓ γ₂ ⊑ γ₂
  ⊓-lb₂  ⊑[]        ⊑[]       = ⊑[]
  ⊓-lb₂ (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊑tₛLat.x⊓ₛy⊑ₛy (↑t p₁) (↑t p₂)) (⊓-lb₂ q₁ q₂)

  -- Note extra γₙ ⊑ Γ assumptions
  ⊓-glb : ∀ {Γ γ γ₁ γ₂} → γ₁ ⊑ Γ → γ₂ ⊑ Γ → γ ⊑ γ₁ → γ ⊑ γ₂ → γ ⊑ γ₁ ⊓ γ₂
  ⊓-glb  ⊑[]          ⊑[]          ⊑[]        ⊑[]       = ⊑[]
  ⊓-glb (⊑∷ p₁' q₁') (⊑∷ p₂' q₂') (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) =
    ⊑∷ (⊑tₛLat.⊓ₛ-greatest {x = ↑t (⊑t.trans p₁ p₁')} {↑t p₁'} {↑t p₂'} p₁ p₂)
       (⊓-glb q₁' q₂' q₁ q₂)

  -- Join upper bounds
  ⊔-ub₁ : ∀ {γ₁ γ₂ Γ} → γ₁ ⊑ Γ → γ₂ ⊑ Γ → γ₁ ⊑  γ₁ ⊔ γ₂
  ⊔-ub₁  ⊑[]        ⊑[]       = ⊑[]
  ⊔-ub₁ (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊑tₛLat.x⊑ₛx⊔ₛy (↑t p₁) (↑t p₂)) (⊔-ub₁ q₁ q₂)

  ⊔-ub₂ : ∀ {γ₁ γ₂ Γ} → γ₁ ⊑ Γ → γ₂ ⊑ Γ → γ₂ ⊑  γ₁ ⊔ γ₂
  ⊔-ub₂  ⊑[]        ⊑[]       = ⊑[]
  ⊔-ub₂ (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊑tₛLat.y⊑ₛx⊔ₛy (↑t p₁) (↑t p₂)) (⊔-ub₂ q₁ q₂)

  ⊔-lub : ∀ {Γ γ₁ γ₂} → γ₁ ⊑ Γ → γ₂ ⊑ Γ → γ₁ ⊔ γ₂ ⊑ Γ
  ⊔-lub  ⊑[]        ⊑[]       = ⊑[]
  ⊔-lub (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) =
    ⊑∷ (⊑tₛLat.⊔ₛ-least {x = ↑t p₁} {↑t p₂} {⊑tₛLat.⊤ₛ}  p₁ p₂)
       (⊔-lub q₁ q₂)

-- Lifting
_⊓ₛ_ : ∀ {Γ} → ⌊ Γ ⌋ → ⌊ Γ ⌋ → ⌊ Γ ⌋
γ ⊓ₛ γ' = _ isSlice ⊑.trans (⊓-lb₁ (γ .proof) (γ' .proof)) (γ .proof)

infixl 6 _⊓ₛ_

_⊔ₛ_ : ∀ {Γ} → ⌊ Γ ⌋ → ⌊ Γ ⌋ → ⌊ Γ ⌋
γ ⊔ₛ γ' = γ .↓ ⊔ γ' .↓ isSlice ⊔-lub (γ .proof) (γ' .proof)

infixl 7 _⊔ₛ_

private
  ⊓ₛ-lb₁ : ∀ {Γ} (γ₁ γ₂ : ⌊ Γ ⌋) → γ₁ ⊓ₛ γ₂ ⊑ₛ γ₁
  ⊓ₛ-lb₁ γ₁ γ₂ = ⊓-lb₁ (γ₁ .proof) (γ₂ .proof)

  ⊓ₛ-lb₂ : ∀ {Γ} (γ₁ γ₂ : ⌊ Γ ⌋) → γ₁ ⊓ₛ γ₂ ⊑ₛ γ₂
  ⊓ₛ-lb₂ γ₁ γ₂ = ⊓-lb₂ (γ₁ .proof) (γ₂ .proof)

  ⊓ₛ-glb : ∀ {Γ} {γ : ⌊ Γ ⌋} (γ₁ γ₂ : ⌊ Γ ⌋) → γ ⊑ₛ γ₁ → γ ⊑ₛ γ₂ → γ ⊑ₛ γ₁ ⊓ₛ γ₂
  ⊓ₛ-glb γ₁ γ₂ = ⊓-glb (γ₁ .proof) (γ₂ .proof)

  ⊓ₛ-infimum : ∀ {Γ} → Infimum (_⊑ₛ_ {Γ}) _⊓ₛ_
  ⊓ₛ-infimum γ₁ γ₂ = ⊓ₛ-lb₁ γ₁ γ₂ , ⊓ₛ-lb₂ γ₁ γ₂ , λ γ → ⊓ₛ-glb {γ = γ} γ₁ γ₂

  ⊔ₛ-ub₁ : ∀ {Γ} (γ₁ γ₂ : ⌊ Γ ⌋) → γ₁ ⊑ₛ γ₁ ⊔ₛ γ₂
  ⊔ₛ-ub₁ γ₁ γ₂ = ⊔-ub₁ (γ₁ .proof) (γ₂ .proof)

  ⊔ₛ-ub₂ : ∀ {Γ} (γ₁ γ₂ : ⌊ Γ ⌋) → γ₂ ⊑ₛ γ₁ ⊔ₛ γ₂
  ⊔ₛ-ub₂ γ₁ γ₂ = ⊔-ub₂ (γ₁ .proof) (γ₂ .proof)

  ⊔ₛ-lub : ∀ {Γ} {γ : ⌊ Γ ⌋} (γ₁ γ₂ : ⌊ Γ ⌋) → γ₁ ⊑ₛ γ → γ₂ ⊑ₛ γ → γ₁ ⊔ₛ γ₂ ⊑ₛ γ
  ⊔ₛ-lub {γ} γ₁ γ₂ p q = ⊔-lub p q

  ⊔ₛ-supremum : ∀ {Γ} → Supremum (_⊑ₛ_ {Γ}) _⊔ₛ_
  ⊔ₛ-supremum γ₁ γ₂ = ⊔ₛ-ub₁ γ₁ γ₂ , ⊔ₛ-ub₂ γ₁ γ₂ , λ γ → ⊔ₛ-lub {γ = γ} γ₁ γ₂


  □-min-slice : ∀ {Γ} → ⌊ Γ ⌋
  □-min-slice {Γ} = □ (length Γ) isSlice □-min
    where
    □-min : ∀ {Γ} → □ (length Γ) ⊑ Γ
    □-min {[]}    = ⊑[]
    □-min {_ ∷ Γ} = ⊑∷ ⊑t□ □-min

  ⊥ₛ' : ∀ {Γ} → ⌊ Γ ⌋
  ⊥ₛ' {Γ} = □-min-slice

  ⊥ₛ-min : ∀ {Γ} → Minimum (_⊑ₛ_ {Γ}) ⊥ₛ'
  ⊥ₛ-min (_ isSlice ⊑[])     = ⊑[]
  ⊥ₛ-min (_ isSlice (⊑∷ _ q)) = ⊑∷ ⊑t□ (⊥ₛ-min (_ isSlice q))

  ⊤ₛ-maximum : ∀ {Γ} → Maximum (_⊑ₛ_ {Γ}) ⊤ₛ'
  ⊤ₛ-maximum γ = γ .proof

  -- distributvity
  ⊓ₛ-distribˡ-⊔ₛ : ∀ {τ} (υ₁ υ₂ υ₃ : ⌊ τ ⌋) → (υ₁ ⊓ₛ (υ₂ ⊔ₛ υ₃)) ≈ₛ ((υ₁ ⊓ₛ υ₂) ⊔ₛ (υ₁ ⊓ₛ υ₃))
  ⊓ₛ-distribˡ-⊔ₛ (_ isSlice ⊑[]) (_ isSlice ⊑[]) (_ isSlice ⊑[]) = refl
  ⊓ₛ-distribˡ-⊔ₛ (γ₁ isSlice ⊑∷ p₁ q₁) (γ₂ isSlice ⊑∷ p₂ q₂) (γ₃ isSlice ⊑∷ p₃ q₃)
    = cong₂ _∷_ (⊑tₛLat.⊓ₛ-distribˡ-⊔ₛ (↑t p₁) (↑t p₂) (↑t p₃))
                (⊓ₛ-distribˡ-⊔ₛ (↑ q₁) (↑ q₂) (↑ q₃))


  ⊑ₛ-isMeetSemilattice : ∀ {Γ} → IsMeetSemilattice (_≡_ on ↓) (_⊑ₛ_ {Γ}) _⊓ₛ_
  ⊑ₛ-isMeetSemilattice = record
                         { isPartialOrder = ⊑ₛ.isPartialOrder
                         ; infimum        = ⊓ₛ-infimum
                         }

  ⊑ₛ-isJoinSemilattice : ∀ {Γ} → IsJoinSemilattice (_≡_ on ↓) (_⊑ₛ_ {Γ}) _⊔ₛ_
  ⊑ₛ-isJoinSemilattice = record
                         { isPartialOrder = ⊑ₛ.isPartialOrder
                         ; supremum       = ⊔ₛ-supremum
                         }

  ⊑ₛ-isLattice : ∀ {Γ} → IsLattice (_≡_ on ↓) (_⊑ₛ_ {Γ}) _⊔ₛ_ _⊓ₛ_
  ⊑ₛ-isLattice = record
                 { isPartialOrder = ⊑ₛ.isPartialOrder
                 ; supremum       = ⊔ₛ-supremum
                 ; infimum        = ⊓ₛ-infimum
                 }

  ⊑ₛ-isBoundedLattice : ∀ {Γ} → IsBoundedLattice (_≡_ on ↓) (_⊑ₛ_ {Γ}) _⊔ₛ_ _⊓ₛ_ ⊤ₛ' ⊥ₛ'
  ⊑ₛ-isBoundedLattice = record
                        { isLattice = ⊑ₛ-isLattice
                        ; maximum   = ⊤ₛ-maximum
                        ; minimum   = ⊥ₛ-min
                        }

  ⊑ₛ-isDistributiveLattice : ∀ {Γ} → IsDistributiveLattice (_≡_ on ↓) (_⊑ₛ_ {Γ}) _⊔ₛ_ _⊓ₛ_
  ⊑ₛ-isDistributiveLattice = record
                             { isLattice = ⊑ₛ-isLattice
                             ; ∧-distribˡ-∨ = ⊓ₛ-distribˡ-⊔ₛ
                             }

module ⊑ₛLat {Γ} where
  open IsBoundedLattice (⊑ₛ-isBoundedLattice {Γ}) public
    using (infimum; supremum; maximum; minimum;
           isBoundedJoinSemilattice; isBoundedMeetSemilattice; isJoinSemilattice; isMeetSemilattice; isLattice)
    renaming (x∧y≤x to x⊓ₛy⊑ₛx; x∧y≤y to x⊓ₛy⊑ₛy; x≤x∨y to x⊑ₛx⊔ₛy; y≤x∨y to y⊑ₛx⊔ₛy;
              ∧-greatest to ⊓ₛ-greatest; ∨-least to ⊔ₛ-least)

  ⊤ₛ = ⊤ₛ'
  ⊥ₛ = ⊥ₛ'

  isBoundedLattice = ⊑ₛ-isBoundedLattice

  open IsDistributiveLattice (⊑ₛ-isDistributiveLattice {Γ}) public 
    using () renaming (∧-distribˡ-∨ to ⊓ₛ-distribˡ-⊔ₛ)

  isDistributiveLattice = ⊑ₛ-isDistributiveLattice

