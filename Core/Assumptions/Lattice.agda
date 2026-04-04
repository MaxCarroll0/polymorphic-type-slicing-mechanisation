module Core.Assumptions.Lattice where

open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_,_)
open import Relation.Binary using (IsPartialOrder)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Maximum; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong₂)
open import Relation.Binary.Lattice.Structures using (IsMeetSemilattice; IsJoinSemilattice; IsLattice; IsBoundedLattice)
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum)
open import Function using (_on_)

open import Core.Typ using (Typ; □)
open import Core.Typ.Precision using (_⊑t_; ⊑?; ⊑t-refl; ⊑t-trans; ⊑t-antisym)
open import Core.Typ.Lattice using (_⊓t_; _⊔t_; ⊓t-lb₁; ⊓t-lb₂; ⊓t-glb; ⊔t-preserves-⊑; ⊓t-preserves-⊑-spec)
open import Core.Assumptions.Base
open import Core.Assumptions.Precision

-- □Γ (length Γ) is below any slice of Γ
□Γ-min-slice : ∀ {Γ' Γ} → Γ' ⊑Γ Γ → □Γ (length Γ) ⊑Γ Γ'
□Γ-min-slice ⊑[]       = ⊑[]
□Γ-min-slice (⊑∷ _ pf) = ⊑∷ ⊑? (□Γ-min-slice pf)

-- Instantiate generic Slice module for assumptions
open import Slice _⊑Γ_ (λ Γ → □Γ (length Γ)) □Γ-min □Γ-min-slice ⊑Γ-refl ⊑Γ-trans public
  renaming (SliceOf to SliceOfΓ; _⊑ₛ_ to _⊑Γₛ_; ⊤ₛ to ⊤Γₛ; ⊥ₛ to ⊥Γₛ; weaken to ⊑Γₛ-weaken; weaken-identity to ⊑Γₛ-weaken-identity; ⊥ₛ-min to ⊥Γₛ-min)

-- Pointwise meet (for same-length lists)
_⊓Γ_ : Assumptions → Assumptions → Assumptions
[]       ⊓Γ []         = []
(τ ∷ Γ₁) ⊓Γ (τ' ∷ Γ₂)  = (τ ⊓t τ') ∷ (Γ₁ ⊓Γ Γ₂)
_        ⊓Γ _          = []

infixl 6 _⊓Γ_

-- Pointwise join (for same-length lists)
_⊔Γ_ : Assumptions → Assumptions → Assumptions
[]       ⊔Γ []         = []
(τ ∷ Γ₁) ⊔Γ (τ' ∷ Γ₂)  = (τ ⊔t τ') ∷ (Γ₁ ⊔Γ Γ₂)
_        ⊔Γ _          = []

infixl 6 _⊔Γ_

-- Meet is lower bound (left) - requires proof that arguments share an upper bound (ensures same length)
⊓Γ-lb₁ : ∀ {Γ₁ Γ₂ Γ} → Γ₁ ⊑Γ Γ → Γ₂ ⊑Γ Γ → Γ₁ ⊓Γ Γ₂ ⊑Γ Γ₁
⊓Γ-lb₁ ⊑[]                ⊑[]                = ⊑[]
⊓Γ-lb₁ (⊑∷ {τ₁} p₁ q₁) (⊑∷ {τ₂} p₂ q₂) = ⊑∷ (⊓t-lb₁ τ₁ τ₂) (⊓Γ-lb₁ q₁ q₂)

-- Meet is lower bound (right)
⊓Γ-lb₂ : ∀ {Γ₁ Γ₂ Γ} → Γ₁ ⊑Γ Γ → Γ₂ ⊑Γ Γ → Γ₁ ⊓Γ Γ₂ ⊑Γ Γ₂
⊓Γ-lb₂ ⊑[]                ⊑[]                = ⊑[]
⊓Γ-lb₂ (⊑∷ {τ₁} p₁ q₁) (⊑∷ {τ₂} p₂ q₂) = ⊑∷ (⊓t-lb₂ τ₁ τ₂) (⊓Γ-lb₂ q₁ q₂)

-- Meet is greatest lower bound
⊓Γ-glb : ∀ {Γ Γ₁ Γ₂} → Γ ⊑Γ Γ₁ → Γ ⊑Γ Γ₂ → Γ ⊑Γ Γ₁ ⊓Γ Γ₂
⊓Γ-glb ⊑[]        ⊑[]        = ⊑[]
⊓Γ-glb (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊓t-glb p₁ p₂) (⊓Γ-glb q₁ q₂)

-- Meet preserves precision (for slices of the same Γ)
⊓Γ-preserves-⊑-spec : ∀ {Γ₁ Γ₂ Γ : Assumptions} → Γ₁ ⊑Γ Γ → Γ₂ ⊑Γ Γ → Γ₁ ⊓Γ Γ₂ ⊑Γ Γ
⊓Γ-preserves-⊑-spec p₁ p₂ = ⊑Γ-trans (⊓Γ-lb₁ p₁ p₂) p₁

-- Join is upper bound (left)
⊔Γ-ub₁ : ∀ {Γ₁ Γ₂ Γ} → Γ₁ ⊑Γ Γ → Γ₂ ⊑Γ Γ → Γ₁ ⊑Γ Γ₁ ⊔Γ Γ₂
⊔Γ-ub₁ ⊑[]        ⊑[]        = ⊑[]
⊔Γ-ub₁ (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊔t-preserves-⊑-ub₁ p₁ p₂) (⊔Γ-ub₁ q₁ q₂)
  where
    open import Core.Typ.Lattice using (⊔t-ub₁)
    open import Core.Typ.Properties using (⊑t-consistent)
    ⊔t-preserves-⊑-ub₁ : ∀ {τ₁ τ₂ τ} → τ₁ ⊑t τ → τ₂ ⊑t τ → τ₁ ⊑t τ₁ ⊔t τ₂
    ⊔t-preserves-⊑-ub₁ p q = ⊔t-ub₁ (⊑t-consistent p q)

-- Join is upper bound (right)
⊔Γ-ub₂ : ∀ {Γ₁ Γ₂ Γ} → Γ₁ ⊑Γ Γ → Γ₂ ⊑Γ Γ → Γ₂ ⊑Γ Γ₁ ⊔Γ Γ₂
⊔Γ-ub₂ ⊑[]        ⊑[]        = ⊑[]
⊔Γ-ub₂ (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊔t-preserves-⊑-ub₂ p₁ p₂) (⊔Γ-ub₂ q₁ q₂)
  where
    open import Core.Typ.Lattice using (⊔t-ub₂)
    open import Core.Typ.Properties using (⊑t-consistent)
    ⊔t-preserves-⊑-ub₂ : ∀ {τ₁ τ₂ τ} → τ₁ ⊑t τ → τ₂ ⊑t τ → τ₂ ⊑t τ₁ ⊔t τ₂
    ⊔t-preserves-⊑-ub₂ p q = ⊔t-ub₂ (⊑t-consistent p q)

-- Join is least upper bound
⊔Γ-lub : ∀ {Γ Γ₁ Γ₂} → Γ₁ ⊑Γ Γ → Γ₂ ⊑Γ Γ → Γ₁ ⊔Γ Γ₂ ⊑Γ Γ
⊔Γ-lub ⊑[]        ⊑[]        = ⊑[]
⊔Γ-lub (⊑∷ p₁ q₁) (⊑∷ p₂ q₂) = ⊑∷ (⊔t-preserves-⊑ p₁ p₂) (⊔Γ-lub q₁ q₂)

-- Lifted partial order on slices of assumptions
⊑Γₛ-refl : ∀ {Γ} → Reflexive (_⊑Γₛ_ {Γ})
⊑Γₛ-refl = ⊑Γ-refl

⊑Γₛ-trans : ∀ {Γ} → Transitive (_⊑Γₛ_ {Γ})
⊑Γₛ-trans = ⊑Γ-trans

⊑Γₛ-antisym : ∀ {Γ} → Antisymmetric (_≡_ on ↓) (_⊑Γₛ_ {Γ})
⊑Γₛ-antisym = ⊑Γ-antisym

⊑Γₛ-isPartialOrder : ∀ {Γ} → IsPartialOrder (_≡_ on ↓) (_⊑Γₛ_ {Γ})
⊑Γₛ-isPartialOrder = record
  { isPreorder = record
    { isEquivalence = record
      { refl = refl ; sym = sym ; trans = trans }
    ; reflexive = λ where refl → ⊑Γ-refl
    ; trans = λ {Γ''} {Γ'} {Γ} → ⊑Γ-trans
    }
  ; antisym = λ {Γ'} {Γ} → ⊑Γ-antisym
  }

-- Slice meet
_⊓Γₛ_ : ∀ {Γ} → ⌊ Γ ⌋ → ⌊ Γ ⌋ → ⌊ Γ ⌋
γ ⊓Γₛ γ' = γ .↓ ⊓Γ γ' .↓ isSlice ⊓Γ-preserves-⊑-spec (γ .proof) (γ' .proof)

infixl 6 _⊓Γₛ_

-- Slice join
_⊔Γₛ_ : ∀ {Γ} → ⌊ Γ ⌋ → ⌊ Γ ⌋ → ⌊ Γ ⌋
γ ⊔Γₛ γ' = γ .↓ ⊔Γ γ' .↓ isSlice ⊔Γ-lub (γ .proof) (γ' .proof)

infixl 7 _⊔Γₛ_

-- Slice meet is lower bound
⊓Γₛ-lb₁ : ∀ {Γ} (γ₁ γ₂ : ⌊ Γ ⌋) → γ₁ ⊓Γₛ γ₂ ⊑Γₛ γ₁
⊓Γₛ-lb₁ γ₁ γ₂ = ⊓Γ-lb₁ (γ₁ .proof) (γ₂ .proof)

⊓Γₛ-lb₂ : ∀ {Γ} (γ₁ γ₂ : ⌊ Γ ⌋) → γ₁ ⊓Γₛ γ₂ ⊑Γₛ γ₂
⊓Γₛ-lb₂ γ₁ γ₂ = ⊓Γ-lb₂ (γ₁ .proof) (γ₂ .proof)

⊓Γₛ-glb : ∀ {Γ} {γ γ₁ γ₂ : ⌊ Γ ⌋} → γ ⊑Γₛ γ₁ → γ ⊑Γₛ γ₂ → γ ⊑Γₛ γ₁ ⊓Γₛ γ₂
⊓Γₛ-glb = ⊓Γ-glb

-- Slice join is upper bound
⊔Γₛ-ub₁ : ∀ {Γ} (γ₁ γ₂ : ⌊ Γ ⌋) → γ₁ ⊑Γₛ γ₁ ⊔Γₛ γ₂
⊔Γₛ-ub₁ γ₁ γ₂ = ⊔Γ-ub₁ (γ₁ .proof) (γ₂ .proof)

⊔Γₛ-ub₂ : ∀ {Γ} (γ₁ γ₂ : ⌊ Γ ⌋) → γ₂ ⊑Γₛ γ₁ ⊔Γₛ γ₂
⊔Γₛ-ub₂ γ₁ γ₂ = ⊔Γ-ub₂ (γ₁ .proof) (γ₂ .proof)

⊔Γₛ-lub : ∀ {Γ} {γ γ₁ γ₂ : ⌊ Γ ⌋} → γ₁ ⊑Γₛ γ → γ₂ ⊑Γₛ γ → γ₁ ⊔Γₛ γ₂ ⊑Γₛ γ
⊔Γₛ-lub {_} {γ} {γ₁} {γ₂} p q = ⊔Γ-lub p q

-- Slice infimum and supremum
⊓Γₛ-infimum : ∀ {Γ} → Infimum (_⊑Γₛ_ {Γ}) _⊓Γₛ_
⊓Γₛ-infimum γ₁ γ₂ = ⊓Γₛ-lb₁ γ₁ γ₂ , ⊓Γₛ-lb₂ γ₁ γ₂ , λ γ → ⊓Γₛ-glb {γ = γ} {γ₁} {γ₂}

⊔Γₛ-supremum : ∀ {Γ} → Supremum (_⊑Γₛ_ {Γ}) _⊔Γₛ_
⊔Γₛ-supremum γ₁ γ₂ = ⊔Γₛ-ub₁ γ₁ γ₂ , ⊔Γₛ-ub₂ γ₁ γ₂ , λ γ → ⊔Γₛ-lub {γ = γ} {γ₁} {γ₂}

-- Slice meet semilattice
⊓Γₛ-isMeetSemilattice : ∀ {Γ} → IsMeetSemilattice (_≡_ on ↓) (_⊑Γₛ_ {Γ}) _⊓Γₛ_
⊓Γₛ-isMeetSemilattice = record
  { isPartialOrder = ⊑Γₛ-isPartialOrder
  ; infimum        = ⊓Γₛ-infimum
  }

-- Slice join semilattice
⊔Γₛ-isJoinSemilattice : ∀ {Γ} → IsJoinSemilattice (_≡_ on ↓) (_⊑Γₛ_ {Γ}) _⊔Γₛ_
⊔Γₛ-isJoinSemilattice = record
  { isPartialOrder = ⊑Γₛ-isPartialOrder
  ; supremum       = ⊔Γₛ-supremum
  }

-- Full lattice on slices of assumptions
⊑Γₛ-isLattice : ∀ {Γ} → IsLattice (_≡_ on ↓) (_⊑Γₛ_ {Γ}) _⊔Γₛ_ _⊓Γₛ_
⊑Γₛ-isLattice = record
  { isPartialOrder = ⊑Γₛ-isPartialOrder
  ; supremum       = ⊔Γₛ-supremum
  ; infimum        = ⊓Γₛ-infimum
  }

-- Bounded lattice: □Γ (length Γ) is bottom, Γ is top
⊤Γₛ-maximum : ∀ {Γ} → Maximum (_⊑Γₛ_ {Γ}) ⊤Γₛ
⊤Γₛ-maximum γ = γ .proof

-- Bounded lattice on slices of assumptions
⊑Γₛ-isBoundedLattice : ∀ {Γ} → IsBoundedLattice (_≡_ on ↓) (_⊑Γₛ_ {Γ}) _⊔Γₛ_ _⊓Γₛ_ ⊤Γₛ ⊥Γₛ
⊑Γₛ-isBoundedLattice = record
  { isLattice = ⊑Γₛ-isLattice
  ; maximum   = ⊤Γₛ-maximum
  ; minimum   = ⊥Γₛ-min
  }
