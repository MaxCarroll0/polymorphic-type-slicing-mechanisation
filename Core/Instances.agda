module Core.Instances where

open import Relation.Nullary using (Dec)
open import Relation.Binary using (IsDecPartialOrder)
open import Relation.Binary.Lattice using (IsMeetSemilattice; IsBoundedLattice; IsDistributiveLattice)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (_on_)

-- For overloading of ⊓, ⊑, ⌊_⌋ etc. operators and types.

record HasDecEq (A : Set) : Set where
  field _≟_ : (x y : A) → Dec (x ≡ y)
open HasDecEq ⦃...⦄ public

record HasPrecision (A : Set) : Set₁ where
  field
    _⊑_               : A → A → Set
    isDecPartialOrder  : IsDecPartialOrder _≡_ _⊑_
  infix 4 _⊑_
open HasPrecision ⦃...⦄ public hiding (isDecPartialOrder)

-- Overloaded ⊑ module
module ⊑ {A : Set} ⦃ hp : HasPrecision A ⦄ =
  IsDecPartialOrder (HasPrecision.isDecPartialOrder hp)
    using (antisym; isPartialOrder; isPreorder; refl; reflexive; trans)

record HasMeet (A : Set) : Set where
  field _⊓_ : A → A → A
  infixl 6 _⊓_
open HasMeet ⦃...⦄ public

record HasJoin (A : Set) : Set where
  field _⊔_ : A → A → A
  infixl 6 _⊔_
open HasJoin ⦃...⦄ public

record HasMeetSemilattice (A : Set) ⦃ _ : HasPrecision A ⦄ ⦃ _ : HasMeet A ⦄ : Set₁ where
  field isMeetSemilattice : IsMeetSemilattice _≡_ _⊑_ _⊓_
open HasMeetSemilattice ⦃...⦄ public hiding (isMeetSemilattice)

-- e (only for types/expression where we have a Meet Semilattice)
module ⊑Lat {A : Set} ⦃ hp : HasPrecision A ⦄ ⦃ hm : HasMeet A ⦄ ⦃ hms : HasMeetSemilattice A ⦄ where
  open IsMeetSemilattice (HasMeetSemilattice.isMeetSemilattice hms) public
    using (infimum)
    renaming (∧-greatest to ⊓-greatest; x∧y≤x to x⊓y⊑x; x∧y≤y to x⊓y⊑y)
  isMeetSemilattice = HasMeetSemilattice.isMeetSemilattice hms


record HasSlice (A : Set) ⦃ _ : HasPrecision A ⦄ : Set₁ where
  field
    SliceOf          : A → Set
    ↓                : ∀ {a} → SliceOf a → A
    _isSlice_        : ∀ {a} → (x : A) → _⊑_ x a → SliceOf a
    ↑                : ∀ {a' a} → _⊑_ a' a → SliceOf a
    weaken           : ∀ {a a'} → _⊑_ a a' → SliceOf a → SliceOf a'
    _≈ₛ_             : ∀ {a a'} → SliceOf a → SliceOf a' → Set
    _≈ₛ?_            : ∀ {a} → (s₁ s₂ : SliceOf a) → Dec (s₁ ≈ₛ s₂)
    _⊑ₛ?_            : ∀ {a} → (s₁ s₂ : SliceOf a) → Dec (_⊑_ (↓ s₁) (↓ s₂))
  infix 3 _isSlice_
open HasSlice ⦃...⦄ public

-- Slice-level lattice bundle
record SliceLattice {A : Set} (S : A → Set) (↓' : ∀ {a} → S a → A) : Set₁ where
  field
    _⊑ₛ_  : ∀ {a} → S a → S a → Set
    _⊓ₛ_  : ∀ {a} → S a → S a → S a
    _⊔ₛ_  : ∀ {a} → S a → S a → S a
    ⊤ₛ    : ∀ {a} → S a
    ⊥ₛ    : ∀ {a} → S a
    isBoundedLattice      : ∀ {a} → IsBoundedLattice (_≡_ on ↓') (_⊑ₛ_ {a}) _⊔ₛ_ _⊓ₛ_ ⊤ₛ ⊥ₛ
    isDistributiveLattice : ∀ {a} → IsDistributiveLattice (_≡_ on ↓') (_⊑ₛ_ {a}) _⊔ₛ_ _⊓ₛ_
  infix 4 _⊑ₛ_
  infixl 6 _⊓ₛ_
  infixl 7 _⊔ₛ_
open SliceLattice ⦃...⦄ public hiding (isBoundedLattice; isDistributiveLattice; ⊤ₛ; ⊥ₛ)

module ⊑ₛLat {A : Set} {S : A → Set} {↓' : ∀ {a} → S a → A}
             ⦃ sl : SliceLattice S ↓' ⦄ {a : A} where
  open IsBoundedLattice (SliceLattice.isBoundedLattice sl {a}) public
    using (infimum; supremum;
           isBoundedJoinSemilattice; isBoundedMeetSemilattice; isJoinSemilattice; isMeetSemilattice; isLattice)
    renaming (x∧y≤x to x⊓ₛy⊑ₛx; x∧y≤y to x⊓ₛy⊑ₛy; x≤x∨y to x⊑ₛx⊔ₛy; y≤x∨y to y⊑ₛx⊔ₛy;
              ∧-greatest to ⊓ₛ-greatest; ∨-least to ⊔ₛ-least;
              maximum to ⊤ₛ-max; minimum to ⊥ₛ-min)
  ⊤ₛ = SliceLattice.⊤ₛ sl
  ⊥ₛ = SliceLattice.⊥ₛ sl
  isBoundedLattice = SliceLattice.isBoundedLattice sl
  open IsDistributiveLattice (SliceLattice.isDistributiveLattice sl {a}) public
    using () renaming (∧-distribˡ-∨ to ⊓ₛ-distribˡ-⊔ₛ)
  isDistributiveLattice = SliceLattice.isDistributiveLattice sl

⌊_⌋ : ∀ {A : Set} ⦃ _ : HasPrecision A ⦄ ⦃ _ : HasSlice A ⦄ → A → Set
⌊_⌋ = SliceOf
