module Core.Instances where

open import Relation.Nullary using (Dec)
open import Relation.Binary using (IsDecPartialOrder)
open import Relation.Binary.Lattice using (IsMeetSemilattice; IsBoundedLattice; IsDistributiveLattice)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (_on_)

record HasDecEq (A : Set) : Set where
  field _≟_ : (x y : A) → Dec (x ≡ y)
open HasDecEq ⦃...⦄ public

record HasPrecision (A : Set) : Set₁ where
  field
    _⊑_               : A → A → Set
    isDecPartialOrder  : IsDecPartialOrder _≡_ _⊑_
  infix 4 _⊑_
open HasPrecision ⦃...⦄ public hiding (isDecPartialOrder)

-- Overloaded ⊑ module: dispatches via HasPrecision instance
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

-- Optional: base-level meet semilattice proof (only Typ and Exp have this)
record HasMeetSemilattice (A : Set) ⦃ _ : HasPrecision A ⦄ ⦃ _ : HasMeet A ⦄ : Set₁ where
  field isMeetSemilattice : IsMeetSemilattice _≡_ _⊑_ _⊓_
open HasMeetSemilattice ⦃...⦄ public hiding (isMeetSemilattice)

-- Overloaded ⊑Lat module (only for types with HasMeetSemilattice)
module ⊑Lat {A : Set} ⦃ hp : HasPrecision A ⦄ ⦃ hm : HasMeet A ⦄ ⦃ hms : HasMeetSemilattice A ⦄ where
  open IsMeetSemilattice (HasMeetSemilattice.isMeetSemilattice hms) public
    using (infimum)
    renaming (∧-greatest to ⊓-greatest; x∧y≤x to x⊓y⊑x; x∧y≤y to x⊓y⊑y)
  isMeetSemilattice = HasMeetSemilattice.isMeetSemilattice hms

-- Slice-level lattice bundle, parameterised by carrier and slice type
record SliceLattice {A : Set} (⌊_⌋ : A → Set) (↓' : ∀ {a} → ⌊ a ⌋ → A) : Set₁ where
  field
    _⊑ₛ_  : ∀ {a} → ⌊ a ⌋ → ⌊ a ⌋ → Set
    _⊓ₛ_  : ∀ {a} → ⌊ a ⌋ → ⌊ a ⌋ → ⌊ a ⌋
    _⊔ₛ_  : ∀ {a} → ⌊ a ⌋ → ⌊ a ⌋ → ⌊ a ⌋
    ⊤ₛ    : ∀ {a} → ⌊ a ⌋
    ⊥ₛ    : ∀ {a} → ⌊ a ⌋
    isBoundedLattice      : ∀ {a} → IsBoundedLattice (_≡_ on ↓') (_⊑ₛ_ {a}) _⊔ₛ_ _⊓ₛ_ ⊤ₛ ⊥ₛ
    isDistributiveLattice : ∀ {a} → IsDistributiveLattice (_≡_ on ↓') (_⊑ₛ_ {a}) _⊔ₛ_ _⊓ₛ_
  infix 4 _⊑ₛ_
  infixl 6 _⊓ₛ_
  infixl 7 _⊔ₛ_
open SliceLattice ⦃...⦄ public hiding (isBoundedLattice; isDistributiveLattice; ⊤ₛ; ⊥ₛ)

-- Overloaded ⊑ₛLat module
module ⊑ₛLat {A : Set} {⌊_⌋ : A → Set} {↓' : ∀ {a} → ⌊ a ⌋ → A}
             ⦃ sl : SliceLattice ⌊_⌋ ↓' ⦄ {a : A} where
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
