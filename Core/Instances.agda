module Core.Instances where

open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsEquivalence; IsDecEquivalence; Maximum)
open import Relation.Binary.Lattice using (IsMeetSemilattice; IsBoundedLattice; IsDistributiveLattice; IsBoundedMeetSemilattice)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Function using (_on_)

-- For overloading of ⊓, ⊑, ⌊_⌋ etc. operators and types.

record HasDecEq (A : Set) : Set where
  field _≟_ : (x y : A) → Dec (x ≡ y)
open HasDecEq ⦃...⦄ public

record HasPrecision (A : Set) : Set₁ where
  field
    _⊑_                : A → A → Set
    isDecPartialOrder  : IsDecPartialOrder _≡_ _⊑_
  infix 4 _⊑_
open HasPrecision ⦃...⦄ public hiding (isDecPartialOrder)

-- Overloaded ⊑ module
module ⊑ {A : Set} ⦃ hp : HasPrecision A ⦄ =
  IsDecPartialOrder (HasPrecision.isDecPartialOrder hp)
    using (antisym; isPartialOrder; isPreorder; refl; reflexive; trans)

record HasMeet (A : Set) ⦃ _ : HasPrecision A ⦄ : Set where
  field
    _⊓_ : A → A → A
    -- Closure required to lift to meets on slices of a term _⊓ₛ_
    closure : ∀ {a b c} → a ⊑ c → b ⊑ c → a ⊓ b ⊑ c
  infixl 6 _⊓_
open HasMeet ⦃...⦄ public

record HasJoin (A : Set) ⦃ _ : HasPrecision A ⦄ : Set where
  field
    _⊔_ : A → A → A
    -- In this case, closure equates to the LUB lattice property
    closure : ∀ {a b c} → a ⊑ c → b ⊑ c → a ⊔ b ⊑ c
  infixl 6 _⊔_
open HasJoin ⦃...⦄ public

-- e (only for types/expression where we have a Meet Semilattice)
record HasMeetSemilattice (A : Set) ⦃ _ : HasPrecision A ⦄ ⦃ _ : HasMeet A ⦄ : Set₁ where
  field isMeetSemilattice : IsMeetSemilattice _≡_ _⊑_ _⊓_
open HasMeetSemilattice ⦃...⦄ public hiding (isMeetSemilattice)

module ⊑Lat {A : Set} ⦃ hp : HasPrecision A ⦄ ⦃ hm : HasMeet A ⦄ ⦃ hms : HasMeetSemilattice A ⦄ where
  open IsMeetSemilattice (HasMeetSemilattice.isMeetSemilattice hms) public
    using (infimum)
    renaming (∧-greatest to ⊓-greatest; x∧y≤x to x⊓y⊑x; x∧y≤y to x⊓y⊑y)
  isMeetSemilattice = HasMeetSemilattice.isMeetSemilattice hms


-- Lifting Precision to Precision on slices OF a fixed term a
record SliceOf {A : Set} ⦃ _ : HasPrecision A ⦄ (a : A) : Set where
  constructor _isSlice_
  field
    ↓     : A
    proof : _⊑_ ↓ a

infix 3 _isSlice_
open SliceOf public

⌊_⌋ : ∀ {A : Set} ⦃ _ : HasPrecision A ⦄ → A → Set
⌊_⌋ = SliceOf

_≈ₛ_ : ∀ {A : Set} ⦃ _ : HasPrecision A ⦄ {a a' : A} → ⌊ a ⌋ → ⌊ a' ⌋ → Set
s₁ ≈ₛ s₂ = s₁ .↓ ≡ s₂ .↓

_≈ₛ?_ : ∀ {A : Set} ⦃ hp : HasPrecision A ⦄ {a : A} (s₁ s₂ : ⌊ a ⌋) → Dec (s₁ ≈ₛ s₂)
_≈ₛ?_ ⦃ hp = hp ⦄ s₁ s₂ = IsDecPartialOrder._≟_ (HasPrecision.isDecPartialOrder hp) (s₁ .↓) (s₂ .↓)

_⊑ₛ_ : ∀ {A : Set} ⦃ _ : HasPrecision A ⦄ {a a' : A} → ⌊ a ⌋ → ⌊ a' ⌋ → Set
s₁ ⊑ₛ s₂ = _⊑_ (s₁ .↓) (s₂ .↓)

infix 4 _⊑ₛ_

_⊑ₛ?_ : ∀ {A : Set} ⦃ hp : HasPrecision A ⦄ {a : A} (s₁ s₂ : ⌊ a ⌋) → Dec (s₁ ⊑ₛ s₂)
_⊑ₛ?_ ⦃ hp = hp ⦄ s₁ s₂ = IsDecPartialOrder._≤?_ (HasPrecision.isDecPartialOrder hp) (s₁ .↓) (s₂ .↓)

↑ : ∀ {A : Set} ⦃ _ : HasPrecision A ⦄ {a' a : A} → _⊑_ a' a → ⌊ a ⌋
↑ {a' = a'} p = a' isSlice p

⊤ₛ : ∀ {A : Set} ⦃ _ : HasPrecision A ⦄ {a : A} → ⌊ a ⌋
⊤ₛ = ↑ ⊑.refl

⊤ₛ-max : ∀ {A : Set} ⦃ _ : HasPrecision A ⦄ {a : A} → Maximum (_⊑ₛ_ {a = a}) ⊤ₛ
⊤ₛ-max s = s .proof

weaken : ∀ {A : Set} ⦃ _ : HasPrecision A ⦄ {a a' : A} → _⊑_ a a' → ⌊ a ⌋ → ⌊ a' ⌋
weaken p s = s .↓ isSlice ⊑.trans (s .proof) p

weaken-identity : ∀ {A : Set} ⦃ _ : HasPrecision A ⦄ {a a' : A} {s : ⌊ a ⌋} {p : _⊑_ a a'} → weaken p s ≈ₛ s
weaken-identity = Eq.refl

private
  ≈ₛ-isEquivalence : ∀ {A : Set} ⦃ hp : HasPrecision A ⦄ {a : A} → IsEquivalence (_≈ₛ_ {a = a} {a' = a})
  ≈ₛ-isEquivalence = record
    { refl  = Eq.refl
    ; sym   = Eq.sym
    ; trans = Eq.trans
    }

  ≈ₛ-isDecEquivalence : ∀ {A : Set} ⦃ hp : HasPrecision A ⦄ {a : A} → IsDecEquivalence (_≈ₛ_ {a = a} {a' = a})
  ≈ₛ-isDecEquivalence = record
    { isEquivalence = ≈ₛ-isEquivalence
    ; _≟_           = _≈ₛ?_
    }

  ⊑ₛ-isPartialOrder : ∀ {A : Set} ⦃ hp : HasPrecision A ⦄ {a : A} → IsPartialOrder (_≈ₛ_ {a = a} {a' = a}) _⊑ₛ_
  ⊑ₛ-isPartialOrder = record
    { isPreorder = record
      { isEquivalence = ≈ₛ-isEquivalence
      ; reflexive     = ⊑.reflexive
      ; trans          = ⊑.trans
      }
    ; antisym = ⊑.antisym
    }

  ⊑ₛ-isDecPartialOrder : ∀ {A : Set} ⦃ hp : HasPrecision A ⦄ {a : A} → IsDecPartialOrder (_≈ₛ_ {a = a} {a' = a}) _⊑ₛ_
  ⊑ₛ-isDecPartialOrder = record
    { isPartialOrder = ⊑ₛ-isPartialOrder
    ; _≟_            = _≈ₛ?_
    ; _≤?_           = _⊑ₛ?_
    }

module ≈ₛ {A : Set} ⦃ hp : HasPrecision A ⦄ {a : A} =
  IsDecEquivalence (≈ₛ-isDecEquivalence {A} ⦃ hp ⦄ {a})

module ⊑ₛ {A : Set} ⦃ hp : HasPrecision A ⦄ {a : A} where
  open IsDecPartialOrder (⊑ₛ-isDecPartialOrder {A} ⦃ hp ⦄ {a}) public
    hiding (module Eq; isEquivalence; ≲-resp-≈; ≲-respˡ-≈; ≲-respʳ-≈; _≟_; _≤?_)
    renaming (≤-resp-≈ to ⊑ₛ-resp-≈ₛ; ≤-respˡ-≈ to ⊑ₛ-respˡ-≈ₛ; ≤-respʳ-≈ to ⊑ₛ-respʳ-≈ₛ)


-- Lift meets/join
_⊓ₛ_ : ∀ {A} {a : A} ⦃ _ : HasPrecision A ⦄ ⦃ hm : HasMeet A ⦄ → ⌊ a ⌋ → ⌊ a ⌋ → ⌊ a ⌋
_⊓ₛ_ ⦃ hm = hm ⦄ s₁ s₂ = s₁ .↓ ⊓ s₂ .↓ isSlice HasMeet.closure hm (s₁ .proof) (s₂ .proof)

_⊔ₛ_ : ∀ {A} {a : A} ⦃ _ : HasPrecision A ⦄ ⦃ hm : HasJoin A ⦄ → ⌊ a ⌋ → ⌊ a ⌋ → ⌊ a ⌋
_⊔ₛ_ ⦃ hm = hm ⦄ s₁ s₂ = s₁ .↓ ⊔ s₂ .↓ isSlice HasJoin.closure hm (s₁ .proof) (s₂ .proof)

-- Lift a meet semilattice to a bounded meet semilattice on slices
module ⊓ₛ
  {A : Set}
  ⦃ hp : HasPrecision A ⦄
  ⦃ hm : HasMeet A ⦄
  ⦃ hms : HasMeetSemilattice A ⦄
  {a : A}
  where

  open IsMeetSemilattice (HasMeetSemilattice.isMeetSemilattice hms)
    hiding (trans; isPartialOrder)


  private
    isBoundedMeetSemilattice' : ∀ {a} → IsBoundedMeetSemilattice (_≈ₛ_ {a = a} {a' = a}) _⊑ₛ_ _⊓ₛ_ ⊤ₛ
    isBoundedMeetSemilattice' = record
      { isMeetSemilattice = record
        { isPartialOrder = ⊑ₛ.isPartialOrder
        ; infimum = λ s₁ s₂ →
                    x∧y≤x (s₁ .↓) (s₂ .↓)
                  , x∧y≤y (s₁ .↓) (s₂ .↓)
                  , λ _ → ∧-greatest
        }
      ; maximum = ⊤ₛ-max
      }

  open IsBoundedMeetSemilattice (isBoundedMeetSemilattice' {a}) public
    using (infimum; isMeetSemilattice; maximum)
    renaming (x∧y≤x to x⊓ₛy⊑ₛx; x∧y≤y to x⊓ₛy⊑ₛy; ∧-greatest to ⊓ₛ-greatest)

  isBoundedMeetSemilattice = isBoundedMeetSemilattice'

record SliceLattice (A : Set) ⦃ hp : HasPrecision A ⦄ ⦃ hm : HasMeet A ⦄ ⦃ hj : HasJoin A ⦄ : Set₁ where
  field
    ⊥ₛ    : ∀ {a} → ⌊ a ⌋
    isBoundedLattice      : ∀ {a} → IsBoundedLattice (_≡_ on ↓) (_⊑ₛ_ {A} ⦃ hp ⦄ {a} {a}) _⊔ₛ_ _⊓ₛ_ (⊤ₛ {A} ⦃ hp ⦄ {a}) ⊥ₛ
    isDistributiveLattice : ∀ {a} → IsDistributiveLattice (_≡_ on ↓) (_⊑ₛ_ {A} ⦃ hp ⦄ {a} {a}) _⊔ₛ_ _⊓ₛ_
  infixl 6 _⊓ₛ_
  infixl 7 _⊔ₛ_
open SliceLattice ⦃...⦄ public using (⊥ₛ)

module ⊑ₛLat {A : Set} ⦃ hp : HasPrecision A ⦄ ⦃ hm : HasMeet A ⦄ ⦃ hj : HasJoin A ⦄ ⦃ sl : SliceLattice A ⦄ {a : A} where
  open IsBoundedLattice (SliceLattice.isBoundedLattice sl {a}) public
    using (infimum; supremum;
           isBoundedJoinSemilattice; isBoundedMeetSemilattice; isJoinSemilattice; isMeetSemilattice; isLattice)
    renaming (x∧y≤x to x⊓ₛy⊑ₛx; x∧y≤y to x⊓ₛy⊑ₛy; x≤x∨y to x⊑ₛx⊔ₛy; y≤x∨y to y⊑ₛx⊔ₛy;
              ∧-greatest to ⊓ₛ-greatest; ∨-least to ⊔ₛ-least;
              maximum to ⊤ₛ-max; minimum to ⊥ₛ-min)
  isBoundedLattice = SliceLattice.isBoundedLattice sl
  open IsDistributiveLattice (SliceLattice.isDistributiveLattice sl {a}) public
    using () renaming (∧-distribˡ-∨ to ⊓ₛ-distribˡ-⊔ₛ)
  isDistributiveLattice = SliceLattice.isDistributiveLattice sl
