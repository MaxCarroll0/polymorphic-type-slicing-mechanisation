module Core.Instances where

open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsEquivalence; IsDecEquivalence; Maximum)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Definitions using (Minimum)
open import Relation.Binary.Lattice
  using ( IsMeetSemilattice; IsJoinSemilattice; IsBoundedLattice; IsDistributiveLattice
        ; IsBoundedMeetSemilattice; IsLattice; Infimum; Supremum)
open import Relation.Binary.Lattice.Bundles as LatBundles
  using (MeetSemilattice; JoinSemilattice)
  renaming (Lattice to LatBundle; BoundedLattice to BLatBundle; DistributiveLattice to DLatBundle)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Function using (_on_)

-- For overloading of ⊓, ⊑, ⌊_⌋ etc. operators and types.

record HasDecEq (A : Set) : Set where
  field _≟_ : (x y : A) → Dec (x ≡ y)
open HasDecEq ⦃...⦄ public

record HasPrecision (A : Set) : Set₁ where
  field
    _≈_                : A → A → Set
    _⊑_                : A → A → Set
    isDecPartialOrder  : IsDecPartialOrder _≈_ _⊑_
  infix 4 _⊑_

  _⊑?_ = IsDecPartialOrder._≤?_ isDecPartialOrder
open HasPrecision ⦃...⦄ public hiding (isDecPartialOrder)

-- Overloaded ⊑ properties module
module ⊑ {A : Set} ⦃ hp : HasPrecision A ⦄ where
  open IsDecPartialOrder (HasPrecision.isDecPartialOrder hp) public
    using (antisym; isPartialOrder; isPreorder; refl; reflexive; trans)

  private
    poset : Poset _ _ _
    poset = record { isPartialOrder = isPartialOrder }

  open import Relation.Binary.Properties.Poset poset public
    using ( <-isStrictPartialOrder
          ; <-irrefl; <-asym; <-trans
          ; <-resp-≈; <-respˡ-≈; <-respʳ-≈
          ; mono⇒cong; antimono⇒cong
          )
    renaming ( _<_   to _⊏_
             ; <⇒≉   to ⊏⇒≉
             ; ≤∧≉⇒< to ⊑∧≉⇒⊏
             ; <⇒≱   to ⊏⇒⋢
             ; ≤⇒≯   to ⊑⇒⋣
             )

_⊏_ : ∀ {A : Set} ⦃ _ : HasPrecision A ⦄ → A → A → Set
_⊏_ = ⊑._⊏_
infix 4 _⊏_

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
-- TODO: Unify _⊑_ with _⊑ₛ_ by giving ⌊ a ⌋ a HasPrecision instance
-- with _≈_ = _≈ₛ_ and _⊑_ = _⊑ₛ_

record HasMeetSemilattice (A : Set) ⦃ hp : HasPrecision A ⦄ ⦃ _ : HasMeet A ⦄ : Set₁ where
  field isMeetSemilattice : IsMeetSemilattice (HasPrecision._≈_ hp) _⊑_ _⊓_
open HasMeetSemilattice ⦃...⦄ public hiding (isMeetSemilattice)

module ⊑Lat {A : Set} ⦃ hp : HasPrecision A ⦄ ⦃ hm : HasMeet A ⦄ ⦃ hms : HasMeetSemilattice A ⦄ where
  open IsMeetSemilattice (HasMeetSemilattice.isMeetSemilattice hms) public
    using (infimum)
    renaming (∧-greatest to ⊓-greatest; x∧y≤x to x⊓y⊑x; x∧y≤y to x⊓y⊑y)
  isMeetSemilattice = HasMeetSemilattice.isMeetSemilattice hms

  private
    meetSL : MeetSemilattice _ _ _
    meetSL = record { isMeetSemilattice = isMeetSemilattice }

  open import Relation.Binary.Lattice.Properties.MeetSemilattice meetSL public
    using ()
    renaming ( ∧-comm       to ⊓-comm
             ; ∧-assoc      to ⊓-assoc
             ; ∧-idempotent to ⊓-idempotent
             ; ∧-monotonic  to ⊓-monotonic
             ; ∧-cong       to ⊓-cong
             ; y≤x⇒x∧y≈y   to y⊑x⇒x⊓y≈y
             )

record HasJoinSemilattice (A : Set) ⦃ hp : HasPrecision A ⦄ ⦃ _ : HasJoin A ⦄ : Set₁ where
  field isJoinSemilattice : IsJoinSemilattice (HasPrecision._≈_ hp) _⊑_ _⊔_
open HasJoinSemilattice ⦃...⦄ public hiding (isJoinSemilattice)

module ⊔Lat {A : Set} ⦃ hp : HasPrecision A ⦄ ⦃ hj : HasJoin A ⦄ ⦃ hjs : HasJoinSemilattice A ⦄ where
  open IsJoinSemilattice (HasJoinSemilattice.isJoinSemilattice hjs) public
    using (supremum)
    renaming (∨-least to ⊔-least; x≤x∨y to x⊑x⊔y; y≤x∨y to y⊑x⊔y)
  isJoinSemilattice = HasJoinSemilattice.isJoinSemilattice hjs

  private
    joinSL : JoinSemilattice _ _ _
    joinSL = record { isJoinSemilattice = isJoinSemilattice }

  open import Relation.Binary.Lattice.Properties.JoinSemilattice joinSL public
    using ()
    renaming ( ∨-comm       to ⊔-comm
             ; ∨-assoc      to ⊔-assoc
             ; ∨-idempotent to ⊔-idempotent
             ; ∨-monotonic  to ⊔-monotonic
             ; ∨-cong       to ⊔-cong
             ; x≤y⇒x∨y≈y   to x⊑y⇒x⊔y≈y
             )


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
s₁ ≈ₛ s₂ = _≈_ (s₁ .↓) (s₂ .↓)

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

weaken-identity : ∀ {A : Set} ⦃ hp : HasPrecision A ⦄ {a a' : A} {s : ⌊ a ⌋} {p : _⊑_ a a'} → weaken p s ≈ₛ s
weaken-identity ⦃ hp ⦄ = IsDecPartialOrder.Eq.refl (HasPrecision.isDecPartialOrder hp)

private
  module ≈-from-hp {A : Set} ⦃ hp : HasPrecision A ⦄ =
    IsDecPartialOrder (HasPrecision.isDecPartialOrder hp)
      using () renaming (module Eq to ≈Eq)

  ≈ₛ-isEquivalence : ∀ {A : Set} ⦃ hp : HasPrecision A ⦄ {a : A} → IsEquivalence (_≈ₛ_ {a = a} {a' = a})
  ≈ₛ-isEquivalence ⦃ hp ⦄ = record
    { refl  = ≈-from-hp.≈Eq.refl
    ; sym   = ≈-from-hp.≈Eq.sym
    ; trans = ≈-from-hp.≈Eq.trans
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

  private
    posetₛ : Poset _ _ _
    posetₛ = record { isPartialOrder = isPartialOrder }

  open import Relation.Binary.Properties.Poset posetₛ public
    using ( <-isStrictPartialOrder
          ; <-irrefl; <-asym; <-trans
          ; <-resp-≈; <-respˡ-≈; <-respʳ-≈
          ; mono⇒cong; antimono⇒cong
          )
    renaming ( _<_   to _⊏ₛ_
             ; <⇒≉   to ⊏ₛ⇒≉ₛ
             ; ≤∧≉⇒< to ⊑ₛ∧≉ₛ⇒⊏ₛ
             ; <⇒≱   to ⊏ₛ⇒⋢ₛ
             ; ≤⇒≯   to ⊑ₛ⇒⋣ₛ
             )

_⊏ₛ_ : ∀ {A : Set} ⦃ _ : HasPrecision A ⦄ {a : A} → ⌊ a ⌋ → ⌊ a ⌋ → Set
_⊏ₛ_ = ⊑ₛ._⊏ₛ_
infix 4 _⊏ₛ_


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


  isBoundedMeetSemilattice : ∀ {a} → IsBoundedMeetSemilattice (_≈ₛ_ {a = a} {a' = a}) _⊑ₛ_ _⊓ₛ_ ⊤ₛ
  isBoundedMeetSemilattice = record
    { isMeetSemilattice = record
      { isPartialOrder = ⊑ₛ.isPartialOrder
      ; infimum = λ s₁ s₂ →
                  x∧y≤x (s₁ .↓) (s₂ .↓)
                , x∧y≤y (s₁ .↓) (s₂ .↓)
                , λ _ → ∧-greatest
      }
    ; maximum = ⊤ₛ-max
    }

  open IsBoundedMeetSemilattice (isBoundedMeetSemilattice {a}) public
    using (infimum; isMeetSemilattice; maximum)
    renaming (x∧y≤x to x⊓ₛy⊑ₛx; x∧y≤y to x⊓ₛy⊑ₛy; ∧-greatest to ⊓ₛ-greatest)

-- Full bounded distributive lattice on slices
record SliceLattice (A : Set) ⦃ hp : HasPrecision A ⦄ ⦃ hm : HasMeet A ⦄ ⦃ hj : HasJoin A ⦄ : Set₁ where
  field
    ⊥ₛ              : ∀ {a} → ⌊ a ⌋
    ⊥ₛ-min          : ∀ {a} → Minimum (_⊑ₛ_ {A} ⦃ hp ⦄ {a} {a}) ⊥ₛ
    x⊓ₛy⊑ₛx        : ∀ {a} (s₁ s₂ : ⌊ a ⌋) → _⊓ₛ_ {A} {a} s₁ s₂ ⊑ₛ s₁
    x⊓ₛy⊑ₛy        : ∀ {a} (s₁ s₂ : ⌊ a ⌋) → _⊓ₛ_ {A} {a} s₁ s₂ ⊑ₛ s₂
    ⊓ₛ-greatest     : ∀ {a} {s s₁ s₂ : ⌊ a ⌋} → s ⊑ₛ s₁ → s ⊑ₛ s₂ → s ⊑ₛ _⊓ₛ_ {A} {a} s₁ s₂
    x⊑ₛx⊔ₛy        : ∀ {a} (s₁ s₂ : ⌊ a ⌋) → s₁ ⊑ₛ _⊔ₛ_ {A} {a} s₁ s₂
    y⊑ₛx⊔ₛy        : ∀ {a} (s₁ s₂ : ⌊ a ⌋) → s₂ ⊑ₛ _⊔ₛ_ {A} {a} s₁ s₂
    ⊓ₛ-distribˡ-⊔ₛ  : ∀ {a} (s₁ s₂ s₃ : ⌊ a ⌋) → _⊓ₛ_ {A} {a} s₁ (_⊔ₛ_ {A} {a} s₂ s₃) ≈ₛ _⊔ₛ_ {A} {a} (_⊓ₛ_ {A} {a} s₁ s₂) (_⊓ₛ_ {A} {a} s₁ s₃)
open SliceLattice ⦃...⦄ public using (⊥ₛ)

module ⊑ₛLat {A : Set} ⦃ hp : HasPrecision A ⦄ ⦃ hm : HasMeet A ⦄ ⦃ hj : HasJoin A ⦄ ⦃ sl : SliceLattice A ⦄ {a : A} where

  isBoundedLattice : IsBoundedLattice (_≈ₛ_) (_⊑ₛ_ {A} ⦃ hp ⦄ {a} {a}) _⊔ₛ_ _⊓ₛ_ (⊤ₛ {A} ⦃ hp ⦄ {a}) (SliceLattice.⊥ₛ sl)
  isBoundedLattice = record
    { isLattice = record
      { isPartialOrder = ⊑ₛ.isPartialOrder
      ; supremum       = λ s₁ s₂ → SliceLattice.x⊑ₛx⊔ₛy sl s₁ s₂ , SliceLattice.y⊑ₛx⊔ₛy sl s₁ s₂ , λ _ p q → HasJoin.closure hj p q
      ; infimum        = λ s₁ s₂ → SliceLattice.x⊓ₛy⊑ₛx sl s₁ s₂ , SliceLattice.x⊓ₛy⊑ₛy sl s₁ s₂ , λ s p q → SliceLattice.⊓ₛ-greatest sl {s = s} {s₁} {s₂} p q
      }
    ; maximum   = ⊤ₛ-max
    ; minimum   = SliceLattice.⊥ₛ-min sl
    }

  open IsBoundedLattice isBoundedLattice public
    using (infimum; supremum;
           isBoundedJoinSemilattice; isBoundedMeetSemilattice; isJoinSemilattice; isMeetSemilattice; isLattice)
    renaming (x∧y≤x to x⊓ₛy⊑ₛx; x∧y≤y to x⊓ₛy⊑ₛy; x≤x∨y to x⊑ₛx⊔ₛy; y≤x∨y to y⊑ₛx⊔ₛy;
              ∧-greatest to ⊓ₛ-greatest; ∨-least to ⊔ₛ-least;
              maximum to ⊤ₛ-max; minimum to ⊥ₛ-min)

  isDistributiveLattice : IsDistributiveLattice (_≈ₛ_) (_⊑ₛ_ {A} ⦃ hp ⦄ {a} {a}) _⊔ₛ_ _⊓ₛ_
  isDistributiveLattice = record
    { isLattice    = IsBoundedLattice.isLattice isBoundedLattice
    ; ∧-distribˡ-∨ = SliceLattice.⊓ₛ-distribˡ-⊔ₛ sl
    }

  open IsDistributiveLattice isDistributiveLattice public
    using () renaming (∧-distribˡ-∨ to ⊓ₛ-distribˡ-⊔ₛ)

  -- Derived lattice properties from stdlib Properties modules
  private
    latBundle : LatBundle _ _ _
    latBundle = record { isLattice = isLattice }

    blatBundle : BLatBundle _ _ _
    blatBundle = record { isBoundedLattice = isBoundedLattice }

    dlatBundle : DLatBundle _ _ _
    dlatBundle = record { isDistributiveLattice = isDistributiveLattice }

  open import Relation.Binary.Lattice.Properties.Lattice latBundle public
    using ()
    renaming ( ∨-absorbs-∧ to ⊔ₛ-absorbs-⊓ₛ
             ; ∧-absorbs-∨ to ⊓ₛ-absorbs-⊔ₛ
             ; ∧≤∨         to ⊓ₛ⊑ₛ⊔ₛ
             )

  open import Relation.Binary.Lattice.Properties.BoundedLattice blatBundle public
    using ()
    renaming ( ∧-zeroˡ to ⊓ₛ-zeroˡ
             ; ∧-zeroʳ to ⊓ₛ-zeroʳ
             ; ∧-zero  to ⊓ₛ-zero
             ; ∨-zeroˡ to ⊔ₛ-zeroˡ
             ; ∨-zeroʳ to ⊔ₛ-zeroʳ
             ; ∨-zero  to ⊔ₛ-zero
             )

  open import Relation.Binary.Lattice.Properties.DistributiveLattice dlatBundle public
    using ()
    renaming ( ∧-distribʳ-∨  to ⊓ₛ-distribʳ-⊔ₛ
             ; ∧-distrib-∨   to ⊓ₛ-distrib-⊔ₛ
             ; ∨-distribˡ-∧  to ⊔ₛ-distribˡ-⊓ₛ
             ; ∨-distribʳ-∧  to ⊔ₛ-distribʳ-⊓ₛ
             ; ∨-distrib-∧   to ⊔ₛ-distrib-⊓ₛ
             )
