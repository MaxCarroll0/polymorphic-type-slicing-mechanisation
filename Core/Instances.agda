module Core.Instances where

open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; ¬_; ¬?)
open import Relation.Nullary.Decidable using () renaming (map′ to dec-map)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsEquivalence; IsDecEquivalence; Maximum)
open import Relation.Binary.Bundles using (Poset; DecPoset; DecStrictPartialOrder; Setoid; DecSetoid)
import Relation.Binary.Properties.Poset as PosetProps
import Relation.Binary.Properties.StrictPartialOrder as StrictPosetProps
import Relation.Binary.Properties.Setoid as SetoidProps
import Relation.Binary.Properties.DecSetoid as DecSetoidProps
import Relation.Binary.Construct.NonStrictToStrict
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
  decPoset : DecPoset _ _ _
  decPoset = record {isDecPartialOrder = HasPrecision.isDecPartialOrder hp}
  open DecPoset decPoset public
    hiding (module Eq; _∼_; _≈_; _≉_; _≟_; isEquivalence; ∼-resp-≈; ∼-respˡ-≈; ∼-respʳ-≈)
    renaming ( _≤_  to _⊑_
             ; _≤?_ to _⊑?_
             ; _≥_  to _⊒_
             ; _≰_  to _⋢_
             ; _≱_  to _⋣_
             ; Carrier  to A
             ; ≤-resp-≈ to ⊑-resp-≈
             ; ≤-respʳ-≈ to ⊑-resp⃗≈
             ; ≤-respˡ-≈ to ⊑-respˡ-≈)
  open PosetProps poset public
    hiding (≤-dec⇒isDecPartialOrder; ≤-dec⇒≈-dec)
    renaming ( _<_ to _⊏_
             ; _≮_ to _⊏̸_
             ; <-asym   to ⊏-asym
             ; <-irrefl to ⊏-irrefl
             ; <-trans  to ⊏-trans
             ; <-isStrictPartialOrder to ⊏-isStrictPartialOrder
             ; <-strictPartialOrder   to ⊏-strictPartialOrder
             ; <-resp-≈ to ⊏-resp-≈
             ; <-respˡ-≈ to ⊏-respˡ-≈
             ; <-respʳ-≈ to ⊏-respʳ-≈
             ; <⇒≉   to ⊏⇒≉
             ; ≤⇒≯   to ⊑⇒⊐̸
             ; <⇒≱   to ⊏⇒⋣
             ; ≤∧≉⇒< to ⊑∧≉⇒⊏
             ; ≥-isPartialOrder to ⊒-isPartialOrder
             ; ≥-isPreorder     to ⊒-isPreorder
             ; ≥-poset          to ⊒-poset
             ; ≥-preorder       to ⊒-preorder
             ; ≥-refl      to ⊒-refl
             ; ≥-reflexive to ⊒-reflexive
             ; ≥-antisym   to ⊒-antisym
             ; ≥-trans     to ⊒-trans
             ; ≰-respʳ-≈ to ⋢-respʳ-≈
             ; ≰-respˡ-≈ to ⋢-respˡ-≈
             )
  open PosetProps ⊒-poset public
    hiding ( ≤-dec⇒isDecPartialOrder; ≤-dec⇒≈-dec
           ; ≥-isPartialOrder; ≥-isPreorder; ≥-poset; ≥-preorder
           ; ≥-refl; ≥-reflexive; ≥-antisym; ≥-trans
           ; mono⇒cong; antimono⇒cong)
    renaming ( _<_ to _⊐_
             ; _≮_ to _⊐̸_
             ; <-asym   to ⊐-asym
             ; <-irrefl to ⊐-irrefl
             ; <-trans  to ⊐-trans
             ; <-isStrictPartialOrder to ⊐-isStrictPartialOrder
             ; <-strictPartialOrder   to ⊐-strictPartialOrder
             ; <-resp-≈ to ⊐-resp-≈
             ; <-respˡ-≈ to ⊐-respˡ-≈
             ; <-respʳ-≈ to ⊐-respʳ-≈
             ; <⇒≉   to ⊐⇒≉
             ; ≤⇒≯   to ⊒⇒⊏̸
             ; <⇒≱   to ⊐⇒⋢
             ; ≤∧≉⇒< to ⊒∧≉⇒⊐
             ; ≰-respʳ-≈ to ⋣-respʳ-≈
             ; ≰-respˡ-≈ to ⋣-respˡ-≈
             )

  ⊒-decPartialOrder : DecPoset _ _ _
  ⊒-decPartialOrder =
    record { isDecPartialOrder = ⊒Props.≤-dec⇒isDecPartialOrder (λ x y → HasPrecision._⊑?_ hp y x) }
      where module ⊒Props = PosetProps ⊒-poset
  open DecPoset ⊒-decPartialOrder public
    using ()
    renaming ( _≤?_ to _⊒?_ 
             ; decPreorder       to ⊒-decPreorder
             ; isDecPartialOrder to ⊒-isDecPartialOrder
             ; isDecPreorder     to ⊒-isDecPreorder
             ; ≤-resp-≈ to ⊒-resp-≈
             ; ≤-respʳ-≈ to ⊒-respʳ-≈
             ; ≤-respˡ-≈ to ⊒-respˡ-≈)
    
  ⊏-decStrictPartialOrder = record { isDecStrictPartialOrder = TS.<-isDecStrictPartialOrder isDecPartialOrder }
    where module TS  = Relation.Binary.Construct.NonStrictToStrict (HasPrecision._≈_ hp) (HasPrecision._⊑_ hp)
  open DecStrictPartialOrder ⊏-decStrictPartialOrder public
    using ()
    renaming ( _<?_ to _⊏?_
             ; isDecStrictPartialOrder to ⊏-isDecStrictPartialOrder) 
  ⊐-decStrictPartialOrder = record { isDecStrictPartialOrder = TS⊒.<-isDecStrictPartialOrder ⊒-isDecPartialOrder }
    where module TS⊒ = Relation.Binary.Construct.NonStrictToStrict (HasPrecision._≈_ hp) _⊒_
  open DecStrictPartialOrder ⊐-decStrictPartialOrder public
    using ()
    renaming ( _<?_ to _⊐?_
             ; isDecStrictPartialOrder to ⊐-isDecStrictPartialOrder)

  _⋢?_ : ∀ x y → Dec (x ⋢ y)
  x ⋢? y = ¬? (HasPrecision._⊑?_ hp x y)
  _⋣?_ : ∀ x y → Dec (x ⋣ y)
  x ⋣? y = ¬? (x ⊒? y)
  _⊏̸?_ : ∀ x y → Dec (x ⊏̸ y)
  x ⊏̸? y = ¬? (x ⊏? y)
  _⊐̸?_ : ∀ x y → Dec (x ⊐̸ y)
  x ⊐̸? y = ¬? (x ⊐? y)


module ≈ {A : Set} ⦃ hp : HasPrecision A ⦄ where
  private module E = IsDecPartialOrder (HasPrecision.isDecPartialOrder hp)
  open E.Eq public
  open SetoidProps record { isEquivalence = isEquivalence } public
  open DecSetoidProps record { isDecEquivalence = isDecEquivalence } public

_≈?_ = ≈._≟_

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
    renaming (∧-greatest to greatest; x∧y≤x to x⊓y⊑x; x∧y≤y to x⊓y⊑y)
  isMeetSemilattice = HasMeetSemilattice.isMeetSemilattice hms

  private
    meetSL : MeetSemilattice _ _ _
    meetSL = record { isMeetSemilattice = isMeetSemilattice }

  open import Relation.Binary.Lattice.Properties.MeetSemilattice meetSL public
    renaming ( ∧-comm       to comm
             ; ∧-assoc      to assoc
             ; ∧-idempotent to idempotent
             ; ∧-monotonic  to monotonic
             ; ∧-cong       to cong
             ; y≤x⇒x∧y≈y    to y⊑x⇒x⊓y≈y
             )

record HasJoinSemilattice (A : Set) ⦃ hp : HasPrecision A ⦄ ⦃ _ : HasJoin A ⦄ : Set₁ where
  field isJoinSemilattice : IsJoinSemilattice (HasPrecision._≈_ hp) _⊑_ _⊔_
open HasJoinSemilattice ⦃...⦄ public hiding (isJoinSemilattice)

module ⊔Lat {A : Set} ⦃ hp : HasPrecision A ⦄ ⦃ hj : HasJoin A ⦄ ⦃ hjs : HasJoinSemilattice A ⦄ where
  open IsJoinSemilattice (HasJoinSemilattice.isJoinSemilattice hjs) public
    using (supremum)
    renaming (∨-least to least; x≤x∨y to x⊑x⊔y; y≤x∨y to y⊑x⊔y)
  isJoinSemilattice = HasJoinSemilattice.isJoinSemilattice hjs

  private
    joinSL : JoinSemilattice _ _ _
    joinSL = record { isJoinSemilattice = isJoinSemilattice }
  
  open import Relation.Binary.Lattice.Properties.JoinSemilattice joinSL public
    renaming ( ∨-comm       to comm
             ; ∨-assoc      to assoc
             ; ∨-idempotent to idempotent
             ; ∨-monotonic  to monotonic
             ; ∨-cong       to cong
             ; x≤y⇒x∨y≈y    to x⊑y⇒x⊔y≈y
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

module ≈ₛ {A : Set} ⦃ hp : HasPrecision A ⦄ {a : A} where
  open IsDecEquivalence (≈ₛ-isDecEquivalence {A} ⦃ hp ⦄ {a}) public
  open SetoidProps record { isEquivalence = ≈ₛ-isEquivalence {A} ⦃ hp ⦄ {a} } public
  open DecSetoidProps record { isDecEquivalence = ≈ₛ-isDecEquivalence {A} ⦃ hp ⦄ {a} } public

-- TODO remove code duplication with ⊑
module ⊑ₛ {A : Set} ⦃ hp : HasPrecision A ⦄ {a : A} where
  open DecPoset record {isDecPartialOrder = ⊑ₛ-isDecPartialOrder {a = a}} public
    hiding (module Eq; _∼_; _≈_; _≉_; _≟_; isEquivalence; ∼-resp-≈; ∼-respˡ-≈; ∼-respʳ-≈)
    renaming ( _≤_  to _⊑_
             ; _≤?_ to _⊑?_
             ; _≥_  to _⊒_
             ; _≰_  to _⋢_
             ; _≱_  to _⋣_
             ; Carrier  to A
             ; ≤-resp-≈ to ⊑-resp-≈
             ; ≤-respʳ-≈ to ⊑-resp⃗≈
             ; ≤-respˡ-≈ to ⊑-respˡ-≈)

  open PosetProps poset public
    hiding (≤-dec⇒isDecPartialOrder; ≤-dec⇒≈-dec)
    renaming ( _<_ to _⊏_
             ; _≮_ to _⊏̸_
             ; <-asym   to ⊏-asym
             ; <-irrefl to ⊏-irrefl
             ; <-trans  to ⊏-trans
             ; <-isStrictPartialOrder to ⊏-isStrictPartialOrder
             ; <-strictPartialOrder   to ⊏-strictPartialOrder
             ; <-resp-≈ to ⊏ₛ-resp-≈
             ; <-respˡ-≈ to ⊏ₛ-respˡ-≈
             ; <-respʳ-≈ to ⊏ₛ-respʳ-≈
             ; <⇒≉   to ⊏⇒≉
             ; ≤⇒≯   to ⊑⇒⊐̸
             ; <⇒≱   to ⊏⇒⋣
             ; ≤∧≉⇒< to ⊑∧≉⇒⊏
             ; ≥-isPartialOrder to ⊒-isPartialOrder
             ; ≥-isPreorder     to ⊒-isPreorder
             ; ≥-poset          to ⊒-poset
             ; ≥-preorder       to ⊒-preorder
             ; ≥-refl      to ⊒-refl
             ; ≥-reflexive to ⊒-reflexive
             ; ≥-antisym   to ⊒-antisym
             ; ≥-trans     to ⊒-trans
             ; ≰-respʳ-≈ to ⋢-respʳ-≈
             ; ≰-respˡ-≈ to ⋢-respˡ-≈
             )
  open PosetProps ⊒-poset public
    hiding ( ≤-dec⇒isDecPartialOrder; ≤-dec⇒≈-dec
           ; ≥-isPartialOrder; ≥-isPreorder; ≥-poset; ≥-preorder
           ; ≥-refl; ≥-reflexive; ≥-antisym; ≥-trans
           ; mono⇒cong; antimono⇒cong)
    renaming ( _<_ to _⊐_
             ; _≮_ to _⊐̸_
             ; <-asym   to ⊐-asym
             ; <-irrefl to ⊐-irrefl
             ; <-trans  to ⊐-trans
             ; <-isStrictPartialOrder to ⊐-isStrictPartialOrder
             ; <-strictPartialOrder   to ⊐-strictPartialOrder
             ; <-resp-≈ to ⊐-resp-≈
             ; <-respˡ-≈ to ⊐-respˡ-≈
             ; <-respʳ-≈ to ⊐-respʳ-≈
             ; <⇒≉   to ⊐⇒≉
             ; ≤⇒≯   to ⊒⇒⊏̸
             ; <⇒≱   to ⊐⇒⋣
             ; ≤∧≉⇒< to ⊒∧≉⇒⊐
             ; ≰-respʳ-≈ to ⋣-respʳ-≈
             ; ≰-respˡ-≈ to ⋣-respˡ-≈
             )

  ⊒-decPartialOrder : DecPoset _ _ _
  ⊒-decPartialOrder =
    record { isDecPartialOrder = ⊒Props.≤-dec⇒isDecPartialOrder (λ x y → _⊑ₛ?_ y x) }
      where module ⊒Props = PosetProps ⊒-poset
  open DecPoset ⊒-decPartialOrder public
    using ()
    renaming ( _≤?_ to _⊒?_
             ; decPreorder       to ⊒-decPreorder
             ; isDecPartialOrder to ⊒-isDecPartialOrder
             ; isDecPreorder     to ⊒-isDecPreorder
             ; ≤-resp-≈ to ⊒-resp-≈
             ; ≤-respʳ-≈ to ⊒-respʳ-≈
             ; ≤-respˡ-≈ to ⊒-respˡ-≈)

  ⊏-decStrictPartialOrder = record { isDecStrictPartialOrder = TS.<-isDecStrictPartialOrder isDecPartialOrder }
    where module TS = Relation.Binary.Construct.NonStrictToStrict (_≈ₛ_ {a = a} {a' = a}) (_⊑ₛ_ {a = a} {a' = a})
  open DecStrictPartialOrder ⊏-decStrictPartialOrder public
    using ()
    renaming ( _<?_ to _⊏?_
             ; isDecStrictPartialOrder to ⊏ₛ-isDecStrictPartialOrder)
  ⊐-decStrictPartialOrder = record { isDecStrictPartialOrder = TS⊒.<-isDecStrictPartialOrder ⊒-isDecPartialOrder }
    where module TS⊒ = Relation.Binary.Construct.NonStrictToStrict (_≈ₛ_ {a = a} {a' = a}) (λ x y → _⊑ₛ_ {a = a} {a' = a} y x)
  open DecStrictPartialOrder ⊐-decStrictPartialOrder public
    using ()
    renaming ( _<?_ to _⊐?_
             ; isDecStrictPartialOrder to ⊐ₛ-isDecStrictPartialOrder)

  _⋢?_ : ∀ (s₁ s₂ : ⌊ a ⌋) → Dec (s₁ ⋢ s₂)
  s₁ ⋢? s₂ = ¬? (s₁ ⊑ₛ? s₂)
  _⋣?_ : ∀ (s₁ s₂ : ⌊ a ⌋) → Dec (s₁ ⋣ s₂)
  s₁ ⋣? s₂ = ¬? (s₁ ⊒? s₂)
  _⊏̸?_ : ∀ (s₁ s₂ : ⌊ a ⌋) → Dec (s₁ ⊏̸ s₂)
  s₁ ⊏̸? s₂ = ¬? (s₁ ⊏? s₂)
  _⊐̸?_ : ∀ (s₁ s₂ : ⌊ a ⌋) → Dec (s₁ ⊐̸ s₂)
  s₁ ⊐̸? s₂ = ¬? (s₁ ⊐? s₂)


_⊒_ = ⊑._⊒_
_⊏_ = ⊑._⊏_
_⊐_ = ⊑._⊐_
_⋣_ = ⊑._⋣_
_⊏̸_ = ⊑._⊏̸_
_⊐̸_ = ⊑._⊐̸_

_⊒?_ = ⊑._⊒?_
_⊏?_ = ⊑._⊏?_
_⊐?_ = ⊑._⊐?_
_⋣?_ = ⊑._⋣?_
_⊏̸?_ = ⊑._⊏̸?_
_⊐̸?_ = ⊑._⊐̸?_

infix 4 _⊒_ _⊏_ _⊐_ _⋣_ _⊏̸_ _⊐̸_

_⊒ₛ_ = ⊑ₛ._⊒_
_⊏ₛ_ = ⊑ₛ._⊏_
_⊐ₛ_ = ⊑ₛ._⊐_
_⋣ₛ_ = ⊑ₛ._⋣_
_⊏̸ₛ_ = ⊑ₛ._⊏̸_
_⊐̸ₛ_ = ⊑ₛ._⊐̸_

_⊒ₛ?_ = ⊑ₛ._⊒?_
_⊏ₛ?_ = ⊑ₛ._⊏?_
_⊐ₛ?_ = ⊑ₛ._⊐?_
_⋣ₛ?_ = ⊑ₛ._⋣?_
_⊏̸ₛ?_ = ⊑ₛ._⊏̸?_
_⊐̸ₛ?_ = ⊑ₛ._⊐̸?_

infix 4 _⊒ₛ_ _⊏ₛ_ _⊐ₛ_ _⋣ₛ_ _⊏̸ₛ_ _⊐̸ₛ_


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
    ⊥ₛ             : ∀ {a} → ⌊ a ⌋
    ⊥ₛ-min         : ∀ {a} → Minimum (_⊑ₛ_ {A} ⦃ hp ⦄ {a} {a}) ⊥ₛ
    x⊓ₛy⊑ₛx        : ∀ {a} (s₁ s₂ : ⌊ a ⌋) → _⊓ₛ_ {A} {a} s₁ s₂ ⊑ₛ s₁
    x⊓ₛy⊑ₛy        : ∀ {a} (s₁ s₂ : ⌊ a ⌋) → _⊓ₛ_ {A} {a} s₁ s₂ ⊑ₛ s₂
    ⊓ₛ-greatest    : ∀ {a} {s s₁ s₂ : ⌊ a ⌋} → s ⊑ₛ s₁ → s ⊑ₛ s₂ → s ⊑ₛ _⊓ₛ_ {A} {a} s₁ s₂
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

  private
    latBundle : LatBundle _ _ _
    latBundle = record { isLattice = isLattice }

    blatBundle : BLatBundle _ _ _
    blatBundle = record { isBoundedLattice = isBoundedLattice }

    dlatBundle : DLatBundle _ _ _
    dlatBundle = record { isDistributiveLattice = isDistributiveLattice }

  open import Relation.Binary.Lattice.Properties.Lattice latBundle public
    renaming ( ∨-absorbs-∧ to ⊔ₛ-absorbs-⊓ₛ
             ; ∧-absorbs-∨ to ⊓ₛ-absorbs-⊔ₛ
             ; ∧≤∨         to ⊓ₛ⊑ₛ⊔ₛ)
  open import Relation.Binary.Lattice.Properties.BoundedLattice blatBundle public
    renaming ( ∧-zeroˡ to ⊓ₛ-zeroˡ
             ; ∧-zeroʳ to ⊓ₛ-zeroʳ
             ; ∧-zero  to ⊓ₛ-zero
             ; ∨-zeroˡ to ⊔ₛ-zeroˡ
             ; ∨-zeroʳ to ⊔ₛ-zeroʳ
             ; ∨-zero  to ⊔ₛ-zero)

  open import Relation.Binary.Lattice.Properties.DistributiveLattice dlatBundle public
    using ()
    renaming ( ∧-distribʳ-∨  to ⊓ₛ-distribʳ-⊔ₛ
             ; ∧-distrib-∨   to ⊓ₛ-distrib-⊔ₛ
             ; ∨-distribˡ-∧  to ⊔ₛ-distribˡ-⊓ₛ
             ; ∨-distribʳ-∧  to ⊔ₛ-distribʳ-⊓ₛ
             ; ∨-distrib-∧   to ⊔ₛ-distrib-⊓ₛ)
