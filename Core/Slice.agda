open import Data.Product using (_,_)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; Maximum; IsEquivalence; IsDecEquivalence)
open import Relation.Binary.Lattice using (IsMeetSemilattice; IsBoundedMeetSemilattice)
open import Relation.Nullary using (Dec; yes; no)

-- Lift partial order to a partial order on elements less than some top
module Core.Slice
  {A : Set}
  {_≈_ _⊑_ : A → A → Set}
  (O : IsDecPartialOrder _≈_ _⊑_)
  where

  open IsDecPartialOrder O

  -- A slice of 'a' is any element below it
  record SliceOf (a : A) : Set where
    constructor _isSlice_
    field
      ↓     : A
      proof : ↓ ⊑ a

  syntax SliceOf a = ⌊ a ⌋
  infix 3 _isSlice_

  open SliceOf public

  -- Lifted equality
  _≈ₛ_ : ∀ {a a'} → ⌊ a ⌋ → ⌊ a' ⌋ → Set
  s₁ ≈ₛ s₂ = s₁ .↓ ≈ s₂ .↓

  _≈ₛ?_ : ∀ {a} (s₁ s₂ : ⌊ a ⌋) → Dec (s₁ ≈ₛ s₂)
  s₁ ≈ₛ? s₂ = s₁ .↓ ≟ s₂ .↓

  private
    ≈ₛ-isEquivalence : ∀ {a} → IsEquivalence (_≈ₛ_ {a} {a})
    ≈ₛ-isEquivalence = record
                      { refl = Eq.refl
                      ; sym = Eq.sym
                      ; trans = Eq.trans
                      }

    ≈ₛ-isDecEquivalence : ∀ {a} → IsDecEquivalence (_≈ₛ_ {a} {a})
    ≈ₛ-isDecEquivalence = record
                          { isEquivalence = ≈ₛ-isEquivalence
                          ; _≟_           = _≈ₛ?_
                          }

  module ≈ₛ {a : A} = IsDecEquivalence (≈ₛ-isDecEquivalence {a})

  -- Lifted ordering on slices
  _⊑ₛ_ : ∀ {a a'} → ⌊ a ⌋ → ⌊ a' ⌋ → Set
  s₁ ⊑ₛ s₂ = s₁ .↓ ⊑ s₂ .↓

  infix 4 _⊑ₛ_

  -- Preserve Partial Order
  private
    ⊑ₛ-isPartialOrder : ∀ {a} → IsPartialOrder (_≈ₛ_ {a} {a}) _⊑ₛ_
    ⊑ₛ-isPartialOrder = record
                        { isPreorder = record
                                       { isEquivalence = ≈ₛ-isEquivalence
                                       ; reflexive = reflexive
                                       ; trans     = trans
                                       }
                        ; antisym = antisym
                        }

  _⊑ₛ?_ : ∀ {a} (s₁ s₂ : ⌊ a ⌋) → Dec (s₁ ⊑ₛ s₂)
  s₁ ⊑ₛ? s₂ = s₁ .↓ ≤? s₂ .↓

  private
    ⊑ₛ-isDecPartialOrder : ∀ {a} → IsDecPartialOrder (_≈ₛ_ {a} {a}) _⊑ₛ_
    ⊑ₛ-isDecPartialOrder = record
                           { isPartialOrder = ⊑ₛ-isPartialOrder
                           ; _≟_            = _≈ₛ?_
                           ; _≤?_           = _⊑ₛ?_
                           }

  module ⊑ₛ {a : A} where
    open IsDecPartialOrder (⊑ₛ-isDecPartialOrder {a}) public
      hiding (module Eq; isEquivalence; ≲-resp-≈; ≲-respˡ-≈; ≲-respʳ-≈; _≟_; _≤?_)
      renaming (≤-resp-≈ to ⊑ₛ-resp-≈ₛ; ≤-respˡ-≈ to ⊑ₛ-respˡ-≈ₛ; ≤-respʳ-≈ to ⊑ₛ-respʳ-≈ₛ)
    
  ↑ : ∀ {a' a} → a' ⊑ a → ⌊ a ⌋
  ↑ {a'} p = a' isSlice p

  -- Top of slice lattice
  ⊤ₛ : ∀ {a} → ⌊ a ⌋
  ⊤ₛ {a} = ↑ (reflexive Eq.refl)

  ⊤ₛ-max : ∀ {a} → Maximum _⊑ₛ_ (⊤ₛ {a})
  ⊤ₛ-max s = s .proof

  -- Weaken a slice to a larger bound
  weaken : ∀ {a a'} → a ⊑ a' → ⌊ a ⌋ → ⌊ a' ⌋
  weaken p s = s .↓ isSlice trans (s .proof) p

  weaken-identity : ∀ {a a'} {s : ⌊ a ⌋} {p : a ⊑ a'} → (weaken p s) ≈ₛ s
  weaken-identity = Eq.refl  

  -- Lift a meet semilattice to a bounded meet lattice
  module LiftMeetSemilattice
    {_⊓_ : A → A → A}
    (M : IsMeetSemilattice _≈_ _⊑_ _⊓_)
    where
    open IsMeetSemilattice M hiding (trans; isPartialOrder)

    -- Lifted meet
    _⊓ₛ_ : ∀ {a} → ⌊ a ⌋ → ⌊ a ⌋ → ⌊ a ⌋
    s₁ ⊓ₛ s₂ = s₁ .↓ ⊓ s₂ .↓ isSlice trans (x∧y≤x (s₁ .↓) (s₂ .↓)) (s₁ .proof)

    private
      isBoundedMeetSemilattice' : ∀ {a} → IsBoundedMeetSemilattice (_≈ₛ_ {a}) _⊑ₛ_ _⊓ₛ_ ⊤ₛ
      isBoundedMeetSemilattice' = record
                                  { isMeetSemilattice = record
                                                        { isPartialOrder = ⊑ₛ-isPartialOrder
                                                        ; infimum = λ s₁ s₂ →
                                                                    x∧y≤x (s₁ .↓) (s₂ .↓)
                                                                  , x∧y≤y (s₁ .↓) (s₂ .↓)
                                                                  , λ _ → ∧-greatest
                                                        }
                                  ; maximum = ⊤ₛ-max
                                  }

    module ⊓ₛ {a : A} where
      open IsBoundedMeetSemilattice (isBoundedMeetSemilattice' {a}) public
        using (infimum; isMeetSemilattice; maximum)
        renaming (x∧y≤x to x⊓ₛy⊑ₛx; x∧y≤y to x⊓ₛy⊑ₛy; ∧-greatest to ⊓ₛ-greatest)

      isBoundedMeetSemilattice = isBoundedMeetSemilattice'


    
