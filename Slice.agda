-- Generic slice structure parameterized over a partial order with slice-relative bottom
module Slice
  {A : Set}
  (_≤_ : A → A → Set)
  (⊥-of : A → A)
  (⊥-of-≤ : ∀ a → ⊥-of a ≤ a)
  (⊥-of-min : ∀ {a' a} → a' ≤ a → ⊥-of a ≤ a')
  (≤-refl : ∀ {a} → a ≤ a)
  (≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c)
  where
  
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  
  -- A slice of 'a' is any element below it
  record SliceOf (a : A) : Set where
    constructor _isSlice_
    field
      ↓     : A
      proof : ↓ ≤ a
  
  syntax SliceOf a = ⌊ a ⌋
  infix 3 _isSlice_
  
  open SliceOf public
  
  -- Lifted ordering on slices
  _⊑ₛ_ : ∀ {a} → ⌊ a ⌋ → ⌊ a ⌋ → Set
  s₁ ⊑ₛ s₂ = s₁ .↓ ≤ s₂ .↓
  
  infix 4 _⊑ₛ_
  
  -- Top and bottom of slice lattice
  ⊤ₛ : ∀ {a} → ⌊ a ⌋
  ⊤ₛ {a} = a isSlice ≤-refl
  
  ⊥ₛ : ∀ {a} → ⌊ a ⌋
  ⊥ₛ {a} = ⊥-of a isSlice ⊥-of-≤ a
  
  -- Weaken a slice to a larger bound
  weaken : ∀ {a a'} → a ≤ a' → ⌊ a ⌋ → ⌊ a' ⌋
  weaken p s = s .↓ isSlice ≤-trans (s .proof) p
  
  weaken-identity : ∀ {a a'} {s : ⌊ a ⌋} {p : a ≤ a'} → (weaken p s) .↓ ≡ s .↓
  weaken-identity = refl
  
  -- Bottom is minimum for any slice
  ⊥ₛ-min : ∀ {a} (s : ⌊ a ⌋) → ⊥ₛ ⊑ₛ s
  ⊥ₛ-min s = ⊥-of-min (s .proof)
  
