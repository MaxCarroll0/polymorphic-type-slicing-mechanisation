-- Cursor-facing composition of context classification with minimal full
-- type slicing.
module Slicing.Interaction where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_ ) renaming (_×_ to _∧_)
open import Core
open import Semantics.Statics
open import Semantics.Statics.FocusClassification
open import Slicing.Full.Full

Queries : ∀ {n Γ C e p}
  → FocusClassifications n Γ C e p → Set
Queries (syn-only (syn-class _ _ τ _ _)) = ⌊ τ ⌋
Queries (ana-only (ana-class _ _ τ _ _)) = ⌊ τ ⌋
Queries (both (syn-class _ _ τˢ _ _) (ana-class _ _ τᵃ _ _)) =
  ⌊ τˢ ⌋ ∧ ⌊ τᵃ ⌋

MinimalSlices : ∀ {n Γ C e τ₀}
  → (fc : FocusClassifications n Γ C e (synPos τ₀))
  → Queries fc → Set
MinimalSlices (syn-only (syn-class _ _ _ cls focus)) u =
  MinSynTypeSlice cls focus u
MinimalSlices (ana-only (ana-class _ _ _ cls _)) u =
  MinAnaTypeSlice cls u
MinimalSlices
  (both (syn-class _ _ _ scls sfocus)
        (ana-class _ _ _ acls _))
  (uˢ , uᵃ) =
  MinSynTypeSlice scls sfocus uˢ ∧ MinAnaTypeSlice acls uᵃ

minimal-slices : ∀ {n Γ C e τ₀}
  → (fc : FocusClassifications n Γ C e (synPos τ₀))
  → (q : Queries fc) → MinimalSlices fc q
minimal-slices (syn-only (syn-class _ _ _ cls focus)) q =
  min-syn-type cls focus q
minimal-slices (ana-only (ana-class _ _ _ cls _)) q =
  min-ana-type cls q
minimal-slices
  (both (syn-class _ _ _ scls sfocus)
        (ana-class _ _ _ acls _))
  (qˢ , qᵃ) =
  min-syn-type scls sfocus qˢ , min-ana-type acls qᵃ

slice-focus : ∀ {n Γ C e τ₀}
  → (D : n , Γ ⊢ plug C e ⇑ τ₀)
  → (q : Queries (classify-focus C D))
  → MinimalSlices (classify-focus C D) q
slice-focus {C = C} D q = minimal-slices (classify-focus C D) q
