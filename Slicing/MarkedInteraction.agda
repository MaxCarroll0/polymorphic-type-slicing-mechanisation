-- End-to-end cursor selection on marked slices.  The result is the requested
-- three-way sum: one full synthesis slice, one analysis slice, or both.
module Slicing.MarkedInteraction where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_ ) renaming (_×_ to _∧_)
open import Core
open import Semantics.Statics
open import Semantics.Statics.FocusClassification
import Semantics.Marking.FocusClassification as M
open import Slicing.Interaction
open import Slicing.Marked

MarkedMinimalSlices : ∀ {n Γ C e τ₀}
  → (fc : FocusClassifications n Γ C e (synPos τ₀))
  → Queries fc → Set
MarkedMinimalSlices (syn-only (syn-class _ _ _ cls focus)) u =
  MinMarkedSynTypeSlice cls focus u
MarkedMinimalSlices (ana-only (ana-class _ _ _ cls _)) u =
  MinMarkedAnaSlice cls u
MarkedMinimalSlices
  (both (syn-class _ _ _ scls sfocus)
        (ana-class _ _ _ acls _))
  (uˢ , uᵃ) =
  MinMarkedSynTypeSlice scls sfocus uˢ ∧ MinMarkedAnaSlice acls uᵃ

mark-minimal-slices : ∀ {n Γ C e τ₀}
  → (fc : FocusClassifications n Γ C e (synPos τ₀))
  → (q : Queries fc)
  → MinimalSlices fc q
  → MarkedMinimalSlices fc q
mark-minimal-slices (syn-only (syn-class _ _ _ cls focus)) q s =
  mark-min-syn-type-slice s
mark-minimal-slices (ana-only (ana-class _ _ _ cls focus)) q s =
  mark-min-ana-slice s
mark-minimal-slices
  (both (syn-class _ _ _ scls sfocus)
        (ana-class _ _ _ acls afocus))
  (qˢ , qᵃ) (sˢ , sᵃ) =
  mark-min-syn-type-slice sˢ , mark-min-ana-slice sᵃ

record MarkedInteractionResult
    {n : ℕ} {Γ : Assms} {C : Ctx} {e : Exp} {τ₀ : Typ}
    (fc : FocusClassifications n Γ C e (synPos τ₀))
    (q : Queries fc) : Set where
  field
    classifications : M.MarkedFocusClassifications n Γ C e (synPos τ₀)
    slices          : MarkedMinimalSlices fc q
open MarkedInteractionResult public

marked-minimal-slices : ∀ {n Γ C e τ₀}
  → (fc : FocusClassifications n Γ C e (synPos τ₀))
  → (q : Queries fc) → MarkedMinimalSlices fc q
marked-minimal-slices fc q = mark-minimal-slices fc q (minimal-slices fc q)

-- The requested composition from a syntactic decomposition, a fixed initial
-- typing derivation, and valid queries to exactly one of the three result
-- shapes above.
slice-marked-focus : ∀ {n Γ C e τ₀}
  → (D : n , Γ ⊢ plug C e ⇑ τ₀)
  → (q : Queries (classify-focus C D))
  → MarkedInteractionResult (classify-focus C D) q
slice-marked-focus {C = C} D q = record
  { classifications = M.mark-classifications (classify-focus C D)
  ; slices = marked-minimal-slices (classify-focus C D) q
  }
