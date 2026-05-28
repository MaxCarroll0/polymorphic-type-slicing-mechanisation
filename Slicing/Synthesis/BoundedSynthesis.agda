open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Core
open import Semantics.Statics
open import Slicing.Synthesis.Synthesis
open import Core.Assms.BiasedPrecision using (_≼a_; _≼ₛ_)

-- Bounded variant of SynSlice carrying a lower bound on the used assumptions (via the biased
-- precision _≼ₛ_): a slice is bounded-minimal if it is minimal among those whose context
-- covers the bound. Intended to characterise the minimal slices that can be combined into
-- minimal slices of compound expressions - in particular products, where naively pairing two
-- minimal slices is not itself minimal (see Counterexamples.¬&syn-preserves-minimality). The
-- product rule in `Slicing.Synthesis.SynSliceCalc.min&` makes each factor see the other's
-- needed assumptions, which is exactly the bound this module is built around. EXPLORATORY.
module Slicing.Synthesis.BoundedSynthesis where

-- Bounded minimal syn slice: minimal among slices satisfying a lower bound
-- i.e. IF the expression uses a variable it must use at least information from the lower bound
BoundedIsMinimal : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ} {υ : ⌊ τ ⌋}
                   → ⌊ Γ ⌋ → SynSlice D ◂ υ → Set
BoundedIsMinimal {D = D} {υ = υ} lb s =
  ∀ (s' : SynSlice D ◂ υ) → lb ≼ₛ s' ↓γₛ → s' ⊑ s → s ≈ s'

BoundedMinSynSlice : ∀ {n Γ e τ} (D : n , Γ ⊢ e ⇑ τ) (υ : ⌊ τ ⌋)
                     → ⌊ Γ ⌋ → Set
BoundedMinSynSlice D υ lb =
  Σ[ s ∈ SynSlice D ◂ υ ]
    (lb ≼ₛ s ↓γₛ) ∧ BoundedIsMinimal lb s
