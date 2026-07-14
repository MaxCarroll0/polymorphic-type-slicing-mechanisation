open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax) renaming (_×_ to _∧_)
open import Function using (_on_)
import Relation.Binary.Construct.On as On
open import Core
open import Semantics.Statics
open import Slicing.Synthesis.Synthesis using (SynSlice_◂_; IsMinimal)
open import Slicing.Analysis.Analysis using
  (AnaSlice; AnaPosSlice; MinAnaSlice; MinAnaPosSlice)

-- Full type slices (POPL, Definition 7.1).  Unlike a focused synthesis
-- slice, a full slice also explains how the assumptions used at the focus
-- are supplied by the surrounding context and its external assumptions.
module Slicing.Full.Full where

private
  instance
    ctx-assms-precision : HasPrecision (Ctx ∧ Assms)
    ctx-assms-precision = prod-precision

    full-data-precision : HasPrecision ((Ctx ∧ Assms) ∧ Exp)
    full-data-precision = prod-precision

    full-pos-data-precision : HasPrecision (((Ctx ∧ Assms) ∧ Exp) ∧ Typ)
    full-pos-data-precision = prod-precision

-- The focus assumptions and focus result type are witnesses: they are not
-- part of the order on full slices.  The context may provide assumptions
-- more precise than the ones selected by the focused SynSlice, so we retain
-- both the focused derivation and the derivation powered by the context.
record SynTypeSlice
    {n : ℕ} {Γ₀ : Assms} {C : Ctx} {n' : ℕ} {Γ : Assms} {e : Exp} {τ τₚ : Typ}
    (Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇒mode τ ])
    (D : n' , Γ ⊢ e ⇑ τ) (u : ⌊ τ ⌋) : Set where
  field
    κ          : ⌊ C ⌋
    γ          : ⌊ Γ₀ ⌋
    outer      : ⌊ τₚ ⌋
    focus-slice : SynSlice D ◂ u
    powered     :
      Σ[ n'' ∈ ℕ ] Σ[ Γᶠ ∈ ⌊ Γ ⌋ ] Σ[ φᶠ ∈ ⌊ τ ⌋ ]
        (SynSlice_◂_.↓γₛ focus-slice ⊑ₛ Γᶠ) ∧
        (n , γ .↓ ⊢ κ .↓ at synPos (outer .↓) ▷ n'' , Γᶠ .↓ [ ⇒mode (φᶠ .↓) ]) ∧
        (n'' , Γᶠ .↓ ⊢ SynSlice_◂_.↓σ focus-slice ⇑ φᶠ .↓)

  data↓ : (Ctx ∧ Assms) ∧ Exp
  data↓ = (κ .↓ , γ .↓) , SynSlice_◂_.↓σ focus-slice

open SynTypeSlice public

instance
  syn-type-slice-precision :
    ∀ {n Γ₀ C n' Γ e τ τₚ}
      {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇒mode τ ]}
      {D : n' , Γ ⊢ e ⇑ τ} {u}
      → HasPrecision (SynTypeSlice Cls D u)
  syn-type-slice-precision = record
    { _≈_               = _≈_ on data↓
    ; _⊑_               = _⊑_ on data↓
    ; isDecPartialOrder =
        On.isDecPartialOrder data↓
          (HasPrecision.isDecPartialOrder full-data-precision)
    }

MinSynTypeSlice :
  ∀ {n Γ₀ C n' Γ e τ τₚ}
    (Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇒mode τ ])
    (D : n' , Γ ⊢ e ⇑ τ) → ⌊ τ ⌋ → Set
MinSynTypeSlice Cls D u = Σ[ s ∈ SynTypeSlice Cls D u ] IsMinimal s

-- The analysing-position variant is needed while recursively traversing a
-- synthesis context (most notably when the focus is an application argument).
-- Its demanded outer type is minimised along with the context and focus term.
record SynPosTypeSlice
    {n : ℕ} {Γ₀ : Assms} {C : Ctx} {n' : ℕ} {Γ : Assms} {e : Exp} {τ τₚ : Typ}
    (Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇒mode τ ])
    (D : n' , Γ ⊢ e ⇑ τ) (u : ⌊ τ ⌋) : Set where
  field
    pos-κ           : ⌊ C ⌋
    pos-γ           : ⌊ Γ₀ ⌋
    pos-outer       : ⌊ τₚ ⌋
    pos-focus-slice : SynSlice D ◂ u
    pos-powered     :
      Σ[ n'' ∈ ℕ ] Σ[ Γᶠ ∈ ⌊ Γ ⌋ ] Σ[ φᶠ ∈ ⌊ τ ⌋ ]
        (SynSlice_◂_.↓γₛ pos-focus-slice ⊑ₛ Γᶠ) ∧
        (n , pos-γ .↓ ⊢ pos-κ .↓ at anaPos (pos-outer .↓) ▷ n'' , Γᶠ .↓ [ ⇒mode (φᶠ .↓) ]) ∧
        (n'' , Γᶠ .↓ ⊢ SynSlice_◂_.↓σ pos-focus-slice ⇑ φᶠ .↓)

  pos-data↓ : ((Ctx ∧ Assms) ∧ Exp) ∧ Typ
  pos-data↓ =
    ((pos-κ .↓ , pos-γ .↓) , SynSlice_◂_.↓σ pos-focus-slice) , pos-outer .↓

open SynPosTypeSlice public

instance
  syn-pos-type-slice-precision :
    ∀ {n Γ₀ C n' Γ e τ τₚ}
      {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇒mode τ ]}
      {D : n' , Γ ⊢ e ⇑ τ} {u}
      → HasPrecision (SynPosTypeSlice Cls D u)
  syn-pos-type-slice-precision = record
    { _≈_               = _≈_ on pos-data↓
    ; _⊑_               = _⊑_ on pos-data↓
    ; isDecPartialOrder =
        On.isDecPartialOrder pos-data↓
          (HasPrecision.isDecPartialOrder full-pos-data-precision)
    }

MinSynPosTypeSlice :
  ∀ {n Γ₀ C n' Γ e τ τₚ}
    (Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇒mode τ ])
    (D : n' , Γ ⊢ e ⇑ τ) → ⌊ τ ⌋ → Set
MinSynPosTypeSlice Cls D u = Σ[ s ∈ SynPosTypeSlice Cls D u ] IsMinimal s

-- In analysis mode the full slice is precisely the existing analysis slice:
-- an empty focus analyses against every type, so no focused synthesis
-- assumptions need to be supplied by the surrounding context.
AnaTypeSlice :
  ∀ {n Γ₀ C n' Γ τ τₚ}
    → (Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇐mode τ ])
    → ⌊ τ ⌋ → Set
AnaTypeSlice = AnaSlice

AnaPosTypeSlice :
  ∀ {n Γ₀ C n' Γ τ τₚ}
    → (Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇐mode τ ])
    → ⌊ τ ⌋ → Set
AnaPosTypeSlice = AnaPosSlice

MinAnaTypeSlice :
  ∀ {n Γ₀ C n' Γ τ τₚ}
    → (Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇐mode τ ])
    → ⌊ τ ⌋ → Set
MinAnaTypeSlice = MinAnaSlice

MinAnaPosTypeSlice :
  ∀ {n Γ₀ C n' Γ τ τₚ}
    → (Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇐mode τ ])
    → ⌊ τ ⌋ → Set
MinAnaPosTypeSlice = MinAnaPosSlice
