-- Cardinality of context classifications after lifting a cursor interaction
-- to marked syntax.  The existing recursive classifier decides whether the
-- fixed typing derivation exposes one synthesis classification, one analysis
-- classification, or both (the focused subsumption case); this module proves
-- that marking preserves that cardinality exactly.
module Semantics.Marking.FocusClassification where

open import Data.Nat using (ℕ)
open import Core
open import Semantics.Statics
import Semantics.Statics.FocusClassification as U
open import Semantics.Marking.Judgment
open import Semantics.Marking.CtxMarking
open import Semantics.Marking.Embedding

record MarkedSynClassification
    (n : ℕ) (Γ : Assms) (C : Ctx) (e : Exp) (p : Position) : Set where
  constructor marked-syn-class
  field
    nᶠ       : ℕ
    Γᶠ       : Assms
    τᶠ       : Typ
    cls      : n , Γ ⊢ C ↬ embedCtx C at p ▷ nᶠ , Γᶠ [ ⇒mode τᶠ ]
    focus    : nᶠ , Γᶠ ⊢ e ↬ embed e ⇑ τᶠ

record MarkedAnaClassification
    (n : ℕ) (Γ : Assms) (C : Ctx) (e : Exp) (p : Position) : Set where
  constructor marked-ana-class
  field
    nᶠ       : ℕ
    Γᶠ       : Assms
    τᶠ       : Typ
    cls      : n , Γ ⊢ C ↬ embedCtx C at p ▷ nᶠ , Γᶠ [ ⇐mode τᶠ ]
    focus    : nᶠ , Γᶠ ⊢ e ↬ embed e ⇓ τᶠ

data MarkedFocusClassifications
    (n : ℕ) (Γ : Assms) (C : Ctx) (e : Exp) (p : Position) : Set where
  syn-only : MarkedSynClassification n Γ C e p
           → MarkedFocusClassifications n Γ C e p
  ana-only : MarkedAnaClassification n Γ C e p
           → MarkedFocusClassifications n Γ C e p
  both     : MarkedSynClassification n Γ C e p
           → MarkedAnaClassification n Γ C e p
           → MarkedFocusClassifications n Γ C e p

mark-syn-classification : ∀ {n Γ C e p}
  → U.SynClassification n Γ C e p
  → MarkedSynClassification n Γ C e p
mark-syn-classification {p = synPos _} (U.syn-class nᶠ Γᶠ τᶠ cls focus) =
  marked-syn-class nᶠ Γᶠ τᶠ (mark-syn-cls cls) (mark-typing-syn focus)
mark-syn-classification {p = anaPos _} (U.syn-class nᶠ Γᶠ τᶠ cls focus) =
  marked-syn-class nᶠ Γᶠ τᶠ (mark-ana-cls cls) (mark-typing-syn focus)

mark-ana-classification : ∀ {n Γ C e p}
  → U.AnaClassification n Γ C e p
  → MarkedAnaClassification n Γ C e p
mark-ana-classification {p = synPos _} (U.ana-class nᶠ Γᶠ τᶠ cls focus) =
  marked-ana-class nᶠ Γᶠ τᶠ (mark-syn-cls cls) (mark-typing-ana focus)
mark-ana-classification {p = anaPos _} (U.ana-class nᶠ Γᶠ τᶠ cls focus) =
  marked-ana-class nᶠ Γᶠ τᶠ (mark-ana-cls cls) (mark-typing-ana focus)

-- The three constructors are the cardinality bound: there is one synthesis
-- result, one analysis result, or exactly the pair exposed by subsumption.
mark-classifications : ∀ {n Γ C e p}
  → U.FocusClassifications n Γ C e p
  → MarkedFocusClassifications n Γ C e p
mark-classifications (U.syn-only s) = syn-only (mark-syn-classification s)
mark-classifications (U.ana-only a) = ana-only (mark-ana-classification a)
mark-classifications (U.both s a) =
  both (mark-syn-classification s) (mark-ana-classification a)

classify-marked-syn : ∀ {n Γ e τ} (C : Ctx)
  → n , Γ ⊢ plug C e ⇑ τ
  → MarkedFocusClassifications n Γ C e (synPos τ)
classify-marked-syn C d = mark-classifications (U.classify-syn C d)

classify-marked-ana : ∀ {n Γ e τ} (C : Ctx)
  → n , Γ ⊢ plug C e ⇓ τ
  → MarkedFocusClassifications n Γ C e (anaPos τ)
classify-marked-ana C d = mark-classifications (U.classify-ana C d)

classify-marked-focus : ∀ {n Γ e τ} (C : Ctx)
  → n , Γ ⊢ plug C e ⇑ τ
  → MarkedFocusClassifications n Γ C e (synPos τ)
classify-marked-focus = classify-marked-syn
