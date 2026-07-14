-- Cardinality of context classifications after lifting a cursor interaction
-- to marked syntax.  The existing recursive classifier decides whether the
-- fixed typing derivation exposes one synthesis classification, one analysis
-- classification, or both (the focused subsumption case); this module proves
-- that marking preserves that cardinality exactly.
module Semantics.Marking.FocusClassification where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Core
open import Core.MCtx using (MCtx)
import Core.MExp as M
open import Core.MExp using (MExp)
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

mutual
  absorb-inconsistency-syn :
    ∀ {n Γ₀ C τ₀ n' Γ τᵃ τˢ}
    → n , Γ₀ ⊢ C at synPos τ₀ ▷ n' , Γ [ ⇐mode τᵃ ]
    → τˢ ≁ τᵃ
    → Σ MCtx λ Č →
        n , Γ₀ ⊢ C ↬ Č at synPos τ₀ ▷ n' , Γ [ ⇒mode τˢ ]
  absorb-inconsistency-syn (sλ: wf cls) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , msλ: wf mcls
  absorb-inconsistency-syn (s∘₁ cls eq d₂) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , ms∘₁ mcls eq (mark-typing-ana d₂)
  absorb-inconsistency-syn (s∘₂ d₁ eq cls) bad
    with absorb-inconsistency-ana cls bad
  ... | Č , mcls = _ , ms∘₂ (mark-typing-syn d₁) eq mcls
  absorb-inconsistency-syn (s<>₁ cls eq wf) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , ms<>₁ mcls eq wf
  absorb-inconsistency-syn (s&₁ cls d₂) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , ms&₁ mcls (mark-typing-syn d₂)
  absorb-inconsistency-syn (s&₂ d₁ cls) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , ms&₂ (mark-typing-syn d₁) mcls
  absorb-inconsistency-syn (sι₁ cls) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , msι₁ mcls
  absorb-inconsistency-syn (sι₂ cls) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , msι₂ mcls
  absorb-inconsistency-syn (scase₀ cls eq d₁ d₂ con) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , mscase₀ mcls eq
      (mark-typing-syn d₁) (mark-typing-syn d₂) con
  absorb-inconsistency-syn (scase₁ d₀ eq cls d₂ con) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , mscase₁ (mark-typing-syn d₀) eq mcls
      (mark-typing-syn d₂) con
  absorb-inconsistency-syn (scase₂ d₀ eq d₁ cls con) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , mscase₂ (mark-typing-syn d₀) eq
      (mark-typing-syn d₁) mcls con
  absorb-inconsistency-syn (sπ₁ cls eq) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , msπ₁ mcls eq
  absorb-inconsistency-syn (sπ₂ cls eq) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , msπ₂ mcls eq
  absorb-inconsistency-syn (sΛ cls) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , msΛ mcls
  absorb-inconsistency-syn (sdef₁ cls d₂) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , msdef₁ mcls (mark-typing-syn d₂)
  absorb-inconsistency-syn (sdef₂ d₁ cls) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , msdef₂ (mark-typing-syn d₁) mcls

  absorb-inconsistency-ana :
    ∀ {n Γ₀ C τ₀ n' Γ τᵃ τˢ}
    → n , Γ₀ ⊢ C at anaPos τ₀ ▷ n' , Γ [ ⇐mode τᵃ ]
    → τˢ ≁ τᵃ
    → Σ MCtx λ Č →
        n , Γ₀ ⊢ C ↬ Č at anaPos τ₀ ▷ n' , Γ [ ⇒mode τˢ ]
  absorb-inconsistency-ana a○ bad =
    _ , maSub⇑ ms○ (λ con → bad (~.sym con))
  absorb-inconsistency-ana (aSub cls con) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , maSub mcls con
  absorb-inconsistency-ana (aλ: con eq wf cls) bad
    with absorb-inconsistency-ana cls bad
  ... | Č , mcls = _ , maλ: con eq wf mcls
  absorb-inconsistency-ana (aλ⇒ eq cls) bad
    with absorb-inconsistency-ana cls bad
  ... | Č , mcls = _ , maλ⇒ eq mcls
  absorb-inconsistency-ana (a&₁ eq cls d₂) bad
    with absorb-inconsistency-ana cls bad
  ... | Č , mcls = _ , ma&₁ eq mcls (mark-typing-ana d₂)
  absorb-inconsistency-ana (a&₂ eq d₁ cls) bad
    with absorb-inconsistency-ana cls bad
  ... | Č , mcls = _ , ma&₂ eq (mark-typing-ana d₁) mcls
  absorb-inconsistency-ana (aι₁ eq cls) bad
    with absorb-inconsistency-ana cls bad
  ... | Č , mcls = _ , maι₁ eq mcls
  absorb-inconsistency-ana (aι₂ eq cls) bad
    with absorb-inconsistency-ana cls bad
  ... | Č , mcls = _ , maι₂ eq mcls
  absorb-inconsistency-ana (acase₀ cls eq d₁ d₂) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , macase₀ mcls eq
      (mark-typing-ana d₁) (mark-typing-ana d₂)
  absorb-inconsistency-ana (acase₁ d₀ eq cls d₂) bad
    with absorb-inconsistency-ana cls bad
  ... | Č , mcls = _ , macase₁ (mark-typing-syn d₀) eq mcls
      (mark-typing-ana d₂)
  absorb-inconsistency-ana (acase₂ d₀ eq d₁ cls) bad
    with absorb-inconsistency-ana cls bad
  ... | Č , mcls = _ , macase₂ (mark-typing-syn d₀) eq
      (mark-typing-ana d₁) mcls
  absorb-inconsistency-ana (adef₁ cls d₂) bad
    with absorb-inconsistency-syn cls bad
  ... | Č , mcls = _ , madef₁ mcls (mark-typing-ana d₂)
  absorb-inconsistency-ana (adef₂ d₁ cls) bad
    with absorb-inconsistency-ana cls bad
  ... | Č , mcls = _ , madef₂ (mark-typing-syn d₁) mcls

record InconsistentFocusClassifications
    {n : ℕ} {Γ₀ : Assms} {C : Ctx} {n' : ℕ} {Γ : Assms}
    {e : Exp} {ě : MExp} {τ₀ τˢ τᵃ : Typ}
    (ACls : n , Γ₀ ⊢ C at synPos τ₀ ▷ n' , Γ [ ⇐mode τᵃ ])
    (D : n' , Γ ⊢ e ↬ ě ⇑ τˢ)
    (bad : τˢ ≁ τᵃ) : Set where
  field
    synthesis-context : MCtx
    synthesis-classification :
      n , Γ₀ ⊢ C ↬ synthesis-context at synPos τ₀
        ▷ n' , Γ [ ⇒mode τˢ ]
    synthesis-focus : n' , Γ ⊢ e ↬ ě ⇑ τˢ
    analysis-classification :
      n , Γ₀ ⊢ C ↬ embedCtx C at synPos τ₀
        ▷ n' , Γ [ ⇐mode τᵃ ]
    analysis-focus : n' , Γ ⊢ e ↬ ě M.⦅≁ τᵃ ⦆ ⇓ τᵃ

inconsistent-focus-classifications :
  ∀ {n Γ₀ C n' Γ e ě τ₀ τˢ τᵃ}
    (ACls : n , Γ₀ ⊢ C at synPos τ₀ ▷ n' , Γ [ ⇐mode τᵃ ])
    (D : n' , Γ ⊢ e ↬ ě ⇑ τˢ)
    (bad : τˢ ≁ τᵃ)
  → InconsistentFocusClassifications ACls D bad
inconsistent-focus-classifications ACls D bad
  with absorb-inconsistency-syn ACls bad
... | Č , SCls = record
  { synthesis-context = Č
  ; synthesis-classification = SCls
  ; synthesis-focus = D
  ; analysis-classification = mark-syn-cls ACls
  ; analysis-focus = mark⇓sub⇑ D (λ con → bad (~.sym con))
  }
