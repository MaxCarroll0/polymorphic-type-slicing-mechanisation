-- Soundness of the type-error debugging queries.  This module deliberately
-- proves preservation of the selected error mark, not minimality of the
-- query; query minimality is a separate theorem.
module Slicing.Debugging where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Core
import Core.MExp as M
open import Core.MExp using (MExp)
open import Core.MCtx using (MCtx; mplug)
open import Core.Typ.WellFormedness using (wf□)
open import Semantics.Statics
open import Semantics.Marking.Judgment
open import Semantics.Marking.CtxMarking
import Semantics.Marking.FocusClassification as MF
open import Slicing.Synthesis.Synthesis
open import Slicing.Analysis.Analysis
open import Slicing.Marked

-- Keep exactly the outer constructor and replace every proper component by
-- a type hole.  This is the debugging query for all shape errors.
outer-query : (τ : Typ) → ⌊ τ ⌋
outer-query □ = ⊥ₛ
outer-query * = * isSlice ⊑*
outer-query ⟨ k ⟩ = ⟨ k ⟩ isSlice ⊑Var
outer-query (τ₁ + τ₂) = (□ + □) isSlice (⊑+ ⊑□ ⊑□)
outer-query (τ₁ × τ₂) = (□ × □) isSlice (⊑× ⊑□ ⊑□)
outer-query (τ₁ ⇒ τ₂) = (□ ⇒ □) isSlice (⊑⇒ ⊑□ ⊑□)
outer-query (∀· τ) = (∀· □) isSlice (⊑∀ ⊑□)

NonArrow NonSum NonProduct : Typ → Set
NonArrow τ = ∀ {τ₁ τ₂} → τ ⊔ □ ⇒ □ ≢ τ₁ ⇒ τ₂
NonSum τ = ∀ {τ₁ τ₂} → τ ⊔ □ + □ ≢ τ₁ + τ₂
NonProduct τ = ∀ {τ₁ τ₂} → τ ⊔ □ × □ ≢ τ₁ × τ₂

NonForall : Typ → Set
NonForall τ = ∀ {τ'} → τ ⊔ ∀· □ ≢ ∀· τ'

-- Any answer above outer-query has the same head constructor.  Hence a
-- mismatch at the original type remains a mismatch at the sliced type.
retain-non-arrow : ∀ {τ φ} → NonArrow τ → outer-query τ .↓ ⊑t φ → NonArrow φ
retain-non-arrow {τ = □} bad p = ⊥-elim (bad refl)
retain-non-arrow {τ = _ ⇒ _} bad p = ⊥-elim (bad refl)
retain-non-arrow {τ = *} bad ⊑* = λ ()
retain-non-arrow {τ = ⟨ _ ⟩} bad ⊑Var = λ ()
retain-non-arrow {τ = _ + _} bad (⊑+ _ _) = λ ()
retain-non-arrow {τ = _ × _} bad (⊑× _ _) = λ ()
retain-non-arrow {τ = ∀· _} bad (⊑∀ _) = λ ()

retain-non-sum : ∀ {τ φ} → NonSum τ → outer-query τ .↓ ⊑t φ → NonSum φ
retain-non-sum {τ = □} bad p = ⊥-elim (bad refl)
retain-non-sum {τ = _ + _} bad p = ⊥-elim (bad refl)
retain-non-sum {τ = *} bad ⊑* = λ ()
retain-non-sum {τ = ⟨ _ ⟩} bad ⊑Var = λ ()
retain-non-sum {τ = _ × _} bad (⊑× _ _) = λ ()
retain-non-sum {τ = _ ⇒ _} bad (⊑⇒ _ _) = λ ()
retain-non-sum {τ = ∀· _} bad (⊑∀ _) = λ ()

retain-non-product : ∀ {τ φ} → NonProduct τ → outer-query τ .↓ ⊑t φ → NonProduct φ
retain-non-product {τ = □} bad p = ⊥-elim (bad refl)
retain-non-product {τ = _ × _} bad p = ⊥-elim (bad refl)
retain-non-product {τ = *} bad ⊑* = λ ()
retain-non-product {τ = ⟨ _ ⟩} bad ⊑Var = λ ()
retain-non-product {τ = _ + _} bad (⊑+ _ _) = λ ()
retain-non-product {τ = _ ⇒ _} bad (⊑⇒ _ _) = λ ()
retain-non-product {τ = ∀· _} bad (⊑∀ _) = λ ()

retain-non-forall : ∀ {τ φ} → NonForall τ → outer-query τ .↓ ⊑t φ → NonForall φ
retain-non-forall {τ = □} bad p = ⊥-elim (bad refl)
retain-non-forall {τ = ∀· _} bad p = ⊥-elim (bad refl)
retain-non-forall {τ = *} bad ⊑* = λ ()
retain-non-forall {τ = ⟨ _ ⟩} bad ⊑Var = λ ()
retain-non-forall {τ = _ + _} bad (⊑+ _ _) = λ ()
retain-non-forall {τ = _ × _} bad (⊑× _ _) = λ ()
retain-non-forall {τ = _ ⇒ _} bad (⊑⇒ _ _) = λ ()

-- Synthesis-side shape errors: put the marked focus slice in the purely
-- structural immediate context.  The same error constructor is derivable.
arrow-syn-sound : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ}
  → NonArrow τ → (s : MarkedSynSlice D (outer-query τ))
  → n , SynSlice_◂_.↓γ (slice s) ⊢ SynSlice_◂_.↓σ (slice s) ∘ □
      ↬ (marked-exp s M.⦅▸⇒⦆) M.∘ M.□ ⇑ □
arrow-syn-sound {τ = τ} bad s =
  mark⇑∘⇑ (marked-syn s)
    (retain-non-arrow {τ = τ} bad (SynSlice_◂_.valid (slice s)))
    (mark⇓sub mark⇑□ ~?₁)

sum-syn-sound : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ}
  → NonSum τ → (s : MarkedSynSlice D (outer-query τ))
  → n , SynSlice_◂_.↓γ (slice s) ⊢
      case SynSlice_◂_.↓σ (slice s) of □ · □
      ↬ M.case (marked-exp s M.⦅▸+⦆) of M.□ · M.□ ⇑ □
sum-syn-sound {τ = τ} bad s =
  mark⇑case⇑ (marked-syn s)
    (retain-non-sum {τ = τ} bad (SynSlice_◂_.valid (slice s)))
    mark⇑□ mark⇑□

product-syn-sound : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ}
  → NonProduct τ → (s : MarkedSynSlice D (outer-query τ))
  → n , SynSlice_◂_.↓γ (slice s) ⊢ π₁ (SynSlice_◂_.↓σ (slice s))
      ↬ M.π₁ (marked-exp s M.⦅▸×⦆) ⇑ □
product-syn-sound {τ = τ} bad s =
  mark⇑π₁⇑ (marked-syn s)
    (retain-non-product {τ = τ} bad (SynSlice_◂_.valid (slice s)))

forall-syn-sound : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ}
  → NonForall τ → (s : MarkedSynSlice D (outer-query τ))
  → n , SynSlice_◂_.↓γ (slice s) ⊢ SynSlice_◂_.↓σ (slice s) < □ >
      ↬ (marked-exp s M.⦅▸∀⦆) M.< □ > ⇑ □
forall-syn-sound {τ = τ} bad s =
  mark⇑<>⇑ (marked-syn s)
    (retain-non-forall {τ = τ} bad (SynSlice_◂_.valid (slice s))) wf□

-- Analysis-side arrow-shape error: install the outer-constructor query as
-- the focus demand of the sliced context, mark an unannotated lambda there,
-- and compose.  The resulting whole marked term still contains ⦅~⇒⦆.
arrow-ana-sound : ∀ {n Γ₀ C n' Γ τ τₚ}
  {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇐mode τ ]}
  → NonArrow τ → (s : MarkedAnaSlice Cls (outer-query τ))
  → ∃[ n'' ] ∃[ Γ' ]
      n , AnaSlice.γ (ana-slice s) .↓ ⊢
        plug (AnaSlice.κ (ana-slice s) .↓) (λ⇒ □)
        ↬ mplug (marked-context s) ((M.λ⇒ M.□) M.⦅~⇒⦆)
        ⇑ AnaSlice.type (ana-slice s) .↓
arrow-ana-sound {τ = τ} bad s with marked-valid s
... | n'' , Γ' , cls =
  n'' , Γ' , mplug-compose-syn cls
    (mark⇓λ⇑
      (retain-non-arrow {τ = τ} bad (AnaSlice.focus⊒ (ana-slice s)))
      (mark⇓sub mark⇑□ ~?₁))

record InconsistentQueries (τˢ τᵃ : Typ) : Set where
  field
    syn-query : ⌊ τˢ ⌋
    ana-query : ⌊ τᵃ ⌋
    queries-inconsistent : syn-query .↓ ≁ ana-query .↓
open InconsistentQueries public

inconsistent-queries : ∀ {τˢ τᵃ} → τˢ ≁ τᵃ → InconsistentQueries τˢ τᵃ
inconsistent-queries bad = record
  { syn-query = ⊤ₛ
  ; ana-query = ⊤ₛ
  ; queries-inconsistent = bad
  }

inconsistency-retained : ∀ {τˢ τᵃ φˢ φᵃ}
  → τˢ ≁ τᵃ
  → τˢ ⊑t φˢ
  → τᵃ ⊑t φᵃ
  → φˢ ≁ φᵃ
inconsistency-retained bad syn⊑ ana⊑ con =
  bad (~-⊑-down con syn⊑ ana⊑)

inconsistency-at-focus-sound : ∀ {n Γ₀ C Č n' Γ e ě τ₀ τˢ τᵃ}
  → n , Γ₀ ⊢ C ↬ Č at synPos τ₀ ▷ n' , Γ [ ⇐mode τᵃ ]
  → n' , Γ ⊢ e ↬ ě ⇑ τˢ
  → τˢ ≁ τᵃ
  → n , Γ₀ ⊢ plug C e ↬ mplug Č (ě M.⦅≁ τᵃ ⦆) ⇑ τ₀
inconsistency-at-focus-sound cls focus bad =
  mplug-compose-syn cls (mark⇓sub⇑ focus (λ con → bad (~.sym con)))

record JoinedInconsistencySlices
    {n : ℕ} {Γ₀ : Assms} {C : Ctx} {Čˢ Čᵃ : MCtx}
    {n' : ℕ} {Γ : Assms} {e : Exp} {ě : MExp} {τ₀ τˢ τᵃ : Typ}
    (SCls : n , Γ₀ ⊢ C ↬ Čˢ at synPos τ₀ ▷ n' , Γ [ ⇒mode τˢ ])
    (D : n' , Γ ⊢ e ↬ ě ⇑ τˢ)
    (ACls : n , Γ₀ ⊢ C ↬ Čᵃ at synPos τ₀ ▷ n' , Γ [ ⇐mode τᵃ ])
    (q : InconsistentQueries τˢ τᵃ)
    (sˢ : MarkedFullSynSlice SCls D (syn-query q))
    (sᵃ : MarkedFullAnaSlice ACls (ana-query q)) : Set where
  field
    focus-n : ℕ
    focus-Γ : Assms
    sliced-syn-type : Typ
    sliced-ana-type : Typ
    joined-context : MCtx
    joined-focus : MExp
    joined-classification :
      n , (marked-full-γ sˢ ⊔ₛ marked-ana-γ sᵃ) .↓ ⊢
        (marked-full-κ sˢ ⊔ₛ marked-ana-κ sᵃ) .↓
        ↬ joined-context
        at synPos ((marked-full-outer sˢ ⊔ₛ marked-ana-outer sᵃ) .↓)
        ▷ focus-n , focus-Γ [ ⇐mode sliced-ana-type ]
    joined-focus-synthesis :
      focus-n , focus-Γ ⊢
        marked-full-exp sˢ .↓
        ↬ joined-focus ⇑ sliced-syn-type
    syn-query-retained : syn-query q .↓ ⊑t sliced-syn-type
    ana-query-retained : ana-query q .↓ ⊑t sliced-ana-type
open JoinedInconsistencySlices public

reindex-marked-ana-classification :
  ∀ {n n' Γ₀ Γ₀' C C' Č Γ τ₀ τ₀' τ}
  → Γ₀' ≡ Γ₀
  → C' ≡ C
  → τ₀' ≡ τ₀
  → n , Γ₀ ⊢ C ↬ Č at synPos τ₀ ▷ n' , Γ [ ⇐mode τ ]
  → n , Γ₀' ⊢ C' ↬ Č at synPos τ₀' ▷ n' , Γ [ ⇐mode τ ]
reindex-marked-ana-classification refl refl refl cls = cls

top-joined-inconsistency-slices :
  ∀ {n Γ₀ C Čˢ Čᵃ n' Γ e ě τ₀ τˢ τᵃ}
    {SCls : n , Γ₀ ⊢ C ↬ Čˢ at synPos τ₀ ▷ n' , Γ [ ⇒mode τˢ ]}
    {D : n' , Γ ⊢ e ↬ ě ⇑ τˢ}
    {ACls : n , Γ₀ ⊢ C ↬ Čᵃ at synPos τ₀ ▷ n' , Γ [ ⇐mode τᵃ ]}
    (q : InconsistentQueries τˢ τᵃ)
  → JoinedInconsistencySlices SCls D ACls q
      (top-marked-full-syn (syn-query q))
      (top-marked-full-ana (ana-query q))
top-joined-inconsistency-slices
    {n} {Γ₀} {C} {_} {_} {_} {_} {_} {_} {τ₀}
    {SCls = SCls} {D = D} {ACls = ACls} q
  = record
  { focus-n = _
  ; focus-Γ = _
  ; sliced-syn-type = _
  ; sliced-ana-type = _
  ; joined-context = _
  ; joined-focus = _
  ; joined-classification = reindex-marked-ana-classification
      (⊑ₛLat.⊔-idempotent
        {A = Assms} {a = Γ₀} (⊤ₛ {A = Assms} {a = Γ₀}))
      (⊑ₛLat.⊔-idempotent
        {A = Ctx} {a = C} (⊤ₛ {A = Ctx} {a = C}))
      (⊑ₛLat.⊔-idempotent
        {A = Typ} {a = τ₀} (⊤ₛ {A = Typ} {a = τ₀}))
      ACls
  ; joined-focus-synthesis = D
  ; syn-query-retained = syn-query q .proof
  ; ana-query-retained = ana-query q .proof
  }

inconsistency-error-sound :
  ∀ {n Γ₀ C Čˢ Čᵃ n' Γ e ě τ₀ τˢ τᵃ}
    {SCls : n , Γ₀ ⊢ C ↬ Čˢ at synPos τ₀ ▷ n' , Γ [ ⇒mode τˢ ]}
    {D : n' , Γ ⊢ e ↬ ě ⇑ τˢ}
    {ACls : n , Γ₀ ⊢ C ↬ Čᵃ at synPos τ₀ ▷ n' , Γ [ ⇐mode τᵃ ]}
    {q : InconsistentQueries τˢ τᵃ}
    {sˢ : MarkedFullSynSlice SCls D (syn-query q)}
    {sᵃ : MarkedFullAnaSlice ACls (ana-query q)}
  → (j : JoinedInconsistencySlices SCls D ACls q sˢ sᵃ)
  → n , (marked-full-γ sˢ ⊔ₛ marked-ana-γ sᵃ) .↓ ⊢
      plug ((marked-full-κ sˢ ⊔ₛ marked-ana-κ sᵃ) .↓)
           (marked-full-exp sˢ .↓)
      ↬ mplug (joined-context j)
          (joined-focus j M.⦅≁ sliced-ana-type j ⦆)
      ⇑ (marked-full-outer sˢ ⊔ₛ marked-ana-outer sᵃ) .↓
inconsistency-error-sound {q = q} j =
  inconsistency-at-focus-sound
    (joined-classification j)
    (joined-focus-synthesis j)
    (inconsistency-retained
      (queries-inconsistent q)
      (syn-query-retained j)
      (ana-query-retained j))

record InconsistencySlicingResult
    {n : ℕ} {Γ₀ : Assms} {C : Ctx} {n' : ℕ} {Γ : Assms}
    {e : Exp} {ě : MExp} {τ₀ τˢ τᵃ : Typ}
    (ACls : n , Γ₀ ⊢ C at synPos τ₀ ▷ n' , Γ [ ⇐mode τᵃ ])
    (D : n' , Γ ⊢ e ↬ ě ⇑ τˢ)
    (bad : τˢ ≁ τᵃ) : Set where
  field
    focus-classifications : MF.InconsistentFocusClassifications ACls D bad
    joined-slices :
      let fc = focus-classifications
          q = inconsistent-queries bad
          SCls = MF.InconsistentFocusClassifications.synthesis-classification fc
          SD = MF.InconsistentFocusClassifications.synthesis-focus fc
          ACls' = MF.InconsistentFocusClassifications.analysis-classification fc
          sˢ = top-marked-full-syn {Cls = SCls} {D = SD} (syn-query q)
          sᵃ = top-marked-full-ana {Cls = ACls'} (ana-query q)
      in JoinedInconsistencySlices SCls SD ACls' q sˢ sᵃ
open InconsistencySlicingResult public

slice-inconsistency-error :
  ∀ {n Γ₀ C n' Γ e ě τ₀ τˢ τᵃ}
    (ACls : n , Γ₀ ⊢ C at synPos τ₀ ▷ n' , Γ [ ⇐mode τᵃ ])
    (D : n' , Γ ⊢ e ↬ ě ⇑ τˢ)
    (bad : τˢ ≁ τᵃ)
  → InconsistencySlicingResult ACls D bad
slice-inconsistency-error ACls D bad
  with MF.inconsistent-focus-classifications ACls D bad
... | fc = record
  { focus-classifications = fc
  ; joined-slices = top-joined-inconsistency-slices (inconsistent-queries bad)
  }

sliced-inconsistency-error-sound :
  ∀ {n Γ₀ C n' Γ e ě τ₀ τˢ τᵃ}
    {ACls : n , Γ₀ ⊢ C at synPos τ₀ ▷ n' , Γ [ ⇐mode τᵃ ]}
    {D : n' , Γ ⊢ e ↬ ě ⇑ τˢ}
    {bad : τˢ ≁ τᵃ}
    (r : InconsistencySlicingResult ACls D bad)
  → let fc = focus-classifications r
        q = inconsistent-queries bad
        SCls = MF.InconsistentFocusClassifications.synthesis-classification fc
        SD = MF.InconsistentFocusClassifications.synthesis-focus fc
        ACls' = MF.InconsistentFocusClassifications.analysis-classification fc
        sˢ = top-marked-full-syn {Cls = SCls} {D = SD} (syn-query q)
        sᵃ = top-marked-full-ana {Cls = ACls'} (ana-query q)
        j = joined-slices r
    in n , (marked-full-γ sˢ ⊔ₛ marked-ana-γ sᵃ) .↓ ⊢
          plug ((marked-full-κ sˢ ⊔ₛ marked-ana-κ sᵃ) .↓)
               (marked-full-exp sˢ .↓)
          ↬ mplug (joined-context j)
              (joined-focus j M.⦅≁ sliced-ana-type j ⦆)
          ⇑ (marked-full-outer sˢ ⊔ₛ marked-ana-outer sᵃ) .↓
sliced-inconsistency-error-sound r =
  inconsistency-error-sound (joined-slices r)
