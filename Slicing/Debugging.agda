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
open import Core.MCtx using (mplug)
open import Core.Typ.WellFormedness using (wf□)
open import Semantics.Statics
open import Semantics.Marking.Judgment
open import Semantics.Marking.CtxMarking
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

-- Paired inconsistency queries.  Querying each complete type is sufficient
-- for soundness: any returned type lies both above and below the original,
-- so recomposition retains the inconsistency.  Query minimality is deferred.
InconsistentQueries : (τ₁ τ₂ : Typ) → Set
InconsistentQueries τ₁ τ₂ = ⌊ τ₁ ⌋ ∧ ⌊ τ₂ ⌋

inconsistent-queries : (τ₁ τ₂ : Typ) → InconsistentQueries τ₁ τ₂
inconsistent-queries τ₁ τ₂ = ⊤ₛ , ⊤ₛ

inconsistency-retained : ∀ {n₁ n₂ Γ₁ Γ₂ e₁ e₂ τ₁ τ₂}
  {D₁ : n₁ , Γ₁ ⊢ e₁ ⇑ τ₁} {D₂ : n₂ , Γ₂ ⊢ e₂ ⇑ τ₂}
  → τ₁ ≁ τ₂
  → (s₁ : MarkedSynSlice D₁ ⊤ₛ)
  → (s₂ : MarkedSynSlice D₂ ⊤ₛ)
  → SynSlice_◂_.↓ϕ (slice s₁) ≁ SynSlice_◂_.↓ϕ (slice s₂)
inconsistency-retained bad s₁ s₂
  with ⊑.antisym {A = Typ}
         (SynSlice_◂_.↓ϕ⊑ (slice s₁)) (SynSlice_◂_.valid (slice s₁))
     | ⊑.antisym {A = Typ}
         (SynSlice_◂_.↓ϕ⊑ (slice s₂)) (SynSlice_◂_.valid (slice s₂))
... | refl | refl = bad

inconsistency-error-sound : ∀ {n₁ n₂ Γ₁ Γ₂ e₁ e₂ τ₁ τ₂}
  {D₁ : n₁ , Γ₁ ⊢ e₁ ⇑ τ₁} {D₂ : n₂ , Γ₂ ⊢ e₂ ⇑ τ₂}
  → τ₁ ≁ τ₂
  → (s₁ : MarkedSynSlice D₁ ⊤ₛ)
  → (s₂ : MarkedSynSlice D₂ ⊤ₛ)
  → n₂ , SynSlice_◂_.↓γ (slice s₂) ⊢ SynSlice_◂_.↓σ (slice s₂)
      ↬ marked-exp s₂ M.⦅≁ SynSlice_◂_.↓ϕ (slice s₁) ⦆
      ⇓ SynSlice_◂_.↓ϕ (slice s₁)
inconsistency-error-sound bad s₁ s₂ =
  mark⇓sub⇑ (marked-syn s₂) (inconsistency-retained bad s₁ s₂)
