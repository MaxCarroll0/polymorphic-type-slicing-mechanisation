open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; subst) renaming (refl to ≡refl; sym to ≡sym)
open import Relation.Nullary using (yes; no; ¬_; Dec)
open import Relation.Nullary.Decidable using (map′; _×-dec_)
open import Data.List using (_∷_)
open import Core
open import Semantics.Statics
open import Semantics.Graduality using (static-gradual-syn)
open import Slicing.Synthesis.FixedAssmsCalc
open import Slicing.Synthesis.FixedAssmsSynthesis
open import Slicing.Synthesis.Synthesis using (SynSlice_◂_; MinSynSlice_◂_; ⊤-syn; minExists)

-- Minimal synthesis slicing under fixed assumptions.  The core `slice` is
-- total on `Sliceable` expressions (those the fixedassms calculus covers:
-- no case, no injection) and returns a calculus derivation.  The exported
-- `min-slice` decides `sliceable?` and yields a MinSynSlice via `soundness`,
-- falling back to `minExists` otherwise.  Dissertation: §8.5-8.6.
module Slicing.Synthesis.FixedAssmsSlicing where

↓□→⊥ₛ : ∀ {τ : Typ} (υ : ⌊ τ ⌋) → υ .↓ ≡ □ → υ ≡ ⊥ₛ {a = τ}
↓□→⊥ₛ (□ isSlice ⊑□) ≡refl = ≡refl

-- Expressions the calculus slices: every synthesising form except case and
-- injection (which have no fixedassms rule).
data Sliceable : Exp → Set where
  sl-□   : Sliceable □
  sl-*   : Sliceable *
  sl-var : ∀ {n} → Sliceable ⟨ n ⟩
  sl-λ:  : ∀ {τ e} → Sliceable e → Sliceable (λ: τ ⇒ e)
  sl-λ⇒  : ∀ {e} → Sliceable e → Sliceable (λ⇒ e)
  sl-∘   : ∀ {e₁ e₂} → Sliceable e₁ → Sliceable e₂ → Sliceable (e₁ ∘ e₂)
  sl-<>  : ∀ {e τ} → Sliceable e → Sliceable (e < τ >)
  sl-&   : ∀ {e₁ e₂} → Sliceable e₁ → Sliceable e₂ → Sliceable (e₁ & e₂)
  sl-π₁  : ∀ {e} → Sliceable e → Sliceable (π₁ e)
  sl-π₂  : ∀ {e} → Sliceable e → Sliceable (π₂ e)
  sl-Λ   : ∀ {e} → Sliceable e → Sliceable (Λ e)
  sl-def : ∀ {e₁ e₂} → Sliceable e₁ → Sliceable e₂ → Sliceable (def e₁ ⊢ e₂)

sliceable? : (e : Exp) → Dec (Sliceable e)
sliceable? □             = yes sl-□
sliceable? *             = yes sl-*
sliceable? ⟨ _ ⟩         = yes sl-var
sliceable? (λ: _ ⇒ e)    = map′ sl-λ: (λ where (sl-λ: p) → p) (sliceable? e)
sliceable? (λ⇒ e)        = map′ sl-λ⇒ (λ where (sl-λ⇒ p) → p) (sliceable? e)
sliceable? (e₁ ∘ e₂)     = map′ (λ (p , q) → sl-∘ p q) (λ where (sl-∘ p q) → p , q)
                                (sliceable? e₁ ×-dec sliceable? e₂)
sliceable? (e < _ >)     = map′ sl-<> (λ where (sl-<> p) → p) (sliceable? e)
sliceable? (e₁ & e₂)     = map′ (λ (p , q) → sl-& p q) (λ where (sl-& p q) → p , q)
                                (sliceable? e₁ ×-dec sliceable? e₂)
sliceable? (π₁ e)        = map′ sl-π₁ (λ where (sl-π₁ p) → p) (sliceable? e)
sliceable? (π₂ e)        = map′ sl-π₂ (λ where (sl-π₂ p) → p) (sliceable? e)
sliceable? (Λ e)         = map′ sl-Λ (λ where (sl-Λ p) → p) (sliceable? e)
sliceable? (def e₁ ⊢ e₂) = map′ (λ (p , q) → sl-def p q) (λ where (sl-def p q) → p , q)
                                (sliceable? e₁ ×-dec sliceable? e₂)
sliceable? (ι₁ _)        = no (λ ())
sliceable? (ι₂ _)        = no (λ ())
sliceable? (case _ of _ · _) = no (λ ())

-- Total slicer on Sliceable expressions.  Bodies are the term-minimal
-- algorithm's non-case clauses; case and injection are excluded by Sliceable.
slice : ∀ {n Γ e τ} → (D : n , Γ ⊢ e ⇑ τ) → (υ : ⌊ τ ⌋) → Sliceable e
      → ∃[ σ ] ∃[ ψ ] ∃[ γ ] D ◂ υ ⤳ σ ⇑ ψ ⊣ γ

slice (⇑ι₁ D) υ ()
slice (⇑ι₂ D) υ ()
slice (⇑case D m D₁ D₂ c) υ ()

slice D (□ isSlice ⊑□) _ = _ , _ , _ , min□
slice ⇑* (.* isSlice ⊑*) _ = _ , _ , _ , min*
slice (⇑Var {τ = τ} p) υ _ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ⇑Var p ◂ υ' ⤳ ⊥ₛ ⇑ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ = _ , _ , _ , minVar p υ≢□

slice (⇑λ: {τ₁ = τ₁} wf D) ((._ ⇒ ._) isSlice ⊑⇒ p₁ p₂) (sl-λ: cf)
  with slice D (↑ p₂) cf
... | _ , _ , ((ϕ₁-↓ ∷ γ-↓) isSlice ⊑∷ ϕ₁-⊑ γ-⊑) , sub
  with extract sub | extract-σ sub
... | s | ≡refl
  = let υ₁ = ↑ p₁
        ϕ₁ = ϕ₁-↓ isSlice ϕ₁-⊑
        ann = ϕ₁ ⊔ₛ υ₁
        sgs = static-gradual-syn
                (⊑∷ (ann .proof) (⊑.refl {Assms}))
                (s .expₛ .proof)
                D
        d-ann = proj₁ (proj₂ sgs)
        ψ₂'-⊑ = proj₂ (proj₂ sgs)
    in _ , _ , _ , minλ: {ψ₂' = ↑ ψ₂'-⊑} sub d-ann
slice (⇑Λ D) (.∀· ._ isSlice ⊑∀ p) (sl-Λ cf)
  with slice D (↑ p) cf
... | _ , _ , _ , sub = _ , _ , _ , minΛ sub
slice (⇑& D₁ D₂) ((._ × ._) isSlice ⊑× p₁ p₂) (sl-& cf₁ cf₂)
  with slice D₁ (↑ p₁) cf₁ | slice D₂ (↑ p₂) cf₂
... | _ , _ , _ , s₁ | _ , _ , _ , s₂ = _ , _ , _ , min& s₁ s₂

slice (⇑∘ D₁ m D₂) υ (sl-∘ cf₁ cf₂) with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ⇑∘ D₁ m D₂ ◂ υ' ⤳ ⊥ₛ ⇑ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D₁ (unmatch⇒ m ⊥ₛ υ) cf₁
...   | _ , _ , _ , sub = _ , _ , _ , min∘ υ≢□ sub

slice (⇑<> D m wf) υ (sl-<> cf) with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ⇑<> D m wf ◂ υ' ⤳ ⊥ₛ ⇑ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D (unmatch∀ m (match-α υ)) cf
...   | _ , _ , _ , sub = _ , _ , _ , min<> υ≢□ sub

slice (⇑π₁ D m) υ (sl-π₁ cf) with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ⇑π₁ D m ◂ υ' ⤳ ⊥ₛ ⇑ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D (unmatch× m υ ⊥ₛ) cf
...   | _ , _ , _ , sub = _ , _ , _ , minπ₁ υ≢□ sub

slice (⇑π₂ D m) υ (sl-π₂ cf) with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ⇑π₂ D m ◂ υ' ⤳ ⊥ₛ ⇑ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D (unmatch× m ⊥ₛ υ) cf
...   | _ , _ , _ , sub = _ , _ , _ , minπ₂ υ≢□ sub

slice (⇑def D₁ D₂) υ (sl-def cf₁ cf₂) with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ⇑def D₁ D₂ ◂ υ' ⤳ ⊥ₛ ⇑ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D₂ υ cf₂
...   | _ , _ , ((υ₁-↓ ∷ γ₂-↓) isSlice ⊑∷ υ₁-⊑ γ₂-⊑) , s-body
  with extract s-body | extract-σ s-body
...   | s₂ | ≡refl
  with slice D₁ (υ₁-↓ isSlice υ₁-⊑) cf₁
...   | _ , _ , _ , s-def
  with extract s-def | extract-ψ s-def
...   | s₁ | ≡refl
  = let sgs = static-gradual-syn
                (⊑∷ (s₁ ↓ϕ⊑) (⊑.refl {Assms}))
                (s₂ .expₛ .proof)
                D₂
        d-def = proj₁ (proj₂ sgs)
        ψ₂'-⊑ = proj₂ (proj₂ sgs)
    in _ , ↑ ψ₂'-⊑ , _ , mindef {ψ₂' = ↑ ψ₂'-⊑} υ≢□ s-body s-def d-def

-- Exported entry point: a minimal synthesis slice for any (D, υ).  Uses the
-- calculus + soundness when the expression is Sliceable, else brute-force
-- minExists.
min-slice : ∀ {n Γ e τ} → (D : n , Γ ⊢ e ⇑ τ) → (υ : ⌊ τ ⌋) → MinSynSlice D ◂ υ
min-slice {e = e} D υ with sliceable? e
... | yes cf = soundness (proj₂ (proj₂ (proj₂ (slice D υ cf))))
... | no  _  = proj₁ (minExists (SynSlice_◂_.reindex (⊤-syn D) (⊤ₛ-max υ)))
