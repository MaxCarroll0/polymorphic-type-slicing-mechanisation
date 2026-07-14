-- A cursor decomposition can expose a synthesising focus, an analysing
-- focus, or both.  The last case occurs when the focused analysis
-- derivation is subsumption: it may either remain at the focus or be moved
-- into the surrounding context classification.
module Semantics.Statics.FocusClassification where

open import Data.Nat using (ℕ)
open import Core
open import Semantics.Statics

record SynClassification
    (n : ℕ) (Γ : Assms) (C : Ctx) (e : Exp) (p : Position) : Set where
  constructor syn-class
  field
    nᶠ     : ℕ
    Γᶠ     : Assms
    τᶠ     : Typ
    cls    : n , Γ ⊢ C at p ▷ nᶠ , Γᶠ [ ⇒mode τᶠ ]
    focus  : nᶠ , Γᶠ ⊢ e ⇑ τᶠ

record AnaClassification
    (n : ℕ) (Γ : Assms) (C : Ctx) (e : Exp) (p : Position) : Set where
  constructor ana-class
  field
    nᶠ     : ℕ
    Γᶠ     : Assms
    τᶠ     : Typ
    cls    : n , Γ ⊢ C at p ▷ nᶠ , Γᶠ [ ⇐mode τᶠ ]
    focus  : nᶠ , Γᶠ ⊢ e ⇓ τᶠ

data FocusClassifications
    (n : ℕ) (Γ : Assms) (C : Ctx) (e : Exp) (p : Position) : Set where
  syn-only : SynClassification n Γ C e p
           → FocusClassifications n Γ C e p
  ana-only : AnaClassification n Γ C e p
           → FocusClassifications n Γ C e p
  both     : SynClassification n Γ C e p
           → AnaClassification n Γ C e p
           → FocusClassifications n Γ C e p

private
  map-classifications :
    ∀ {n₁ Γ₁ C₁ p₁ n₂ Γ₂ C₂ p₂ e}
    → (∀ {nᶠ Γᶠ m}
       → n₁ , Γ₁ ⊢ C₁ at p₁ ▷ nᶠ , Γᶠ [ m ]
       → n₂ , Γ₂ ⊢ C₂ at p₂ ▷ nᶠ , Γᶠ [ m ])
    → FocusClassifications n₁ Γ₁ C₁ e p₁
    → FocusClassifications n₂ Γ₂ C₂ e p₂
  map-classifications f (syn-only (syn-class nᶠ Γᶠ τᶠ cls focus)) =
    syn-only (syn-class nᶠ Γᶠ τᶠ (f cls) focus)
  map-classifications f (ana-only (ana-class nᶠ Γᶠ τᶠ cls focus)) =
    ana-only (ana-class nᶠ Γᶠ τᶠ (f cls) focus)
  map-classifications f
    (both (syn-class nᶠ Γᶠ τᶠ cls focus)
          (ana-class nᶠ' Γᶠ' τᶠ' cls' focus')) =
    both (syn-class nᶠ Γᶠ τᶠ (f cls) focus)
         (ana-class nᶠ' Γᶠ' τᶠ' (f cls') focus')

mutual
  classify-syn : ∀ {n Γ e τ} (C : Ctx)
    → n , Γ ⊢ plug C e ⇑ τ
    → FocusClassifications n Γ C e (synPos τ)

  classify-syn ○ d = syn-only (syn-class _ _ _ s○ d)
  classify-syn (λ: τ ⇒ C) (⇑λ: wf d) =
    map-classifications (sλ: wf) (classify-syn C d)
  classify-syn (λ⇒ C) ()
  classify-syn (C ∘₁ e₂) (⇑∘ d₁ eq d₂) =
    map-classifications (λ cls → s∘₁ cls eq d₂) (classify-syn C d₁)
  classify-syn (e₁ ∘₂ C) (⇑∘ d₁ eq d₂) =
    map-classifications (s∘₂ d₁ eq) (classify-ana C d₂)
  classify-syn (C < σ >₁) (⇑<> d eq wf) =
    map-classifications (λ cls → s<>₁ cls eq wf) (classify-syn C d)
  classify-syn (C &₁ e₂) (⇑& d₁ d₂) =
    map-classifications (λ cls → s&₁ cls d₂) (classify-syn C d₁)
  classify-syn (e₁ &₂ C) (⇑& d₁ d₂) =
    map-classifications (s&₂ d₁) (classify-syn C d₂)
  classify-syn (ι₁ C) (⇑ι₁ d) =
    map-classifications sι₁ (classify-syn C d)
  classify-syn (ι₂ C) (⇑ι₂ d) =
    map-classifications sι₂ (classify-syn C d)
  classify-syn (case e₀ of C ·₁ e₂) (⇑case d₀ eq d₁ d₂ con) =
    map-classifications
      (λ cls → scase₁ d₀ eq cls d₂ con) (classify-syn C d₁)
  classify-syn (case e₀ of₂ e₁ · C) (⇑case d₀ eq d₁ d₂ con) =
    map-classifications
      (λ cls → scase₂ d₀ eq d₁ cls con) (classify-syn C d₂)
  classify-syn (π₁ C) (⇑π₁ d eq) =
    map-classifications (λ cls → sπ₁ cls eq) (classify-syn C d)
  classify-syn (π₂ C) (⇑π₂ d eq) =
    map-classifications (λ cls → sπ₂ cls eq) (classify-syn C d)
  classify-syn (Λ C) (⇑Λ d) =
    map-classifications sΛ (classify-syn C d)
  classify-syn (def C ⊢₁ e₂) (⇑def d₁ d₂) =
    map-classifications (λ cls → sdef₁ cls d₂) (classify-syn C d₁)
  classify-syn (def e₁ ⊢₂ C) (⇑def d₁ d₂) =
    map-classifications (sdef₂ d₁) (classify-syn C d₂)

  classify-ana : ∀ {n Γ e τ} (C : Ctx)
    → n , Γ ⊢ plug C e ⇓ τ
    → FocusClassifications n Γ C e (anaPos τ)

  classify-ana ○ d@(⇓Sub syn con) =
    both (syn-class _ _ _ (aSub s○ con) syn)
         (ana-class _ _ _ a○ d)
  classify-ana ○ d = ana-only (ana-class _ _ _ a○ d)
  classify-ana (λ: τ ⇒ C) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con)
      (classify-syn (λ: τ ⇒ C) d)
  classify-ana (λ: τ₁ ⇒ C) (⇓λ: c eq wf d) =
    map-classifications (λ cls → aλ: c eq wf cls) (classify-ana C d)
  classify-ana (λ⇒ C) (⇓Sub () _)
  classify-ana (λ⇒ C) (⇓λ eq d) =
    map-classifications (aλ⇒ eq) (classify-ana C d)
  classify-ana (C ∘₁ e₂) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con)
      (classify-syn (C ∘₁ e₂) d)
  classify-ana (e₁ ∘₂ C) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con)
      (classify-syn (e₁ ∘₂ C) d)
  classify-ana (C < σ >₁) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con)
      (classify-syn (C < σ >₁) d)
  classify-ana (C &₁ e₂) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con)
      (classify-syn (C &₁ e₂) d)
  classify-ana (C &₁ e₂) (⇓& eq d₁ d₂) =
    map-classifications (λ cls → a&₁ eq cls d₂) (classify-ana C d₁)
  classify-ana (e₁ &₂ C) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con)
      (classify-syn (e₁ &₂ C) d)
  classify-ana (e₁ &₂ C) (⇓& eq d₁ d₂) =
    map-classifications (λ cls → a&₂ eq d₁ cls) (classify-ana C d₂)
  classify-ana (ι₁ C) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con) (classify-syn (ι₁ C) d)
  classify-ana (ι₁ C) (⇓ι₁ eq d) =
    map-classifications (aι₁ eq) (classify-ana C d)
  classify-ana (ι₂ C) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con) (classify-syn (ι₂ C) d)
  classify-ana (ι₂ C) (⇓ι₂ eq d) =
    map-classifications (aι₂ eq) (classify-ana C d)
  classify-ana (case e₀ of C ·₁ e₂) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con)
      (classify-syn (case e₀ of C ·₁ e₂) d)
  classify-ana (case e₀ of C ·₁ e₂) (⇓case d₀ eq d₁ d₂) =
    map-classifications
      (λ cls → acase₁ d₀ eq cls d₂) (classify-ana C d₁)
  classify-ana (case e₀ of₂ e₁ · C) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con)
      (classify-syn (case e₀ of₂ e₁ · C) d)
  classify-ana (case e₀ of₂ e₁ · C) (⇓case d₀ eq d₁ d₂) =
    map-classifications
      (λ cls → acase₂ d₀ eq d₁ cls) (classify-ana C d₂)
  classify-ana (π₁ C) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con) (classify-syn (π₁ C) d)
  classify-ana (π₂ C) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con) (classify-syn (π₂ C) d)
  classify-ana (Λ C) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con) (classify-syn (Λ C) d)
  classify-ana (def C ⊢₁ e₂) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con)
      (classify-syn (def C ⊢₁ e₂) d)
  classify-ana (def C ⊢₁ e₂) (⇓def d₁ d₂) =
    map-classifications (λ cls → adef₁ cls d₂) (classify-syn C d₁)
  classify-ana (def e₁ ⊢₂ C) (⇓Sub d con) =
    map-classifications (λ cls → aSub cls con)
      (classify-syn (def e₁ ⊢₂ C) d)
  classify-ana (def e₁ ⊢₂ C) (⇓def d₁ d₂) =
    map-classifications (adef₂ d₁) (classify-ana C d₂)

classify-focus : ∀ {n Γ e τ} (C : Ctx)
  → n , Γ ⊢ plug C e ⇑ τ
  → FocusClassifications n Γ C e (synPos τ)
classify-focus = classify-syn
