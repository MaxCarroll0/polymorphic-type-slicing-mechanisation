{-# OPTIONS --allow-unsolved-metas --allow-incomplete-matches #-}

module Semantics.Marking.CtxMarking where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.Maybe using (just; nothing)
open import Data.List using (_∷_)
open import Data.Product using (Σ; _,_; ∃; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂)
open import Relation.Nullary using (¬_)
open import Core
open import Core.MExp
open import Core.MCtx
open import Semantics.Statics.CtxTyping using (CtxMode; ⇒mode; ⇐mode; Position; synPos; anaPos)
open import Semantics.Marking.Judgment

-- Focus typing for marked context classification: at the focus position,
-- we have a marking judgment on the focus expression/MExp pair.
MFocusTyping : ℕ → Assms → Exp → MExp → CtxMode → Set
MFocusTyping n Γ' e ě (⇒mode τ')  = n , Γ' ⊢ e ↬ ě ⇑ τ'
MFocusTyping n Γ' e ě (⇐mode τ')  = n , Γ' ⊢ e ↬ ě ⇓ τ'

-- Marked context classification.
--
-- n , Γ ⊢ C ↬ Č at p ▷ n' , Γ' [ m ] reads:
--   Under type depth n and outer assumptions Γ, the unmarked context C
--   marks to the marked context Č; in position p the focus mode is m
--   under depth n' and assumptions Γ'.
--
-- The judgement mirrors the unmarked Ctx classification one-to-one for
-- "successful" cases, and adds new rules for each kind of error mark.
-- Each error rule records the precondition under which the marking
-- algorithm would synthesize/insert that mark.
data _,_⊢_↬_at_▷_,_[_] : ℕ → Assms → Ctx → MCtx → Position → ℕ → Assms → CtxMode → Set where

  -- ============================================================
  -- HOLES
  -- ============================================================

  ms○      : ∀ {n Γ τ}                                                                                    →
             n , Γ ⊢ ○ ↬ ○ at synPos τ ▷ n , Γ [ ⇒mode τ ]

  ma○      : ∀ {n Γ τ}                                                                                    →
             n , Γ ⊢ ○ ↬ ○ at anaPos τ ▷ n , Γ [ ⇐mode τ ]

  -- ============================================================
  -- SUBSUMPTION
  -- ============================================================

  -- Successful subsumption (mirrors aSub; uses Marking/Judgment.agda's
  -- mark⇓sub at the leaf).
  maSub    : ∀ {n Γ n' Γ' C Č τ τ' m}
             → n , Γ ⊢ C ↬ Č at synPos τ' ▷ n' , Γ' [ m ]
             → τ ~ τ'                                                                                      →
             n , Γ ⊢ C ↬ Č at anaPos τ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- DEBUG VIA TYPE SLICING — mark ⦅≁ τ ⦆ (type inconsistency)
  --
  -- This mark fires when the surrounding context analyses against τ but the
  -- focus's synthesis type τ' is INCONSISTENT with τ. To debug:
  --   * Slice the syn type τ' down to a minimal slice τ'-min that suffices to
  --     witness τ ≁ τ' (BoundedMinSynSlice on the focus, queried at the
  --     "incompatibility" between τ and τ').
  --   * Slice the analysis-context: AnaSlice on the surrounding C at the
  --     same incompatibility, giving a minimal κ-slice of C and the
  --     minimal outer-type slice ψ ⊑ τ that PRESERVES the inconsistency.
  --   * Together (κ, focus.σ-slice, type-slices) point at exactly the parts
  --     of the program responsible for the type clash, isolating the user's
  --     mistake from unrelated code.
  -- ============================================================
  maSub⇑   : ∀ {n Γ n' Γ' C Č τ τ' m}
             → n , Γ ⊢ C ↬ Č at synPos τ' ▷ n' , Γ' [ m ]
             → ¬ (τ ~ τ')                                                                                  →
             n , Γ ⊢ C ↬ Č ⦅≁ τ ⦆ at anaPos τ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- ANNOTATED LAMBDA — synthesis (no mark involved)
  -- ============================================================

  msλ:     : ∀ {n Γ n' Γ' τ₁ τ₂ C Č m} → n ⊢wf τ₁
             → n , (τ₁ ∷ Γ) ⊢ C ↬ Č at synPos τ₂ ▷ n' , Γ' [ m ]                                         →
             n , Γ ⊢ λ: τ₁ ⇒ C ↬ λ: τ₁ ⇒ Č at synPos (τ₁ ⇒ τ₂) ▷ n' , Γ' [ m ]

  -- Annotated lambda — analysis (no mark). Mirrors mark⇓λ:.
  maλ:     : ∀ {n Γ n' Γ' C Č τ τ₁ τ₂ m}
             → τ ~ τ₁ ⇒ □
             → τ ⊔ τ₁ ⇒ □ ≡ τ₁ ⇒ τ₂
             → n ⊢wf τ₁
             → n , (τ₁ ∷ Γ) ⊢ C ↬ Č at anaPos τ₂ ▷ n' , Γ' [ m ]                                         →
             n , Γ ⊢ λ: τ₁ ⇒ C ↬ λ: τ₁ ⇒ Č at anaPos τ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- UNANNOTATED LAMBDA — analysis (no mark)
  -- ============================================================

  maλ⇒     : ∀ {n Γ n' Γ' C Č τ τ₁ τ₂ m}
             → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂
             → n , (τ₁ ∷ Γ) ⊢ C ↬ Č at anaPos τ₂ ▷ n' , Γ' [ m ]                                         →
             n , Γ ⊢ λ⇒ C ↬ λ⇒ Č at anaPos τ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- DEBUG VIA TYPE SLICING — mark ⦅~⇒⦆ on unannotated lambda (analysis)
  --
  -- Fires when an unannotated lambda is analysed against a non-arrow τ.
  -- The mark wraps the lambda and the body is analysed against □.
  -- To debug:
  --   * Slice τ down to a minimal slice that witnesses ¬(τ ⊔ □⇒□ ≡ ...) —
  --     i.e. a slice τ-min ⊑ τ that still has a non-arrow head.
  --   * The surrounding AnaSlice on the surrounding context isolates which
  --     enclosing operation imposed this τ-shape (e.g. an annotation, a
  --     def-body type, etc.).
  -- ============================================================
  -- Note: mirrors mark⇓λ⇑ — body at Γ (no binder), since matching failed
  -- and there's no domain type to bind.
  maλ⇒⇑    : ∀ {n Γ n' Γ' C Č τ m}
             → (∀ {τ₁ τ₂} → τ ⊔ □ ⇒ □ ≢ τ₁ ⇒ τ₂)
             → n , Γ ⊢ C ↬ Č at anaPos □ ▷ n' , Γ' [ m ]                                                 →
             n , Γ ⊢ λ⇒ C ↬ (λ⇒ Č) ⦅~⇒⦆ at anaPos τ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- DEBUG VIA TYPE SLICING — mark ⦅~⇒⦆ on lambda in synthesis position
  --
  -- A bare λ⇒ has no synthesis type, so in synthesis position it gets a
  -- ⦅~⇒⦆ mark and synthesises □. To debug:
  --   * (Future) lift type slicing to MExp; the mark is *not* a type-mismatch
  --     per se but a syntactic limitation. Slicing the surrounding synPos
  --     context can show what consumer expected a synthesis type and could
  --     suggest where the user might add a type annotation.
  -- ============================================================
  -- Note: mirrors mark⇑λ⇒ — body at Γ (no binder).
  msλ⇒⇑    : ∀ {n Γ n' Γ' C Č m}
             → n , Γ ⊢ C ↬ Č at anaPos □ ▷ n' , Γ' [ m ]                                                 →
             n , Γ ⊢ λ⇒ C ↬ (λ⇒ Č) ⦅~⇒⦆ at synPos □ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- APPLICATION (focus on function) — synthesis, no mark
  -- ============================================================

  ms∘₁     : ∀ {n Γ n' Γ' C Č e ě τ τ₁ τ₂ m}
             → n , Γ ⊢ C ↬ Č at synPos τ ▷ n' , Γ' [ m ]
             → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂
             → n , Γ ⊢ e ↬ ě ⇓ τ₁                                                                          →
             n , Γ ⊢ C ∘₁ e ↬ Č ∘₁ ě at synPos τ₂ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- DEBUG VIA TYPE SLICING — mark ⦅▸⇒⦆ on focus-on-function (synthesis)
  --
  -- Fires when the focus synthesises a non-arrow type τ. To debug:
  --   * Slice the focus's syn type τ to a minimal τ-min that still fails
  --     (τ-min ⊔ □⇒□ ≡ ⇒-shape).
  --   * The MinSynSlice on the function-focus tells the user the smallest
  --     subterm responsible for the bad type — they can fix it without
  --     reading any of the rest of the program.
  -- ============================================================
  ms∘₁⇑    : ∀ {n Γ n' Γ' C Č e ě τ m}
             → n , Γ ⊢ C ↬ Č at synPos τ ▷ n' , Γ' [ m ]
             → (∀ {τ₁ τ₂} → τ ⊔ □ ⇒ □ ≢ τ₁ ⇒ τ₂)
             → n , Γ ⊢ e ↬ ě ⇓ □                                                                           →
             n , Γ ⊢ C ∘₁ e ↬ (Č ⦅▸⇒⦆) ∘₁ ě at synPos □ ▷ n' , Γ' [ m ]

  -- Application (focus on argument) — synthesis, no mark
  ms∘₂     : ∀ {n Γ n' Γ' e ě C Č τ τ₁ τ₂ m}
             → n , Γ ⊢ e ↬ ě ⇑ τ
             → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂
             → n , Γ ⊢ C ↬ Č at anaPos τ₁ ▷ n' , Γ' [ m ]                                                →
             n , Γ ⊢ e ∘₂ C ↬ ě ∘₂ Č at synPos τ₂ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- DEBUG VIA TYPE SLICING — mark ⦅▸⇒⦆ on focus-on-argument (synthesis)
  --
  -- Fires when the externally-typed function synthesises a non-arrow τ.
  -- The argument is analysed at □. To debug:
  --   * Slice the function's syn type to a minimal slice that fails the
  --     match — points the user at exactly the misshapen sub-derivation.
  -- ============================================================
  ms∘₂⇑    : ∀ {n Γ n' Γ' e ě C Č τ m}
             → n , Γ ⊢ e ↬ ě ⇑ τ
             → (∀ {τ₁ τ₂} → τ ⊔ □ ⇒ □ ≢ τ₁ ⇒ τ₂)
             → n , Γ ⊢ C ↬ Č at anaPos □ ▷ n' , Γ' [ m ]                                                 →
             n , Γ ⊢ e ∘₂ C ↬ (ě ⦅▸⇒⦆) ∘₂ Č at synPos □ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- TYPE APPLICATION — synthesis, no mark
  -- ============================================================

  ms<>₁    : ∀ {n Γ n' Γ' C Č τ τ' σ m}
             → n , Γ ⊢ C ↬ Č at synPos τ ▷ n' , Γ' [ m ]
             → τ ⊔ ∀· □ ≡ ∀· τ'
             → n ⊢wf σ                                                                                      →
             n , Γ ⊢ C < σ >₁ ↬ Č < σ >₁ at synPos ([ zero ↦ σ ] τ') ▷ n' , Γ' [ m ]

  -- ============================================================
  -- DEBUG VIA TYPE SLICING — mark ⦅▸∀⦆ on type application
  --
  -- Fires when the focus's syn type is not a ∀. Slice the focus's syn type
  -- down to find the minimal subterm with a non-∀ head; combine with the
  -- enclosing context to see why the user expected a polymorphic value.
  -- ============================================================
  ms<>₁⇑   : ∀ {n Γ n' Γ' C Č τ σ m}
             → n , Γ ⊢ C ↬ Č at synPos τ ▷ n' , Γ' [ m ]
             → (∀ {τ'} → τ ⊔ ∀· □ ≢ ∀· τ')
             → n ⊢wf σ                                                                                      →
             n , Γ ⊢ C < σ >₁ ↬ (Č ⦅▸∀⦆) < σ >₁ at synPos □ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- PAIR — synthesis (no mark)
  -- ============================================================

  ms&₁     : ∀ {n Γ n' Γ' C Č e ě τ₁ τ₂ m}
             → n , Γ ⊢ C ↬ Č at synPos τ₁ ▷ n' , Γ' [ m ]
             → n , Γ ⊢ e ↬ ě ⇑ τ₂                                                                          →
             n , Γ ⊢ C &₁ e ↬ Č &₁ ě at synPos (τ₁ × τ₂) ▷ n' , Γ' [ m ]

  ms&₂     : ∀ {n Γ n' Γ' e ě C Č τ₁ τ₂ m}
             → n , Γ ⊢ e ↬ ě ⇑ τ₁
             → n , Γ ⊢ C ↬ Č at synPos τ₂ ▷ n' , Γ' [ m ]                                                →
             n , Γ ⊢ e &₂ C ↬ ě &₂ Č at synPos (τ₁ × τ₂) ▷ n' , Γ' [ m ]

  -- Pair — analysis with successful match (no mark)
  ma&₁     : ∀ {n Γ n' Γ' C Č e ě τ τ₁ τ₂ m}
             → τ ⊔ □ × □ ≡ τ₁ × τ₂
             → n , Γ ⊢ C ↬ Č at anaPos τ₁ ▷ n' , Γ' [ m ]
             → n , Γ ⊢ e ↬ ě ⇓ τ₂                                                                          →
             n , Γ ⊢ C &₁ e ↬ Č &₁ ě at anaPos τ ▷ n' , Γ' [ m ]

  ma&₂     : ∀ {n Γ n' Γ' e ě C Č τ τ₁ τ₂ m}
             → τ ⊔ □ × □ ≡ τ₁ × τ₂
             → n , Γ ⊢ e ↬ ě ⇓ τ₁
             → n , Γ ⊢ C ↬ Č at anaPos τ₂ ▷ n' , Γ' [ m ]                                                →
             n , Γ ⊢ e &₂ C ↬ ě &₂ Č at anaPos τ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- INJECTIONS — analysis (no mark when sum-shape matches)
  -- ============================================================

  maι₁     : ∀ {n Γ n' Γ' C Č τ τ₁ τ₂ m}
             → τ ⊔ □ + □ ≡ τ₁ + τ₂
             → n , Γ ⊢ C ↬ Č at anaPos τ₁ ▷ n' , Γ' [ m ]                                                →
             n , Γ ⊢ ι₁ C ↬ ι₁ Č at anaPos τ ▷ n' , Γ' [ m ]

  maι₂     : ∀ {n Γ n' Γ' C Č τ τ₁ τ₂ m}
             → τ ⊔ □ + □ ≡ τ₁ + τ₂
             → n , Γ ⊢ C ↬ Č at anaPos τ₂ ▷ n' , Γ' [ m ]                                                →
             n , Γ ⊢ ι₂ C ↬ ι₂ Č at anaPos τ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- DEBUG VIA TYPE SLICING — mark ⦅~+⦆ on injection in synthesis position
  --
  -- A bare ι₁/ι₂ has no synthesis type. The mark wraps the injection and
  -- synthesises □.
  -- This mark is similar to ⦅~⇒⦆ on bare λ⇒: a syntactic limitation, not
  -- a real type clash. Slicing the surrounding synPos context shows what
  -- consumer expected a synthesizable expression — useful for suggesting
  -- where to add a type annotation.
  -- ============================================================
  msι₁⇑    : ∀ {n Γ n' Γ' C Č m}
             → n , Γ ⊢ C ↬ Č at anaPos □ ▷ n' , Γ' [ m ]                                                 →
             n , Γ ⊢ ι₁ C ↬ (ι₁ Č) ⦅~+⦆ at synPos □ ▷ n' , Γ' [ m ]

  msι₂⇑    : ∀ {n Γ n' Γ' C Č m}
             → n , Γ ⊢ C ↬ Č at anaPos □ ▷ n' , Γ' [ m ]                                                 →
             n , Γ ⊢ ι₂ C ↬ (ι₂ Č) ⦅~+⦆ at synPos □ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- CASE — synthesis: focus on left/right branch (no mark when sum matches)
  -- ============================================================

  mscase₁  : ∀ {n Γ n' Γ' e ě C Č e' ě' τ τ₁ τ₂ τ₁' τ₂' m}
             → n , Γ ⊢ e ↬ ě ⇑ τ
             → τ ⊔ □ + □ ≡ τ₁ + τ₂
             → n , (τ₁ ∷ Γ) ⊢ C ↬ Č at synPos τ₁' ▷ n' , Γ' [ m ]
             → n , (τ₂ ∷ Γ) ⊢ e' ↬ ě' ⇑ τ₂'
             → τ₁' ~ τ₂'                                                                                    →
             n , Γ ⊢ case e of C ·₁ e' ↬ case ě of Č ·₁ ě' at synPos (τ₁' ⊔ τ₂') ▷ n' , Γ' [ m ]

  mscase₂  : ∀ {n Γ n' Γ' e ě e' ě' C Č τ τ₁ τ₂ τ₁' τ₂' m}
             → n , Γ ⊢ e ↬ ě ⇑ τ
             → τ ⊔ □ + □ ≡ τ₁ + τ₂
             → n , (τ₁ ∷ Γ) ⊢ e' ↬ ě' ⇑ τ₁'
             → n , (τ₂ ∷ Γ) ⊢ C ↬ Č at synPos τ₂' ▷ n' , Γ' [ m ]
             → τ₁' ~ τ₂'                                                                                    →
             n , Γ ⊢ case e of₂ e' · C ↬ case ě of₂ ě' · Č at synPos (τ₁' ⊔ τ₂') ▷ n' , Γ' [ m ]

  -- ============================================================
  -- DEBUG VIA TYPE SLICING — mark ⦅▸+⦆ on case scrutinee (synthesis)
  --
  -- Fires when the scrutinee synthesises a non-sum type. To debug:
  --   * Slice the scrutinee's syn type to find the minimal subterm with a
  --     non-sum head.
  --   * The branches are still classified at synPos τ₁'/τ₂' but with the
  --     branch-context types degraded to □ (since matching failed).
  -- ============================================================
  -- Note: mirrors mark⇑case⇑'s typing of branches at Γ (no binder), since
  -- the matching failed and there's no payload type to add.
  mscase₁⇑ : ∀ {n Γ n' Γ' e ě C Č e' ě' τ τ₁' τ₂' m}
             → n , Γ ⊢ e ↬ ě ⇑ τ
             → (∀ {τ₁ τ₂} → τ ⊔ □ + □ ≢ τ₁ + τ₂)
             → n , Γ ⊢ C ↬ Č at synPos τ₁' ▷ n' , Γ' [ m ]
             → n , Γ ⊢ e' ↬ ě' ⇑ τ₂'                                                                       →
             n , Γ ⊢ case e of C ·₁ e' ↬ case (ě ⦅▸+⦆) of Č ·₁ ě' at synPos □ ▷ n' , Γ' [ m ]

  mscase₂⇑ : ∀ {n Γ n' Γ' e ě e' ě' C Č τ τ₁' τ₂' m}
             → n , Γ ⊢ e ↬ ě ⇑ τ
             → (∀ {τ₁ τ₂} → τ ⊔ □ + □ ≢ τ₁ + τ₂)
             → n , Γ ⊢ e' ↬ ě' ⇑ τ₁'
             → n , Γ ⊢ C ↬ Č at synPos τ₂' ▷ n' , Γ' [ m ]                                                →
             n , Γ ⊢ case e of₂ e' · C ↬ case (ě ⦅▸+⦆) of₂ ě' · Č at synPos □ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- DEBUG VIA TYPE SLICING — synthesis case with inconsistent branches
  -- (no wrapper added; result type is □ instead of the join)
  --
  -- Fires when the scrutinee's sum matches but the two branches synthesise
  -- types τ₁' and τ₂' that are inconsistent. To debug:
  --   * Slice each branch's syn type down to a minimal slice that still
  --     witnesses τ₁' ≁ τ₂'. The pair of MinSynSlices points the user at
  --     exactly the parts of each branch that disagree.
  -- ============================================================
  mscase₁≁ : ∀ {n Γ n' Γ' e ě C Č e' ě' τ τ₁ τ₂ τ₁' τ₂' m}
             → n , Γ ⊢ e ↬ ě ⇑ τ
             → τ ⊔ □ + □ ≡ τ₁ + τ₂
             → n , (τ₁ ∷ Γ) ⊢ C ↬ Č at synPos τ₁' ▷ n' , Γ' [ m ]
             → n , (τ₂ ∷ Γ) ⊢ e' ↬ ě' ⇑ τ₂'
             → ¬ (τ₁' ~ τ₂')                                                                                →
             n , Γ ⊢ case e of C ·₁ e' ↬ case ě of Č ·₁ ě' at synPos □ ▷ n' , Γ' [ m ]

  mscase₂≁ : ∀ {n Γ n' Γ' e ě e' ě' C Č τ τ₁ τ₂ τ₁' τ₂' m}
             → n , Γ ⊢ e ↬ ě ⇑ τ
             → τ ⊔ □ + □ ≡ τ₁ + τ₂
             → n , (τ₁ ∷ Γ) ⊢ e' ↬ ě' ⇑ τ₁'
             → n , (τ₂ ∷ Γ) ⊢ C ↬ Č at synPos τ₂' ▷ n' , Γ' [ m ]
             → ¬ (τ₁' ~ τ₂')                                                                                →
             n , Γ ⊢ case e of₂ e' · C ↬ case ě of₂ ě' · Č at synPos □ ▷ n' , Γ' [ m ]

  -- Case — analysis: focus on left/right branch (no mark)
  macase₁  : ∀ {n Γ n' Γ' e ě C Č e' ě' τ τ₀ τ₁ τ₂ m}
             → n , Γ ⊢ e ↬ ě ⇑ τ₀
             → τ₀ ⊔ □ + □ ≡ τ₁ + τ₂
             → n , (τ₁ ∷ Γ) ⊢ C ↬ Č at anaPos τ ▷ n' , Γ' [ m ]
             → n , (τ₂ ∷ Γ) ⊢ e' ↬ ě' ⇓ τ                                                                  →
             n , Γ ⊢ case e of C ·₁ e' ↬ case ě of Č ·₁ ě' at anaPos τ ▷ n' , Γ' [ m ]

  macase₂  : ∀ {n Γ n' Γ' e ě e' ě' C Č τ τ₀ τ₁ τ₂ m}
             → n , Γ ⊢ e ↬ ě ⇑ τ₀
             → τ₀ ⊔ □ + □ ≡ τ₁ + τ₂
             → n , (τ₁ ∷ Γ) ⊢ e' ↬ ě' ⇓ τ
             → n , (τ₂ ∷ Γ) ⊢ C ↬ Č at anaPos τ ▷ n' , Γ' [ m ]                                          →
             n , Γ ⊢ case e of₂ e' · C ↬ case ě of₂ ě' · Č at anaPos τ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- DEBUG VIA TYPE SLICING — mark ⦅▸+⦆ on case scrutinee (analysis)
  --
  -- Fires when the scrutinee in an analysis case has non-sum type. The
  -- branches are reclassified with □ binders. Same debugging strategy as
  -- the synthesis variant above.
  -- ============================================================
  macase₁⇑ : ∀ {n Γ n' Γ' e ě C Č e' ě' τ τ₀ m}
             → n , Γ ⊢ e ↬ ě ⇑ τ₀
             → (∀ {τ₁ τ₂} → τ₀ ⊔ □ + □ ≢ τ₁ + τ₂)
             → n , (□ ∷ Γ) ⊢ C ↬ Č at anaPos τ ▷ n' , Γ' [ m ]
             → n , (□ ∷ Γ) ⊢ e' ↬ ě' ⇓ τ                                                                   →
             n , Γ ⊢ case e of C ·₁ e' ↬ case (ě ⦅▸+⦆) of Č ·₁ ě' at anaPos τ ▷ n' , Γ' [ m ]

  macase₂⇑ : ∀ {n Γ n' Γ' e ě e' ě' C Č τ τ₀ m}
             → n , Γ ⊢ e ↬ ě ⇑ τ₀
             → (∀ {τ₁ τ₂} → τ₀ ⊔ □ + □ ≢ τ₁ + τ₂)
             → n , (□ ∷ Γ) ⊢ e' ↬ ě' ⇓ τ
             → n , (□ ∷ Γ) ⊢ C ↬ Č at anaPos τ ▷ n' , Γ' [ m ]                                           →
             n , Γ ⊢ case e of₂ e' · C ↬ case (ě ⦅▸+⦆) of₂ ě' · Č at anaPos τ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- PROJECTIONS — synthesis, no mark
  -- ============================================================

  msπ₁     : ∀ {n Γ n' Γ' C Č τ τ₁ τ₂ m}
             → n , Γ ⊢ C ↬ Č at synPos τ ▷ n' , Γ' [ m ]
             → τ ⊔ □ × □ ≡ τ₁ × τ₂                                                                          →
             n , Γ ⊢ π₁ C ↬ π₁ Č at synPos τ₁ ▷ n' , Γ' [ m ]

  msπ₂     : ∀ {n Γ n' Γ' C Č τ τ₁ τ₂ m}
             → n , Γ ⊢ C ↬ Č at synPos τ ▷ n' , Γ' [ m ]
             → τ ⊔ □ × □ ≡ τ₁ × τ₂                                                                          →
             n , Γ ⊢ π₂ C ↬ π₂ Č at synPos τ₂ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- DEBUG VIA TYPE SLICING — mark ⦅▸×⦆ on projection
  --
  -- Fires when the projected expression has a non-product syn type. To debug:
  --   * Slice the focus's syn type τ down to the smallest subterm that
  --     gives a non-× head — gives a precise, source-level explanation of
  --     why the projection failed.
  -- ============================================================
  msπ₁⇑    : ∀ {n Γ n' Γ' C Č τ m}
             → n , Γ ⊢ C ↬ Č at synPos τ ▷ n' , Γ' [ m ]
             → (∀ {τ₁ τ₂} → τ ⊔ □ × □ ≢ τ₁ × τ₂)                                                            →
             n , Γ ⊢ π₁ C ↬ π₁ (Č ⦅▸×⦆) at synPos □ ▷ n' , Γ' [ m ]

  msπ₂⇑    : ∀ {n Γ n' Γ' C Č τ m}
             → n , Γ ⊢ C ↬ Č at synPos τ ▷ n' , Γ' [ m ]
             → (∀ {τ₁ τ₂} → τ ⊔ □ × □ ≢ τ₁ × τ₂)                                                            →
             n , Γ ⊢ π₂ C ↬ π₂ (Č ⦅▸×⦆) at synPos □ ▷ n' , Γ' [ m ]

  -- ============================================================
  -- TYPE ABSTRACTION — synthesis, no mark
  -- ============================================================

  msΛ      : ∀ {n Γ n' Γ' C Č τ m}
             → suc n , shiftΓ (suc zero) Γ ⊢ C ↬ Č at synPos τ ▷ n' , Γ' [ m ]                            →
             n , Γ ⊢ Λ C ↬ Λ Č at synPos (∀· τ) ▷ n' , Γ' [ m ]

  -- ============================================================
  -- DEFINITION — synthesis (no mark)
  -- ============================================================

  msdef₁   : ∀ {n Γ n' Γ' C Č e ě τ' τ m}
             → n , Γ ⊢ C ↬ Č at synPos τ' ▷ n' , Γ' [ m ]
             → n , (τ' ∷ Γ) ⊢ e ↬ ě ⇑ τ                                                                    →
             n , Γ ⊢ def C ⊢₁ e ↬ def Č ⊢₁ ě at synPos τ ▷ n' , Γ' [ m ]

  msdef₂   : ∀ {n Γ n' Γ' e ě C Č τ' τ m}
             → n , Γ ⊢ e ↬ ě ⇑ τ'
             → n , (τ' ∷ Γ) ⊢ C ↬ Č at synPos τ ▷ n' , Γ' [ m ]                                          →
             n , Γ ⊢ def e ⊢₂ C ↬ def ě ⊢₂ Č at synPos τ ▷ n' , Γ' [ m ]

  madef₁   : ∀ {n Γ n' Γ' C Č e ě τ τ' m}
             → n , Γ ⊢ C ↬ Č at synPos τ' ▷ n' , Γ' [ m ]
             → n , (τ' ∷ Γ) ⊢ e ↬ ě ⇓ τ                                                                    →
             n , Γ ⊢ def C ⊢₁ e ↬ def Č ⊢₁ ě at anaPos τ ▷ n' , Γ' [ m ]

  madef₂   : ∀ {n Γ n' Γ' e ě C Č τ τ' m}
             → n , Γ ⊢ e ↬ ě ⇑ τ'
             → n , (τ' ∷ Γ) ⊢ C ↬ Č at anaPos τ ▷ n' , Γ' [ m ]                                          →
             n , Γ ⊢ def e ⊢₂ C ↬ def ě ⊢₂ Č at anaPos τ ▷ n' , Γ' [ m ]

-- =================================================================
-- FREE-VARIABLE MARK ⟨ k ⟩⇑
--
-- The ⟨ k ⟩⇑ mark is NOT a wrapper — it is a leaf that *replaces* an
-- otherwise-leaf variable lookup. It does not appear as an MCtx
-- constructor; it appears only as a focus MExp via the MFocusTyping
-- judgment using mark⇑Var⇑. A focus typing of `⟨ k ⟩⇑` at synPos □ in any
-- enclosing context is a valid classification.
--
-- IMPORTANT: this mark is NOT a type error. Type slicing CANNOT debug it
-- meaningfully — slicing types of the *enclosing* context says nothing
-- about which variable was missing. Debugging an unbound variable is a
-- scope-resolution task, not a type-clash task. Tooling should report
-- "unbound variable k" without invoking type slicing at all.
-- =================================================================

-- =================================================================
-- SOUNDNESS: classification + focus marking → marking of the plug
-- =================================================================

mutual
  mplug-compose-syn : ∀ {n Γ n' Γ' C Č e ě τ m}
    → n , Γ ⊢ C ↬ Č at synPos τ ▷ n' , Γ' [ m ]
    → MFocusTyping n' Γ' e ě m
    → n , Γ ⊢ plug C e ↬ mplug Č ě ⇑ τ

  mplug-compose-syn ms○ ft = ft
  mplug-compose-syn (msλ: wf cls) ft = mark⇑λ: wf (mplug-compose-syn cls ft)
  mplug-compose-syn (ms∘₁ cls eq d₂) ft = mark⇑∘ (mplug-compose-syn cls ft) eq d₂
  mplug-compose-syn (ms∘₁⇑ cls ¬eq d₂) ft = mark⇑∘⇑ (mplug-compose-syn cls ft) ¬eq d₂
  mplug-compose-syn (ms∘₂ d₁ eq cls) ft = mark⇑∘ d₁ eq (mplug-compose-ana cls ft)
  mplug-compose-syn (ms∘₂⇑ d₁ ¬eq cls) ft = mark⇑∘⇑ d₁ ¬eq (mplug-compose-ana cls ft)
  mplug-compose-syn (ms<>₁ cls eq wf) ft = mark⇑<> (mplug-compose-syn cls ft) eq wf
  mplug-compose-syn (ms<>₁⇑ cls ¬eq wf) ft = mark⇑<>⇑ (mplug-compose-syn cls ft) ¬eq wf
  mplug-compose-syn (ms&₁ cls d₂) ft = mark⇑& (mplug-compose-syn cls ft) d₂
  mplug-compose-syn (ms&₂ d₁ cls) ft = mark⇑& d₁ (mplug-compose-syn cls ft)
  mplug-compose-syn (msπ₁ cls eq) ft = mark⇑π₁ (mplug-compose-syn cls ft) eq
  mplug-compose-syn (msπ₂ cls eq) ft = mark⇑π₂ (mplug-compose-syn cls ft) eq
  mplug-compose-syn (msπ₁⇑ cls ¬eq) ft = mark⇑π₁⇑ (mplug-compose-syn cls ft) ¬eq
  mplug-compose-syn (msπ₂⇑ cls ¬eq) ft = mark⇑π₂⇑ (mplug-compose-syn cls ft) ¬eq
  mplug-compose-syn (msΛ cls) ft = mark⇑Λ (mplug-compose-syn cls ft)
  mplug-compose-syn (msdef₁ cls d₂) ft = mark⇑def (mplug-compose-syn cls ft) d₂
  mplug-compose-syn (msdef₂ d₁ cls) ft = mark⇑def d₁ (mplug-compose-syn cls ft)
  mplug-compose-syn (mscase₁ d₀ eq cls d₂ con) ft = mark⇑case d₀ eq (mplug-compose-syn cls ft) d₂ con
  mplug-compose-syn (mscase₂ d₀ eq d₁ cls con) ft = mark⇑case d₀ eq d₁ (mplug-compose-syn cls ft) con
  mplug-compose-syn (mscase₁⇑ d₀ ¬eq cls d₂) ft = mark⇑case⇑ d₀ ¬eq (mplug-compose-syn cls ft) d₂
  mplug-compose-syn (mscase₂⇑ d₀ ¬eq d₁ cls) ft = mark⇑case⇑ d₀ ¬eq d₁ (mplug-compose-syn cls ft)
  mplug-compose-syn (mscase₁≁ d₀ eq cls d₂ ¬con) ft = mark⇑case≁ d₀ eq (mplug-compose-syn cls ft) d₂ ¬con
  mplug-compose-syn (mscase₂≁ d₀ eq d₁ cls ¬con) ft = mark⇑case≁ d₀ eq d₁ (mplug-compose-syn cls ft) ¬con
  mplug-compose-syn (msλ⇒⇑ cls) ft = mark⇑λ⇒ (mplug-compose-ana cls ft)
  mplug-compose-syn (msι₁⇑ cls) ft = mark⇑ι₁ (mplug-compose-ana cls ft)
  mplug-compose-syn (msι₂⇑ cls) ft = mark⇑ι₂ (mplug-compose-ana cls ft)

  mplug-compose-ana : ∀ {n Γ n' Γ' C Č e ě τ m}
    → n , Γ ⊢ C ↬ Č at anaPos τ ▷ n' , Γ' [ m ]
    → MFocusTyping n' Γ' e ě m
    → n , Γ ⊢ plug C e ↬ mplug Č ě ⇓ τ

  mplug-compose-ana ma○ ft = ft
  mplug-compose-ana (maSub cls con) ft = mark⇓sub (mplug-compose-syn cls ft) con
  mplug-compose-ana (maSub⇑ cls ¬con) ft = mark⇓sub⇑ (mplug-compose-syn cls ft) ¬con
  mplug-compose-ana (maλ: c eq wf cls) ft = mark⇓λ: c eq wf (mplug-compose-ana cls ft)
  mplug-compose-ana (maλ⇒ eq cls) ft = mark⇓λ eq (mplug-compose-ana cls ft)
  mplug-compose-ana (maλ⇒⇑ ¬eq cls) ft = mark⇓λ⇑ ¬eq (mplug-compose-ana cls ft)
  mplug-compose-ana (ma&₁ eq cls d₂) ft = mark⇓& eq (mplug-compose-ana cls ft) d₂
  mplug-compose-ana (ma&₂ eq d₁ cls) ft = mark⇓& eq d₁ (mplug-compose-ana cls ft)
  mplug-compose-ana (maι₁ eq cls) ft = mark⇓ι₁ eq (mplug-compose-ana cls ft)
  mplug-compose-ana (maι₂ eq cls) ft = mark⇓ι₂ eq (mplug-compose-ana cls ft)
  mplug-compose-ana (macase₁ d₀ eq cls d₂) ft = mark⇓case d₀ eq (mplug-compose-ana cls ft) d₂
  mplug-compose-ana (macase₂ d₀ eq d₁ cls) ft = mark⇓case d₀ eq d₁ (mplug-compose-ana cls ft)
  mplug-compose-ana (macase₁⇑ d₀ ¬eq cls d₂) ft = mark⇓case⇑ d₀ ¬eq (mplug-compose-ana cls ft) d₂
  mplug-compose-ana (macase₂⇑ d₀ ¬eq d₁ cls) ft = mark⇓case⇑ d₀ ¬eq d₁ (mplug-compose-ana cls ft)
  mplug-compose-ana (madef₁ cls d₂) ft = mark⇓def (mplug-compose-syn cls ft) d₂
  mplug-compose-ana (madef₂ d₁ cls) ft = mark⇓def d₁ (mplug-compose-ana cls ft)

-- =================================================================
-- TOTALITY: every marking judgment of a plug decomposes into a
-- classification + focus marking.
-- =================================================================

-- Result of decomposing a marking judgment for `plug C e`:
--   ∃ ě_focus, Č, n', Γ', m. cls ∧ focus-marking ∧ (mplug Č ě_focus ≡ ě)
-- where ě is the marked image of plug C e.
MPlugResult : ℕ → Assms → Ctx → Exp → MExp → Position → Set
MPlugResult n Γ C e ě p =
  Σ MExp λ ě_focus → Σ MCtx λ Č → Σ ℕ λ n' → Σ Assms λ Γ' → Σ CtxMode λ m →
    (n , Γ ⊢ C ↬ Č at p ▷ n' , Γ' [ m ]) ∧
    MFocusTyping n' Γ' e ě_focus m ∧
    mplug Č ě_focus ≡ ě

-- Totality: every marking judgment of plug C e decomposes into a
-- classification of C + focus marking, mirroring plug-syn / plug-ana
-- from Semantics.Statics.CtxTyping but threading the marked side.
--
-- Proof structure: mutual recursion on the input Ctx C. For each
-- constructor of C, the marking judgment's top constructor is
-- structurally constrained (by mark-wf-syn / mark-wf-ana inversion),
-- so we pattern-match on the marking judgment and recurse.
mutual
  mplug-decompose-syn : ∀ {n Γ e ě τ} (C : Ctx)
    → n , Γ ⊢ plug C e ↬ ě ⇑ τ
    → MPlugResult n Γ C e ě (synPos τ)

  mplug-decompose-syn ○ d =
    _ , ○ , _ , _ , _ , ms○ , d , refl

  mplug-decompose-syn (λ: τ ⇒ C) (mark⇑λ: wf d)
    with mplug-decompose-syn C d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , (λ: τ ⇒ Č) , _ , _ , _ , msλ: wf cls , ft , cong (λ: τ ⇒_) eq

  mplug-decompose-syn (λ⇒ C) (mark⇑λ⇒ d)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , (λ⇒ Č) ⦅~⇒⦆ , _ , _ , _ , msλ⇒⇑ cls , ft , cong (λ x → (λ⇒ x) ⦅~⇒⦆) eq

  mplug-decompose-syn (C ∘₁ e₂) (mark⇑∘ d₁ eq d₂)
    with mplug-decompose-syn C d₁
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , Č ∘₁ _ , _ , _ , _ , ms∘₁ cls eq d₂ , ft , cong (_∘ _) feq
  mplug-decompose-syn (C ∘₁ e₂) (mark⇑∘⇑ d₁ ¬eq d₂)
    with mplug-decompose-syn C d₁
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (Č ⦅▸⇒⦆) ∘₁ _ , _ , _ , _ , ms∘₁⇑ cls ¬eq d₂ , ft
        , cong (λ x → (x ⦅▸⇒⦆) ∘ _) feq

  mplug-decompose-syn (e₁ ∘₂ C) (mark⇑∘ d₁ eq d₂)
    with mplug-decompose-ana C d₂
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , _ ∘₂ Č , _ , _ , _ , ms∘₂ d₁ eq cls , ft , cong (_ ∘_) feq
  mplug-decompose-syn (e₁ ∘₂ C) (mark⇑∘⇑ d₁ ¬eq d₂)
    with mplug-decompose-ana C d₂
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , _ ∘₂ Č , _ , _ , _ , ms∘₂⇑ d₁ ¬eq cls , ft , cong (_ ∘_) feq

  mplug-decompose-syn (C < σ >₁) (mark⇑<> d eq wf)
    with mplug-decompose-syn C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , Č < σ >₁ , _ , _ , _ , ms<>₁ cls eq wf , ft , cong (_< σ >) feq
  mplug-decompose-syn (C < σ >₁) (mark⇑<>⇑ d ¬eq wf)
    with mplug-decompose-syn C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (Č ⦅▸∀⦆) < σ >₁ , _ , _ , _ , ms<>₁⇑ cls ¬eq wf , ft
        , cong (λ x → (x ⦅▸∀⦆) < σ >) feq

  mplug-decompose-syn (C &₁ e₂) (mark⇑& d₁ d₂)
    with mplug-decompose-syn C d₁
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , Č &₁ _ , _ , _ , _ , ms&₁ cls d₂ , ft , cong (_& _) feq
  mplug-decompose-syn (e₁ &₂ C) (mark⇑& d₁ d₂)
    with mplug-decompose-syn C d₂
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , _ &₂ Č , _ , _ , _ , ms&₂ d₁ cls , ft , cong (_ &_) feq

  mplug-decompose-syn (ι₁ C) (mark⇑ι₁ d)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (ι₁ Č) ⦅~+⦆ , _ , _ , _ , msι₁⇑ cls , ft
        , cong (λ x → (ι₁ x) ⦅~+⦆) feq
  mplug-decompose-syn (ι₂ C) (mark⇑ι₂ d)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (ι₂ Č) ⦅~+⦆ , _ , _ , _ , msι₂⇑ cls , ft
        , cong (λ x → (ι₂ x) ⦅~+⦆) feq

  mplug-decompose-syn (case e₀ of C ·₁ e₂) (mark⇑case d₀ eq d₁ d₂ con)
    with mplug-decompose-syn C d₁
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (case _ of Č ·₁ _) , _ , _ , _ , mscase₁ d₀ eq cls d₂ con , ft
        , cong (λ x → case _ of x · _) feq
  mplug-decompose-syn (case e₀ of C ·₁ e₂) (mark⇑case⇑ d₀ ¬eq d₁ d₂)
    with mplug-decompose-syn C d₁
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (case _ of Č ·₁ _) , _ , _ , _ , mscase₁⇑ d₀ ¬eq cls d₂ , ft
        , cong (λ x → case (_ ⦅▸+⦆) of x · _) feq
  mplug-decompose-syn (case e₀ of C ·₁ e₂) (mark⇑case≁ d₀ eq d₁ d₂ ¬con)
    with mplug-decompose-syn C d₁
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (case _ of Č ·₁ _) , _ , _ , _ , mscase₁≁ d₀ eq cls d₂ ¬con , ft
        , cong (λ x → case _ of x · _) feq

  mplug-decompose-syn (case e₀ of₂ e₁ · C) (mark⇑case d₀ eq d₁ d₂ con)
    with mplug-decompose-syn C d₂
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (case _ of₂ _ · Č) , _ , _ , _ , mscase₂ d₀ eq d₁ cls con , ft
        , cong (λ x → case _ of _ · x) feq
  mplug-decompose-syn (case e₀ of₂ e₁ · C) (mark⇑case⇑ d₀ ¬eq d₁ d₂)
    with mplug-decompose-syn C d₂
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (case _ of₂ _ · Č) , _ , _ , _ , mscase₂⇑ d₀ ¬eq d₁ cls , ft
        , cong (λ x → case (_ ⦅▸+⦆) of _ · x) feq
  mplug-decompose-syn (case e₀ of₂ e₁ · C) (mark⇑case≁ d₀ eq d₁ d₂ ¬con)
    with mplug-decompose-syn C d₂
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (case _ of₂ _ · Č) , _ , _ , _ , mscase₂≁ d₀ eq d₁ cls ¬con , ft
        , cong (λ x → case _ of _ · x) feq

  mplug-decompose-syn (π₁ C) (mark⇑π₁ d eq)
    with mplug-decompose-syn C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , π₁ Č , _ , _ , _ , msπ₁ cls eq , ft , cong π₁ feq
  mplug-decompose-syn (π₁ C) (mark⇑π₁⇑ d ¬eq)
    with mplug-decompose-syn C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , π₁ (Č ⦅▸×⦆) , _ , _ , _ , msπ₁⇑ cls ¬eq , ft
        , cong (λ x → π₁ (x ⦅▸×⦆)) feq

  mplug-decompose-syn (π₂ C) (mark⇑π₂ d eq)
    with mplug-decompose-syn C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , π₂ Č , _ , _ , _ , msπ₂ cls eq , ft , cong π₂ feq
  mplug-decompose-syn (π₂ C) (mark⇑π₂⇑ d ¬eq)
    with mplug-decompose-syn C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , π₂ (Č ⦅▸×⦆) , _ , _ , _ , msπ₂⇑ cls ¬eq , ft
        , cong (λ x → π₂ (x ⦅▸×⦆)) feq

  mplug-decompose-syn (Λ C) (mark⇑Λ d)
    with mplug-decompose-syn C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , Λ Č , _ , _ , _ , msΛ cls , ft , cong Λ feq

  mplug-decompose-syn (def C ⊢₁ e₂) (mark⇑def d₁ d₂)
    with mplug-decompose-syn C d₁
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (def Č ⊢₁ _) , _ , _ , _ , msdef₁ cls d₂ , ft
        , cong (λ x → def x ⊢ _) feq
  mplug-decompose-syn (def e₁ ⊢₂ C) (mark⇑def d₁ d₂)
    with mplug-decompose-syn C d₂
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (def _ ⊢₂ Č) , _ , _ , _ , msdef₂ d₁ cls , ft
        , cong (λ x → def _ ⊢ x) feq

  mplug-decompose-ana : ∀ {n Γ e ě τ} (C : Ctx)
    → n , Γ ⊢ plug C e ↬ ě ⇓ τ
    → MPlugResult n Γ C e ě (anaPos τ)

  -- Hole at ana: peel off subsumption if present; otherwise use ma○.
  mplug-decompose-ana ○ (mark⇓sub d con) =
    _ , ○ , _ , _ , _ , maSub ms○ con , d , refl
  mplug-decompose-ana ○ (mark⇓sub⇑ d ¬con) =
    _ , ○ ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ ms○ ¬con , d , refl
  mplug-decompose-ana ○ d@(mark⇓λ _ _)      = _ , ○ , _ , _ , _ , ma○ , d , refl
  mplug-decompose-ana ○ d@(mark⇓λ⇑ _ _)     = _ , ○ , _ , _ , _ , ma○ , d , refl
  mplug-decompose-ana ○ d@(mark⇓λ: _ _ _ _) = _ , ○ , _ , _ , _ , ma○ , d , refl
  mplug-decompose-ana ○ d@(mark⇓ι₁ _ _)     = _ , ○ , _ , _ , _ , ma○ , d , refl
  mplug-decompose-ana ○ d@(mark⇓ι₂ _ _)     = _ , ○ , _ , _ , _ , ma○ , d , refl
  mplug-decompose-ana ○ d@(mark⇓& _ _ _)    = _ , ○ , _ , _ , _ , ma○ , d , refl
  mplug-decompose-ana ○ d@(mark⇓def _ _)    = _ , ○ , _ , _ , _ , ma○ , d , refl
  mplug-decompose-ana ○ d@(mark⇓case _ _ _ _) = _ , ○ , _ , _ , _ , ma○ , d , refl
  mplug-decompose-ana ○ d@(mark⇓case⇑ _ _ _ _) = _ , ○ , _ , _ , _ , ma○ , d , refl

  -- Non-hole Ctx constructors: either direct analysis rule, or subsumption.
  mplug-decompose-ana (λ: τ ⇒ C) (mark⇓sub d con)
    with mplug-decompose-syn (λ: τ ⇒ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č , _ , _ , _ , maSub cls con , ft , eq
  mplug-decompose-ana (λ: τ ⇒ C) (mark⇓sub⇑ d ¬con)
    with mplug-decompose-syn (λ: τ ⇒ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ cls ¬con , ft , cong (_⦅≁ _ ⦆) eq
  mplug-decompose-ana (λ: τ₁ ⇒ C) (mark⇓λ: c eq wf d)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (λ: τ₁ ⇒ Č) , _ , _ , _ , maλ: c eq wf cls , ft , cong (λ: τ₁ ⇒_) feq

  mplug-decompose-ana (λ⇒ C) (mark⇓sub (mark⇑λ⇒ d) con)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (λ⇒ Č) ⦅~⇒⦆ , _ , _ , _ , maSub (msλ⇒⇑ cls) con , ft
        , cong (λ x → (λ⇒ x) ⦅~⇒⦆) feq
  mplug-decompose-ana (λ⇒ C) (mark⇓sub⇑ (mark⇑λ⇒ d) ¬con)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , ((λ⇒ Č) ⦅~⇒⦆) ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ (msλ⇒⇑ cls) ¬con , ft
        , cong (λ x → ((λ⇒ x) ⦅~⇒⦆) ⦅≁ _ ⦆) feq
  mplug-decompose-ana (λ⇒ C) (mark⇓λ eq d)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (λ⇒ Č) , _ , _ , _ , maλ⇒ eq cls , ft , cong λ⇒_ feq
  mplug-decompose-ana (λ⇒ C) (mark⇓λ⇑ ¬eq d)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (λ⇒ Č) ⦅~⇒⦆ , _ , _ , _ , maλ⇒⇑ ¬eq cls , ft
        , cong (λ x → (λ⇒ x) ⦅~⇒⦆) feq

  mplug-decompose-ana (C ∘₁ e₂) (mark⇓sub d con)
    with mplug-decompose-syn (C ∘₁ e₂) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č , _ , _ , _ , maSub cls con , ft , eq
  mplug-decompose-ana (C ∘₁ e₂) (mark⇓sub⇑ d ¬con)
    with mplug-decompose-syn (C ∘₁ e₂) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ cls ¬con , ft , cong (_⦅≁ _ ⦆) eq
  mplug-decompose-ana (e₁ ∘₂ C) (mark⇓sub d con)
    with mplug-decompose-syn (e₁ ∘₂ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č , _ , _ , _ , maSub cls con , ft , eq
  mplug-decompose-ana (e₁ ∘₂ C) (mark⇓sub⇑ d ¬con)
    with mplug-decompose-syn (e₁ ∘₂ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ cls ¬con , ft , cong (_⦅≁ _ ⦆) eq

  mplug-decompose-ana (C < σ >₁) (mark⇓sub d con)
    with mplug-decompose-syn (C < σ >₁) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č , _ , _ , _ , maSub cls con , ft , eq
  mplug-decompose-ana (C < σ >₁) (mark⇓sub⇑ d ¬con)
    with mplug-decompose-syn (C < σ >₁) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ cls ¬con , ft , cong (_⦅≁ _ ⦆) eq

  mplug-decompose-ana (C &₁ e₂) (mark⇓sub d con)
    with mplug-decompose-syn (C &₁ e₂) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č , _ , _ , _ , maSub cls con , ft , eq
  mplug-decompose-ana (C &₁ e₂) (mark⇓sub⇑ d ¬con)
    with mplug-decompose-syn (C &₁ e₂) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ cls ¬con , ft , cong (_⦅≁ _ ⦆) eq
  mplug-decompose-ana (C &₁ e₂) (mark⇓& eq d₁ d₂)
    with mplug-decompose-ana C d₁
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , Č &₁ _ , _ , _ , _ , ma&₁ eq cls d₂ , ft , cong (_& _) feq
  mplug-decompose-ana (e₁ &₂ C) (mark⇓sub d con)
    with mplug-decompose-syn (e₁ &₂ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č , _ , _ , _ , maSub cls con , ft , eq
  mplug-decompose-ana (e₁ &₂ C) (mark⇓sub⇑ d ¬con)
    with mplug-decompose-syn (e₁ &₂ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ cls ¬con , ft , cong (_⦅≁ _ ⦆) eq
  mplug-decompose-ana (e₁ &₂ C) (mark⇓& eq d₁ d₂)
    with mplug-decompose-ana C d₂
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , _ &₂ Č , _ , _ , _ , ma&₂ eq d₁ cls , ft , cong (_ &_) feq

  mplug-decompose-ana (ι₁ C) (mark⇓sub (mark⇑ι₁ d) con)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (ι₁ Č) ⦅~+⦆ , _ , _ , _ , maSub (msι₁⇑ cls) con , ft
        , cong (λ x → (ι₁ x) ⦅~+⦆) feq
  mplug-decompose-ana (ι₁ C) (mark⇓sub⇑ (mark⇑ι₁ d) ¬con)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , ((ι₁ Č) ⦅~+⦆) ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ (msι₁⇑ cls) ¬con , ft
        , cong (λ x → ((ι₁ x) ⦅~+⦆) ⦅≁ _ ⦆) feq
  mplug-decompose-ana (ι₁ C) (mark⇓ι₁ eq d)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , ι₁ Č , _ , _ , _ , maι₁ eq cls , ft , cong ι₁ feq
  mplug-decompose-ana (ι₂ C) (mark⇓sub (mark⇑ι₂ d) con)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (ι₂ Č) ⦅~+⦆ , _ , _ , _ , maSub (msι₂⇑ cls) con , ft
        , cong (λ x → (ι₂ x) ⦅~+⦆) feq
  mplug-decompose-ana (ι₂ C) (mark⇓sub⇑ (mark⇑ι₂ d) ¬con)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , ((ι₂ Č) ⦅~+⦆) ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ (msι₂⇑ cls) ¬con , ft
        , cong (λ x → ((ι₂ x) ⦅~+⦆) ⦅≁ _ ⦆) feq
  mplug-decompose-ana (ι₂ C) (mark⇓ι₂ eq d)
    with mplug-decompose-ana C d
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , ι₂ Č , _ , _ , _ , maι₂ eq cls , ft , cong ι₂ feq

  mplug-decompose-ana (case e₀ of C ·₁ e₂) (mark⇓sub d con)
    with mplug-decompose-syn (case e₀ of C ·₁ e₂) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č , _ , _ , _ , maSub cls con , ft , eq
  mplug-decompose-ana (case e₀ of C ·₁ e₂) (mark⇓sub⇑ d ¬con)
    with mplug-decompose-syn (case e₀ of C ·₁ e₂) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ cls ¬con , ft , cong (_⦅≁ _ ⦆) eq
  mplug-decompose-ana (case e₀ of C ·₁ e₂) (mark⇓case d₀ eq d₁ d₂)
    with mplug-decompose-ana C d₁
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (case _ of Č ·₁ _) , _ , _ , _ , macase₁ d₀ eq cls d₂ , ft
        , cong (λ x → case _ of x · _) feq
  mplug-decompose-ana (case e₀ of C ·₁ e₂) (mark⇓case⇑ d₀ ¬eq d₁ d₂)
    with mplug-decompose-ana C d₁
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (case _ of Č ·₁ _) , _ , _ , _ , macase₁⇑ d₀ ¬eq cls d₂ , ft
        , cong (λ x → case (_ ⦅▸+⦆) of x · _) feq

  mplug-decompose-ana (case e₀ of₂ e₁ · C) (mark⇓sub d con)
    with mplug-decompose-syn (case e₀ of₂ e₁ · C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č , _ , _ , _ , maSub cls con , ft , eq
  mplug-decompose-ana (case e₀ of₂ e₁ · C) (mark⇓sub⇑ d ¬con)
    with mplug-decompose-syn (case e₀ of₂ e₁ · C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ cls ¬con , ft , cong (_⦅≁ _ ⦆) eq
  mplug-decompose-ana (case e₀ of₂ e₁ · C) (mark⇓case d₀ eq d₁ d₂)
    with mplug-decompose-ana C d₂
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (case _ of₂ _ · Č) , _ , _ , _ , macase₂ d₀ eq d₁ cls , ft
        , cong (λ x → case _ of _ · x) feq
  mplug-decompose-ana (case e₀ of₂ e₁ · C) (mark⇓case⇑ d₀ ¬eq d₁ d₂)
    with mplug-decompose-ana C d₂
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (case _ of₂ _ · Č) , _ , _ , _ , macase₂⇑ d₀ ¬eq d₁ cls , ft
        , cong (λ x → case (_ ⦅▸+⦆) of _ · x) feq

  mplug-decompose-ana (π₁ C) (mark⇓sub d con)
    with mplug-decompose-syn (π₁ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č , _ , _ , _ , maSub cls con , ft , eq
  mplug-decompose-ana (π₁ C) (mark⇓sub⇑ d ¬con)
    with mplug-decompose-syn (π₁ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ cls ¬con , ft , cong (_⦅≁ _ ⦆) eq
  mplug-decompose-ana (π₂ C) (mark⇓sub d con)
    with mplug-decompose-syn (π₂ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č , _ , _ , _ , maSub cls con , ft , eq
  mplug-decompose-ana (π₂ C) (mark⇓sub⇑ d ¬con)
    with mplug-decompose-syn (π₂ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ cls ¬con , ft , cong (_⦅≁ _ ⦆) eq

  mplug-decompose-ana (Λ C) (mark⇓sub d con)
    with mplug-decompose-syn (Λ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č , _ , _ , _ , maSub cls con , ft , eq
  mplug-decompose-ana (Λ C) (mark⇓sub⇑ d ¬con)
    with mplug-decompose-syn (Λ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ cls ¬con , ft , cong (_⦅≁ _ ⦆) eq

  mplug-decompose-ana (def C ⊢₁ e₂) (mark⇓sub d con)
    with mplug-decompose-syn (def C ⊢₁ e₂) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č , _ , _ , _ , maSub cls con , ft , eq
  mplug-decompose-ana (def C ⊢₁ e₂) (mark⇓sub⇑ d ¬con)
    with mplug-decompose-syn (def C ⊢₁ e₂) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ cls ¬con , ft , cong (_⦅≁ _ ⦆) eq
  mplug-decompose-ana (def C ⊢₁ e₂) (mark⇓def d₁ d₂)
    with mplug-decompose-syn C d₁
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (def Č ⊢₁ _) , _ , _ , _ , madef₁ cls d₂ , ft
        , cong (λ x → def x ⊢ _) feq
  mplug-decompose-ana (def e₁ ⊢₂ C) (mark⇓sub d con)
    with mplug-decompose-syn (def e₁ ⊢₂ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č , _ , _ , _ , maSub cls con , ft , eq
  mplug-decompose-ana (def e₁ ⊢₂ C) (mark⇓sub⇑ d ¬con)
    with mplug-decompose-syn (def e₁ ⊢₂ C) d
  ... | ě , Č , _ , _ , _ , cls , ft , eq =
        ě , Č ⦅≁ _ ⦆ , _ , _ , _ , maSub⇑ cls ¬con , ft , cong (_⦅≁ _ ⦆) eq
  mplug-decompose-ana (def e₁ ⊢₂ C) (mark⇓def d₁ d₂)
    with mplug-decompose-ana C d₂
  ... | ě , Č , _ , _ , _ , cls , ft , feq =
        ě , (def _ ⊢₂ Č) , _ , _ , _ , madef₂ d₁ cls , ft
        , cong (λ x → def _ ⊢ x) feq
