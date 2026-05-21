open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List using (_∷_)
open import Core
open import Core.Typ.WellFormedness using (wf□)
open import Core.Typ.Lift using (unmatch⇒-≡-fst; unmatch⇒-≡-snd;
                                  unmatch×-≡-fst; unmatch×-≡-snd;
                                  unmatch+-≡-fst; unmatch+-≡-snd;
                                  unmatch⇒; unmatch×; unmatch+;
                                  _⇒ₛ_; _×ₛ_; _+ₛ_; ∀·ₛ;
                                  fst×ₛ'; snd×ₛ; fst+ₛ'; snd+ₛ';
                                  dom⇒ₛ; cod⇒ₛ; body∀ₛ; match⇒ₛ; match×ₛ; match+ₛ; match∀ₛ)
open import Core.Assms.Lift using (shift-unshiftΓ; hdₛ; tlₛ; unshiftΓₛ; cons-decompₛ)
open import Relation.Binary.PropositionalEquality using (sym; subst; cong)
open import Semantics.Statics
open import Slicing.Synthesis.Synthesis using (SynSlice_◂_; _⇑_∈_⊒_; MinSynSlice_◂_; _↓s; _↓γ; _↓γₛ; _↓σ; _↓σₛ; _↓σ⊑; _↓γ⊑; _↓ϕ; _↓ϕₛ)
import Slicing.Synthesis.Synthesis as SS
open import Semantics.Graduality using (static-gradual-syn; static-gradual-ana; static-gradual-ana-cls)
open import Slicing.Synthesis.SynSliceCalc using (_⊢_◂_↦_⊣_)
import Slicing.Synthesis.SynSliceCalc as SSC
open import Slicing.Analysis.Analysis

module Slicing.Analysis.AnaSliceCalc where

-- Mutually-recursive minimal analysis slice calculi.
--
-- MinAna covers slices of synthesising contexts (outer synPos τ_p) where
-- the focus is in analysis mode. Cases are the s* classification rules.
--
-- MinAnaPos covers slices of analysis-position contexts (outer anaPos τ_p),
-- the "stronger construct" that *also* tracks a minimal outer-analysis
-- type slice. Cases are the a* classification rules.
--
-- They are mutual because:
--   * minS∘₂ has an inner classification at anaPos (the argument's
--     surrounding context), so it recurses on MinAnaPos.
--   * minASub and minAdef₁ have an inner classification at synPos,
--     so they recurse on MinAna.
mutual
  -- Forward declarations: data MinAna, data MinAnaPos, extract, extract-pos
  -- are all in one mutual block. The data signatures are declared first
  -- (without `where`), then extract/extract-pos type signatures, then the
  -- constructors via `data ... where`, then the function bodies. This
  -- order is required so that minS∘₂'s constructor type can reference
  -- `extract-pos m` (which produces the AnaPosSlice whose `ana-υ_outer`
  -- field ties the function MinSynSlice's query to the argument's
  -- minimal outer slice).
  data MinAna : ∀ {n Γ₀ C n_f Γ τ τ_p}
              → (Cls : n ； Γ₀ ⊢ C at synPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]) → ⌊ τ ⌋ → Set
  data MinAnaPos : ∀ {n Γ₀ C n_f Γ τ τ_p}
                 → (Cls : n ； Γ₀ ⊢ C at anaPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]) → ⌊ τ ⌋ → Set

  extract-pos : ∀ {n Γ₀ C n_f Γ τ τ_p}
                  {Cls : n ； Γ₀ ⊢ C at anaPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]} {υ}
                → MinAnaPos Cls υ → AnaPosSlice Cls υ

  data MinAna where

    min□      : ∀ {n Γ₀ C n_f Γ τ τ_p} {Cls : n ； Γ₀ ⊢ C at synPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]}
              → MinAna Cls ⊥ₛ

    minSλ:    : ∀ {n Γ n_f Γ' τ₁ C τ₂ τ}
                  {wf : n ⊢wf τ₁}
                  {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at synPos τ₂ ▷ n_f ； Γ' [ ⇐mode τ ]}
              → {υ : ⌊ τ ⌋} → (υ₁ : ⌊ τ₁ ⌋)
              → MinAna Cls' υ
              → MinAna (sλ: wf Cls') υ

    minS∘₁    : ∀ {n Γ n_f Γ' C e τ τ₁ τ₂ τ_f}
                  {Cls' : n ； Γ ⊢ C at synPos τ ▷ n_f ； Γ' [ ⇐mode τ_f ]}
                  {eq : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                  {d₂ : n ； Γ ⊢ e ↤ τ₁}
              → {υ : ⌊ τ_f ⌋}
              → MinAna Cls' υ
              → MinAna (s∘₁ Cls' eq d₂) υ

    -- Application argument: outer synPos τ₂, inner C at anaPos τ₁.
    -- The argument's MinAnaPos `m` is the source of truth for the
    -- minimal outer-position slice (= ana-υ_outer (extract-pos m)).
    -- The function part is sliced via an exact MinSynSlice on D₁ queried
    -- at `unmatch⇒ eq (ana-υ_outer (extract-pos m)) ⊥ₛ`. Tying the
    -- query directly to extract-pos m removes the alignment friction in
    -- the s∘₂ extract clause: by minimality + exactness, fn.type's match
    -- dom equals (ana-υ_outer (extract-pos m)).↓.
    --
    -- The constructor also packages a lifted classification of ana-κ arg
    -- at anaPos (ana-υ_outer arg).↓ AT (ss ↓s ↓γ) (the function's γ slice).
    -- This is the s∘₂ extract's inner cls; storing it sidesteps the m
    -- alignment issue that arises from existential m₁ in the generic
    -- static-gradual-ana-cls. The algorithm constructing minS∘₂ produces
    -- this classification directly, since at construction-time it has the
    -- full Cls' available and can verify the structural alignment.
    minS∘₂    : ∀ {n Γ n_f Γ' e₁ C τ₀ τ₁ τ₂ τ}
                  {D₁ : n ； Γ ⊢ e₁ ↦ τ₀} {eq : τ₀ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                  {Cls' : n ； Γ ⊢ C at anaPos τ₁ ▷ n_f ； Γ' [ ⇐mode τ ]}
              → {υ : ⌊ τ ⌋}
              → (m : MinAnaPos Cls' υ)
              → (ss : MinSynSlice D₁ ◂ (unmatch⇒-min {τ₀} eq (ana-υ_outer (extract-pos m)) ⊥ₛ))
              → (focus : ⌊ τ ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n_f₁ ] ∃[ Γ_f₁ ]
                  (n ； (ss ↓s ↓γ) ⊢ (ana-κ (extract-pos m)) .↓
                     at anaPos ((dom⇒ₛ (SynSlice_◂_.type (ss ↓s)) eq) .↓)
                     ▷ n_f₁ ； Γ_f₁
                     [ ⇐mode (focus .↓) ])
              → MinAna (s∘₂ D₁ eq Cls') υ

    minS<>₁   : ∀ {n Γ n_f Γ' C τ_inner τ_fa σ τ}
                  {Cls' : n ； Γ ⊢ C at synPos τ_inner ▷ n_f ； Γ' [ ⇐mode τ ]}
                  {eq : τ_inner ⊔ ∀· □ ≡ ∀· τ_fa}
                  {wf : n ⊢wf σ}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (s<>₁ Cls' eq wf) υ

    minS&₁    : ∀ {n Γ n_f Γ' C e τ₁ τ₂ τ}
                  {Cls' : n ； Γ ⊢ C at synPos τ₁ ▷ n_f ； Γ' [ ⇐mode τ ]}
                  {d₂ : n ； Γ ⊢ e ↦ τ₂}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (s&₁ Cls' d₂) υ

    minS&₂    : ∀ {n Γ n_f Γ' C e τ₁ τ₂ τ}
                  {d₁ : n ； Γ ⊢ e ↦ τ₁}
                  {Cls' : n ； Γ ⊢ C at synPos τ₂ ▷ n_f ； Γ' [ ⇐mode τ ]}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (s&₂ d₁ Cls') υ

    -- Case in synthesis, focus on left branch. All external expressions
    -- (scrutinee e, sibling e') are sliced to □. The match equation
    -- becomes □ ⊔ □ + □ ≡ □ + □; body Cls' is lifted to (□ ∷ tlₛ); sibling
    -- d₂ becomes ↦□ ↤ □. Consistency: extract m's lifted type ~ □ holds
    -- trivially. The body lift is the constructor argument.
    minScase₁ : ∀ {n Γ n_f Γ' e C e' τ₀ τ₁ τ₂ τ₁' τ₂' τ}
                  {D : n ； Γ ⊢ e ↦ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at synPos τ₁' ▷ n_f ； Γ' [ ⇐mode τ ]}
                  {d₂ : n ； (τ₂ ∷ Γ) ⊢ e' ↦ τ₂'}
                  {con : τ₁' ~ τ₂'}
              → {υ : ⌊ τ ⌋}
              → (m : MinAna Cls' υ)
              → (typ : ⌊ τ₁' ⌋)
              → (typ ⊑ₛ (extract m .type))
              → (focus : ⌊ τ ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n-f' ] ∃[ Γ-f' ]
                  (n ； (□ ∷ (tlₛ (extract m .γ)) .↓) ⊢ (extract m .κ) .↓
                     at synPos (typ .↓) ▷ n-f' ； Γ-f'
                     [ ⇐mode (focus .↓) ])
              → MinAna (scase₁ D eq Cls' d₂ con) υ

    -- Case in synthesis, focus on right branch (symmetric).
    minScase₂ : ∀ {n Γ n_f Γ' e e' C τ₀ τ₁ τ₂ τ₁' τ₂' τ}
                  {D : n ； Γ ⊢ e ↦ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {d₁ : n ； (τ₁ ∷ Γ) ⊢ e' ↦ τ₁'}
                  {Cls' : n ； (τ₂ ∷ Γ) ⊢ C at synPos τ₂' ▷ n_f ； Γ' [ ⇐mode τ ]}
                  {con : τ₁' ~ τ₂'}
              → {υ : ⌊ τ ⌋}
              → (m : MinAna Cls' υ)
              → (typ : ⌊ τ₂' ⌋)
              → (typ ⊑ₛ (extract m .type))
              → (focus : ⌊ τ ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n-f' ] ∃[ Γ-f' ]
                  (n ； (□ ∷ (tlₛ (extract m .γ)) .↓) ⊢ (extract m .κ) .↓
                     at synPos (typ .↓) ▷ n-f' ； Γ-f'
                     [ ⇐mode (focus .↓) ])
              → MinAna (scase₂ D eq d₁ Cls' con) υ

    minSπ₁    : ∀ {n Γ n_f Γ' C τ_inner τ₁ τ₂ τ}
                  {Cls' : n ； Γ ⊢ C at synPos τ_inner ▷ n_f ； Γ' [ ⇐mode τ ]}
                  {eq : τ_inner ⊔ □ × □ ≡ τ₁ × τ₂}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (sπ₁ Cls' eq) υ

    minSπ₂    : ∀ {n Γ n_f Γ' C τ_inner τ₁ τ₂ τ}
                  {Cls' : n ； Γ ⊢ C at synPos τ_inner ▷ n_f ； Γ' [ ⇐mode τ ]}
                  {eq : τ_inner ⊔ □ × □ ≡ τ₁ × τ₂}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (sπ₂ Cls' eq) υ

    minSΛ     : ∀ {n Γ n_f Γ' C τ_body τ}
                  {Cls' : suc n ； shiftΓ (suc zero) Γ ⊢ C at synPos τ_body ▷ n_f ； Γ' [ ⇐mode τ ]}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (sΛ Cls') υ

    minSdef₁  : ∀ {n Γ n_f Γ' C e τ' τ_body τ}
                  {Cls' : n ； Γ ⊢ C at synPos τ' ▷ n_f ； Γ' [ ⇐mode τ_body ]}
                  {d₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ}
              → {υ : ⌊ τ_body ⌋}
              → MinAna Cls' υ
              → MinAna (sdef₁ Cls' d₂) υ

    -- Let body case. Slices def-e to □ (minimal) and packages a lifted body
    -- classification at (□ ∷ tlₛ extract m .γ). The algorithm produces the
    -- lifted classification via static-gradual-syn-cls (specialised to
    -- preserve mode — the body's analysis hole determines focus, which is
    -- preserved when the body's focus doesn't depend on the binder).
    minSdef₂  : ∀ {n Γ n_f Γ' e C τ' τ_body τ}
                  {D : n ； Γ ⊢ e ↦ τ'}
                  {Cls' : n ； (τ' ∷ Γ) ⊢ C at synPos τ_body ▷ n_f ； Γ' [ ⇐mode τ ]}
              → {υ : ⌊ τ ⌋}
              → (m : MinAna Cls' υ)
              → (typ : ⌊ τ_body ⌋)
              → (typ ⊑ₛ (extract m .type))
              → (focus : ⌊ τ ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n-f' ] ∃[ Γ-f' ]
                  (n ； (□ ∷ (tlₛ (extract m .γ)) .↓) ⊢ (extract m .κ) .↓
                     at synPos (typ .↓) ▷ n-f' ； Γ-f'
                     [ ⇐mode (focus .↓) ])
              → MinAna (sdef₂ D Cls') υ

  data MinAnaPos where

    min□Pos   : ∀ {n Γ₀ C n_f Γ τ τ_p} {Cls : n ； Γ₀ ⊢ C at anaPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]}
              → MinAnaPos Cls ⊥ₛ

    minA○     : ∀ {n Γ τ}
              → (υ : ⌊ τ ⌋)
              → MinAnaPos (a○ {n = n} {Γ = Γ} {τ = τ}) υ

    -- aSub: outer anaPos τ₀, inner at synPos τ' with τ₀ ~ τ'.
    -- Recurses on MinAna for the inner synPos sub-classification.
    minASub   : ∀ {n Γ n_f Γ' C τ₀ τ' τ}
                  {Cls' : n ； Γ ⊢ C at synPos τ' ▷ n_f ； Γ' [ ⇐mode τ ]}
                  {con : τ₀ ~ τ'}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAnaPos (aSub {τ = τ₀} Cls' con) υ

    -- Annotated lambda in analysis (tightened, mirrors minSdef₂/minAcase).
    -- The asymmetric consistency τ ~ τ₁⇒□ and match τ ⊔ τ₁⇒□ ≡ τ₁'⇒τ₂ don't
    -- admit a clean unmatch-style construction at the slice level, so the
    -- algorithm pre-packages outer-υ together with the lifted consistency
    -- and match equation. The match's first component is hdₛ (extract-pos
    -- m .ana-γ) (the binder slice) and the second is ana-υ_outer (extract
    -- -pos m) (the body's analysis target slice).
    minAλ:    : ∀ {n Γ n_f Γ' C τ τ₁ τ₁' τ₂ τ'}
                  {c : τ ~ τ₁ ⇒ □} {eq : τ ⊔ τ₁ ⇒ □ ≡ τ₁' ⇒ τ₂}
                  {wf : n ⊢wf τ₁}
                  {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ n_f ； Γ' [ ⇐mode τ' ]}
              → {υ : ⌊ τ' ⌋}
              → (m : MinAnaPos Cls' υ)
              → (outer-υ : ⌊ τ ⌋)
              → (outer-υ .↓ ~ (hdₛ (ana-γ (extract-pos m))) .↓ ⇒ □)
              → (outer-υ .↓ ⊔ (hdₛ (ana-γ (extract-pos m))) .↓ ⇒ □
                   ≡ (hdₛ (ana-γ (extract-pos m))) .↓ ⇒ (ana-υ_outer (extract-pos m)) .↓)
              → MinAnaPos (aλ: c eq wf Cls') υ

    minAλ⇒    : ∀ {n Γ n_f Γ' C τ τ₁ τ₂ τ'}
                  {eq : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                  {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ n_f ； Γ' [ ⇐mode τ' ]}
              → {υ : ⌊ τ' ⌋}
              → MinAnaPos Cls' υ
              → MinAnaPos (aλ⇒ {τ = τ} eq Cls') υ

    minA&₁    : ∀ {n Γ n_f Γ' C e τ τ₁ τ₂ τf}
                  {eq : τ ⊔ □ × □ ≡ τ₁ × τ₂}
                  {Cls' : n ； Γ ⊢ C at anaPos τ₁ ▷ n_f ； Γ' [ ⇐mode τf ]}
                  {d₂ : n ； Γ ⊢ e ↤ τ₂}
              → {υ : ⌊ τf ⌋}
              → MinAnaPos Cls' υ
              → MinAnaPos (a&₁ {τ = τ} eq Cls' d₂) υ

    minA&₂    : ∀ {n Γ n_f Γ' C e τ τ₁ τ₂ τ'}
                  {eq : τ ⊔ □ × □ ≡ τ₁ × τ₂}
                  {d₁ : n ； Γ ⊢ e ↤ τ₁}
                  {Cls' : n ； Γ ⊢ C at anaPos τ₂ ▷ n_f ； Γ' [ ⇐mode τ' ]}
              → {υ : ⌊ τ' ⌋}
              → MinAnaPos Cls' υ
              → MinAnaPos (a&₂ {τ = τ} eq d₁ Cls') υ

    minAι₁    : ∀ {n Γ n_f Γ' C τ τ₁ τ₂ τ'}
                  {eq : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {Cls' : n ； Γ ⊢ C at anaPos τ₁ ▷ n_f ； Γ' [ ⇐mode τ' ]}
              → {υ : ⌊ τ' ⌋}
              → MinAnaPos Cls' υ
              → MinAnaPos (aι₁ {τ = τ} eq Cls') υ

    minAι₂    : ∀ {n Γ n_f Γ' C τ τ₁ τ₂ τ'}
                  {eq : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {Cls' : n ； Γ ⊢ C at anaPos τ₂ ▷ n_f ； Γ' [ ⇐mode τ' ]}
              → {υ : ⌊ τ' ⌋}
              → MinAnaPos Cls' υ
              → MinAnaPos (aι₂ {τ = τ} eq Cls') υ

    -- Case in analysis, focus on left branch. Mirrors minScase₁: slices
    -- scrutinee e and sibling e' to □, packages a lifted body Cls' at
    -- (□ ∷ tlₛ ana-γ) so minimality holds.
    -- Case in analysis, focus on left branch. The lifted Cls' is at an
    -- existential mode ⇐mode focus.↓ (smaller than the algorithm's natural
    -- focus due to static-gradual-ana-cls's mode-⊑ output). The focus and
    -- focus⊒ are constructor arguments (mirroring minS∘₂).
    minAcase₁ : ∀ {n Γ n_f Γ' e C e' τ τ₀ τ₁ τ₂ τ'}
                  {D : n ； Γ ⊢ e ↦ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {Cls' : n ； (τ₁ ∷ Γ) ⊢ C at anaPos τ ▷ n_f ； Γ' [ ⇐mode τ' ]}
                  {d₂ : n ； (τ₂ ∷ Γ) ⊢ e' ↤ τ}
              → {υ : ⌊ τ' ⌋}
              → (m : MinAnaPos Cls' υ)
              → (focus : ⌊ τ' ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n-f' ] ∃[ Γ-f' ]
                  (n ； (□ ∷ (tlₛ (ana-γ (extract-pos m))) .↓) ⊢ (ana-κ (extract-pos m)) .↓
                     at anaPos ((ana-υ_outer (extract-pos m)) .↓) ▷ n-f' ； Γ-f'
                     [ ⇐mode (focus .↓) ])
              → MinAnaPos (acase₁ D eq Cls' d₂) υ

    -- Case in analysis, focus on right branch (symmetric).
    minAcase₂ : ∀ {n Γ n_f Γ' e e' C τ τ₀ τ₁ τ₂ τ'}
                  {D : n ； Γ ⊢ e ↦ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {d₁ : n ； (τ₁ ∷ Γ) ⊢ e' ↤ τ}
                  {Cls' : n ； (τ₂ ∷ Γ) ⊢ C at anaPos τ ▷ n_f ； Γ' [ ⇐mode τ' ]}
              → {υ : ⌊ τ' ⌋}
              → (m : MinAnaPos Cls' υ)
              → (focus : ⌊ τ' ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n-f' ] ∃[ Γ-f' ]
                  (n ； (□ ∷ (tlₛ (ana-γ (extract-pos m))) .↓) ⊢ (ana-κ (extract-pos m)) .↓
                     at anaPos ((ana-υ_outer (extract-pos m)) .↓) ▷ n-f' ； Γ-f'
                     [ ⇐mode (focus .↓) ])
              → MinAnaPos (acase₂ D eq d₁ Cls') υ

    -- adef₁: outer anaPos τ, inner at synPos τ'. Recurses on MinAna.
    minAdef₁  : ∀ {n Γ n_f Γ' C e τ τ' τ''}
                  {Cls' : n ； Γ ⊢ C at synPos τ' ▷ n_f ； Γ' [ ⇐mode τ'' ]}
                  {d₂ : n ； (τ' ∷ Γ) ⊢ e ↤ τ}
              → {υ : ⌊ τ'' ⌋}
              → MinAna Cls' υ
              → MinAnaPos (adef₁ Cls' d₂) υ

    -- Let-binding in analysis, focus on body (tightened, mirrors minSdef₂).
    -- Packages a lifted derivation of D at (tlₛ extract-pos m .ana-γ) whose
    -- syn type equals (hdₛ extract-pos m .ana-γ).
    minAdef₂  : ∀ {n Γ n_f Γ' e C τ τ' τ''}
                  {D : n ； Γ ⊢ e ↦ τ'}
                  {Cls' : n ； (τ' ∷ Γ) ⊢ C at anaPos τ ▷ n_f ； Γ' [ ⇐mode τ'' ]}
              → {υ : ⌊ τ'' ⌋}
              → (m : MinAnaPos Cls' υ)
              → (focus : ⌊ τ'' ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n-f' ] ∃[ Γ-f' ]
                  (n ； (□ ∷ (tlₛ (ana-γ (extract-pos m))) .↓) ⊢ (ana-κ (extract-pos m)) .↓
                     at anaPos ((ana-υ_outer (extract-pos m)) .↓) ▷ n-f' ； Γ-f'
                     [ ⇐mode (focus .↓) ])
              → MinAnaPos (adef₂ D Cls') υ

-- Mutual extract proof.
--
-- AnaSlice (synPos outer) and AnaPosSlice (anaPos outer) are extracted
-- mutually, mirroring the mutual structure of MinAna and MinAnaPos.
--
-- Proven cases:
--   * min□ → ⊥-ana, min□Pos → ⊥-ana-pos.
--   * minA○ → AnaPosSlice with υ_outer = υ (a○ couples outer = focus).
--   * minASub → recurse synPos via extract; lift via aSub with ~?₂
--     (giving outer υ_outer = ⊥ₛ).
--
-- Inductive cases left as holes; each requires a slice-level helper
-- (binder head-swap, eq-lifting via match⇒ₛ/match×ₛ/match+ₛ, or
-- BoundedMinSynSlice extraction for siblings).
--
-- Note: extract and extract-pos are part of the SAME `mutual` block above
-- (the same one that contains data MinAna and MinAnaPos), since
-- minS∘₂'s constructor type references `extract-pos m` directly.
  extract : ∀ {n Γ₀ C n_f Γ τ τ_p}
              {Cls : n ； Γ₀ ⊢ C at synPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]} {υ}
            → MinAna Cls υ → AnaSlice Cls υ

  -- min□: trivial bottom slice.
  extract min□ = ⊥-ana

  -- The 12 outer-synPos inductive cases (minSλ:, minS∘₁, minS∘₂,
  -- minS<>₁, minS&₁, minS&₂, minScase₁, minScase₂, minSπ₁, minSπ₂,
  -- minSΛ, minSdef₁, minSdef₂) are left as holes. minS∘₂ in particular
  -- recurses on extract-pos to obtain υ₁, then uses the calc-provided
  -- function evidence to build the outer AnaSlice.
  -- Annotated lambda in synthesis: outer sλ: wf Cls' at synPos (τ₁ ⇒ τ₂),
  -- inner Cls' at synPos τ₂ in extended context (τ₁ ∷ Γ). Destructure
  -- inner.γ via the ⊑∷ pattern to project out the binder slice (hd) and
  -- the outer-context slice (tl). The outer type slice is hd ⇒ₛ inner.type.
  extract (minSλ: {n = n} {wf = wf} υ₁ m) =
    let inner = extract m
        hd-slice = hdₛ (inner .γ)
        tl-slice = tlₛ (inner .γ)
        hd⊑ = hd-slice .proof
        n_f , Γ_f , inner-cls = inner .valid
        inner-cls-decomp =
          subst (λ x → n ； x ⊢ inner .κ .↓ at synPos (inner .type .↓)
                          ▷ n_f ； Γ_f [ ⇐mode (inner .focus .↓) ])
                (cons-decompₛ (inner .γ)) inner-cls
    in record
         { κ      = (λ: _ ⇒ inner .κ .↓) isSlice ⊑λ hd⊑ (inner .κ .proof)
         ; γ      = tl-slice
         ; type   = hd-slice ⇒ₛ inner .type
         ; focus  = inner .focus
         ; focus⊒ = inner .focus⊒
         ; valid  = _ , _ , sλ: (wf-⊑ wf hd⊑) inner-cls-decomp
         }
  -- Application focus on function: outer s∘₁ Cls' eq d₂. Argument exp
  -- slice is □e (minimal); discharges via ↤Sub ↦□ ~?₁.
  extract (minS∘₁ {eq = eq} m) =
    let inner = extract m
        _ , _ , inner-cls = inner .valid
        ψ = AnaSlice.type inner
    in record
         { κ      = ((inner .κ .↓) ∘₁ □) isSlice
                      ⊑∘₁ (inner .κ .proof) ⊑□
         ; γ      = inner .γ
         ; type   = cod⇒ₛ ψ eq
         ; focus  = inner .focus
         ; focus⊒ = inner .focus⊒
         ; valid  = _ , _ , s∘₁ inner-cls (match⇒ₛ ψ eq) (↤Sub ↦□ ~?₁)
         }
  -- Argument case (focus on argument): outer s∘₂ D₁ eq Cls'.
  -- The constructor packages a lifted classification `cls-lifted` of
  -- ana-κ arg at anaPos (dom⇒ₛ ψ eq).↓ AT (ss ↓s ↓γ) with focus
  -- [⇐mode (focus.↓)] for any focus ⊒ υ. The AnaSlice's focus field
  -- takes this potentially-larger focus, reflecting that the function
  -- application can enforce a larger focus query than the user's υ.
  extract (minS∘₂ {τ₀ = τ₀} {D₁ = D₁} {eq = eq}
                  {Cls' = Cls'} {υ = υ} m ss focus focus⊒ (n_f₁ , Γ_f₁ , cls-lifted)) =
    let arg        = extract-pos m
        fn         = ss ↓s
        ψ          = SynSlice_◂_.type fn
    in record
         { κ      = ((fn ↓σ) ∘₂ (ana-κ arg .↓)) isSlice
                      ⊑∘₂ (fn ↓σ⊑) (ana-κ arg .proof)
         ; γ      = fn ↓γₛ
         ; type   = cod⇒ₛ ψ eq
         ; focus  = focus
         ; focus⊒ = focus⊒
         ; valid  = _ , _ , s∘₂ (SynSlice_◂_.syn fn) (match⇒ₛ ψ eq) cls-lifted
         }
  -- Type application: outer s<>₁ Cls' eq wf. Inner at synPos τ_inner; we
  -- compute the lifted body via body∀ₛ. Outer type slice is the substituted
  -- body via sub-⊑ at zero. σ-slice in the lifted ctx is □ (minimal); wf
  -- discharges via wf□.
  extract (minS<>₁ {eq = eq} {wf = wf} m) =
    let inner = extract m
        _ , _ , inner-cls = inner .valid
        ψ = inner .type
        body = body∀ₛ ψ eq
    in record
         { κ      = ((inner .κ .↓) < □ >₁) isSlice
                      ⊑<>₁ (inner .κ .proof) ⊑□
         ; γ      = inner .γ
         ; type   = ↑ (sub-⊑ zero ⊑□ (body .proof))
         ; focus  = inner .focus
         ; focus⊒ = inner .focus⊒
         ; valid  = _ , _ , s<>₁ inner-cls (match∀ₛ ψ eq) wf□
         }
  -- Pair, focus on left: outer s&₁ Cls' d₂. Sibling exp = □e (minimal);
  -- sibling synthesises □ via ↦□. Outer type slice is product of inner.type
  -- and ⊥ₛ (the sibling's syn-type slice).
  extract (minS&₁ m) =
    let inner = extract m
        _ , _ , inner-cls = inner .valid
    in record
         { κ      = ((inner .κ .↓) &₁ □) isSlice
                      ⊑&₁ (inner .κ .proof) ⊑□
         ; γ      = inner .γ
         ; type   = AnaSlice.type inner ×ₛ ⊥ₛ
         ; focus  = inner .focus
         ; focus⊒ = inner .focus⊒
         ; valid  = _ , _ , s&₁ inner-cls ↦□
         }
  extract (minS&₂ m) =
    let inner = extract m
        _ , _ , inner-cls = inner .valid
    in record
         { κ      = (□ &₂ (inner .κ .↓)) isSlice
                      ⊑&₂ ⊑□ (inner .κ .proof)
         ; γ      = inner .γ
         ; type   = ⊥ₛ ×ₛ AnaSlice.type inner
         ; focus  = inner .focus
         ; focus⊒ = inner .focus⊒
         ; valid  = _ , _ , s&₂ ↦□ inner-cls
         }
  -- Case (synthesis, focus left, tightened): outer scase₁ D eq Cls' d₂ con.
  -- Destructure inner.γ for binder (hd) and outer-context (tl) slices, then
  -- plug pre-lifted D, eq, d₂ into the scase₁ rule. Outer type is the join
  -- inner.type ⊔~ₛ τ₂'-slice using the lifted consistency.
  extract (minScase₁ {n = n} {con = con} m typ _ focus focus⊒ (n-f' , Γ-f' , Cls-lifted)) =
    let inner = extract m
    in record
         { κ      = (case □ of (inner .κ .↓) ·₁ □) isSlice
                      ⊑case₁ ⊑□ (inner .κ .proof) ⊑□
         ; γ      = tlₛ (inner .γ)
         ; type   = _⊔~ₛ_ typ ⊥ₛ {c = con}
         ; focus  = focus
         ; focus⊒ = focus⊒
         ; valid  = n-f' , Γ-f' , scase₁ ↦□ refl Cls-lifted ↦□ ~?₁
         }
  -- Case (synthesis, focus right, tightened): symmetric.
  extract (minScase₂ {n = n} {con = con} m typ _ focus focus⊒ (n-f' , Γ-f' , Cls-lifted)) =
    let inner = extract m
    in record
         { κ      = (case □ of₂ □ · (inner .κ .↓)) isSlice
                      ⊑case₂ ⊑□ ⊑□ (inner .κ .proof)
         ; γ      = tlₛ (inner .γ)
         ; type   = _⊔~ₛ_ ⊥ₛ typ {c = con}
         ; focus  = focus
         ; focus⊒ = focus⊒
         ; valid  = n-f' , Γ-f' , scase₂ ↦□ refl ↦□ Cls-lifted ~?₂
         }
  -- π₁ C: outer sπ₁ Cls' eq. Inner at synPos τ_inner; outer at synPos τ₁
  -- (the first projection of the matched product). Outer type slice is
  -- fst×ₛ' inner.type eq.
  extract (minSπ₁ {eq = eq} m) =
    let inner = extract m
        _ , _ , inner-cls = inner .valid
        ψ = AnaSlice.type inner
    in record
         { κ      = (π₁ (inner .κ .↓)) isSlice ⊑π₁ (inner .κ .proof)
         ; γ      = inner .γ
         ; type   = fst×ₛ' ψ eq
         ; focus  = inner .focus
         ; focus⊒ = inner .focus⊒
         ; valid  = _ , _ , sπ₁ inner-cls (match×ₛ ψ eq)
         }
  extract (minSπ₂ {eq = eq} m) =
    let inner = extract m
        _ , _ , inner-cls = inner .valid
        ψ = AnaSlice.type inner
    in record
         { κ      = (π₂ (inner .κ .↓)) isSlice ⊑π₂ (inner .κ .proof)
         ; γ      = inner .γ
         ; type   = snd×ₛ ψ eq
         ; focus  = inner .focus
         ; focus⊒ = inner .focus⊒
         ; valid  = _ , _ , sπ₂ inner-cls (match×ₛ ψ eq)
         }
  -- Type abstraction: outer sΛ Cls'. Inner at (suc n; shiftΓ (suc zero) Γ);
  -- outer at (n; Γ). Project outer.γ via unshiftΓₛ; use shift-unshiftΓ to
  -- bridge the propositional equality shiftΓ (suc zero) (unshiftΓ ... γ) ≡ γ.
  extract (minSΛ {n = n} {υ = υ} m) =
    let inner = extract m
        γ-eq = shift-unshiftΓ (inner .γ .↓) (inner .γ .proof)
        n_f , Γ_f , inner-cls = inner .valid
        inner-cls' = subst (λ x → suc n ； x ⊢ (inner .κ .↓) at synPos (inner .type .↓)
                                                 ▷ n_f ； Γ_f [ ⇐mode (inner .focus .↓) ])
                           (sym γ-eq) inner-cls
    in record
         { κ      = (Λ (inner .κ .↓)) isSlice ⊑Λ (inner .κ .proof)
         ; γ      = unshiftΓₛ (inner .γ)
         ; type   = ∀·ₛ (inner .type)
         ; focus  = inner .focus
         ; focus⊒ = inner .focus⊒
         ; valid  = n_f , Γ_f , sΛ inner-cls'
         }
  -- def C ⊢₁ e: outer sdef₁ Cls' d₂. Lift d₂ from (τ' ∷ Γ) down to
  -- (inner.type ∷ inner.γ) via static-gradual-syn. Outer type slice is
  -- the lifted body's synthesised type. Body exp slice is □e (minimal);
  -- body synthesises □ via ↦□. Outer type slice is ⊥ₛ (= □).
  extract (minSdef₁ m) =
    let inner = extract m
        _ , _ , inner-cls = inner .valid
    in record
         { κ      = (def (inner .κ .↓) ⊢₁ □) isSlice
                      ⊑def₁ (inner .κ .proof) ⊑□
         ; γ      = inner .γ
         ; type   = ⊥ₛ
         ; focus  = inner .focus
         ; focus⊒ = inner .focus⊒
         ; valid  = _ , _ , sdef₁ inner-cls ↦□
         }
  -- Let-binding focus on body (tightened constructor): outer sdef₂ D Cls'.
  -- The constructor packages a lifted D derivation at the outer.γ with syn
  -- type matching the binder slice. Destructure inner.γ to split off the
  -- binder slice (hd) and outer-context slice (tl); then sdef₂ plugs in
  -- directly via the lifted D and inner-cls (which is at (hd ∷ tl)).
  extract (minSdef₂ {n = n} m typ _ focus focus⊒ (n-f' , Γ-f' , Cls-lifted)) =
    let inner = extract m
    in record
         { κ      = (def □ ⊢₂ (inner .κ .↓)) isSlice
                      ⊑def₂ ⊑□ (inner .κ .proof)
         ; γ      = tlₛ (inner .γ)
         ; type   = typ
         ; focus  = focus
         ; focus⊒ = focus⊒
         ; valid  = n-f' , Γ-f' , sdef₂ ↦□ Cls-lifted
         }

  -- min□Pos: trivial bottom slice for outer anaPos.
  extract-pos min□Pos = ⊥-ana-pos

  -- minA○: outer anaPos τ with a○ coupling outer = focus = τ. Pick
  -- υ_outer = υ; classification is a○ at υ.↓. γ = ⊥ₛ (minimum); κ = ⊥ₛ
  -- (⌊○⌋ is a singleton, so ⊤ₛ ≡ ⊥ₛ here, but ⊥ₛ states the intent).
  extract-pos (minA○ {τ = τ} υ) = record
    { κ       = ⊥ₛ
    ; γ       = ⊥ₛ
    ; υ_outer = υ
    ; focus   = υ
    ; focus⊒  = ⊑ₛ.refl {A = Typ} {x = υ}
    ; valid   = _ , _ , a○
    }

  -- minASub: outer aSub at anaPos τ₀, inner Cls' at synPos τ'.
  -- Recurse via extract (synPos) on m. Pick outer υ_outer = ⊥ₛ so the
  -- consistency obligation is `□ ~ τ'_slice.↓` discharged by ~?₂.
  extract-pos (minASub m) =
    let s = extract m
        _ , _ , inner-cls = s .valid
    in record
         { κ       = s .κ
         ; γ       = s .γ
         ; υ_outer = ⊥ₛ
         ; focus   = s .focus
         ; focus⊒  = s .focus⊒
         ; valid   = _ , _ , aSub inner-cls ~?₂
         }

  -- The remaining outer-anaPos inductive cases. Each recurses on
  -- extract-pos (minAλ:, minAλ⇒, minA&₁, minA&₂, minAι₁, minAι₂,
  -- minAcase₁, minAcase₂, minAdef₂) or extract (minAdef₁'s synPos
  -- inner). All need slice-level eq lifting and binder head-swap.
  -- Annotated lambda in analysis (tightened): outer aλ: c eq wf Cls'.
  -- Destructure inner.γ for binder (hd) and outer-context (tl) slices, then
  -- aλ: rule plugs in directly with the pre-packaged c-lifted/eq-lifted.
  extract-pos {n = n} (minAλ: {wf = wf} m outer-υ c-lifted eq-lifted) =
    let inner = extract-pos m
        hd⊑ = hdₛ (ana-γ inner) .proof
        n_f , Γ_f , inner-cls = ana-valid inner
        inner-cls-decomp =
          subst (λ x → n ； x ⊢ (ana-κ inner .↓) at anaPos (ana-υ_outer inner .↓)
                          ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ])
                (cons-decompₛ (ana-γ inner)) inner-cls
    in record
         { κ       = (λ: _ ⇒ (ana-κ inner .↓)) isSlice ⊑λ hd⊑ (ana-κ inner .proof)
         ; γ       = tlₛ (ana-γ inner)
         ; υ_outer = outer-υ
         ; focus   = ana-focus inner
         ; focus⊒  = ana-focus⊒ inner
         ; valid   = _ , _ , aλ: c-lifted eq-lifted (wf-⊑ wf hd⊑) inner-cls-decomp
         }
  -- Unannotated lambda in analysis: outer aλ⇒ eq Cls'. Inner Cls' at
  -- anaPos τ₂ in (τ₁ ∷ Γ); destructure inner.γ to extract the binder
  -- slice (hd) and outer-context slice (tl). outer.υ_outer is built via
  -- unmatch⇒ with the binder/body slices; bridge via unmatch⇒-≡-fst/snd.
  extract-pos {n = n} {υ = υ} (minAλ⇒ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} m) =
    let inner = extract-pos m
        hd : ⌊ τ₁ ⌋
        hd = hdₛ (ana-γ inner)
        tl : ⌊ _ ⌋
        tl = tlₛ (ana-γ inner)
        υ-cod : ⌊ τ₂ ⌋
        υ-cod = ana-υ_outer inner
        outer-υ : ⌊ τ ⌋
        outer-υ = unmatch⇒ eq hd υ-cod
        match-eq : outer-υ .↓ ⊔ □ ⇒ □ ≡ (dom⇒ₛ outer-υ eq) .↓ ⇒ (cod⇒ₛ outer-υ eq) .↓
        match-eq = match⇒ₛ outer-υ eq
        hd≡dom : hd .↓ ≡ (dom⇒ₛ outer-υ eq) .↓
        hd≡dom = unmatch⇒-≡-fst {τ = τ} eq hd υ-cod match-eq
        υ-cod≡cod : υ-cod .↓ ≡ (cod⇒ₛ outer-υ eq) .↓
        υ-cod≡cod = unmatch⇒-≡-snd {τ = τ} eq hd υ-cod match-eq
        n_f , Γ_f , inner-cls = ana-valid inner
        inner-cls-decomp =
          subst (λ x → n ； x ⊢ (ana-κ inner .↓) at anaPos (ana-υ_outer inner .↓)
                          ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ])
                (cons-decompₛ (ana-γ inner)) inner-cls
        inner-cls-1 : n ； (hd .↓ ∷ tl .↓) ⊢ (ana-κ inner .↓)
                            at anaPos ((cod⇒ₛ outer-υ eq) .↓) ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ]
        inner-cls-1 = subst (λ x → n ； (hd .↓ ∷ tl .↓) ⊢ (ana-κ inner .↓)
                                          at anaPos x ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ])
                            υ-cod≡cod inner-cls-decomp
        inner-cls-2 : n ； ((dom⇒ₛ outer-υ eq) .↓ ∷ tl .↓) ⊢ (ana-κ inner .↓)
                            at anaPos ((cod⇒ₛ outer-υ eq) .↓) ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ]
        inner-cls-2 = subst (λ x → n ； (x ∷ tl .↓) ⊢ (ana-κ inner .↓)
                                          at anaPos ((cod⇒ₛ outer-υ eq) .↓)
                                          ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ])
                            hd≡dom inner-cls-1
    in record
         { κ       = (λ⇒ (ana-κ inner .↓)) isSlice ⊑λu (ana-κ inner .proof)
         ; γ       = tl
         ; υ_outer = outer-υ
         ; focus   = ana-focus inner
         ; focus⊒  = ana-focus⊒ inner
         ; valid   = n_f , Γ_f , aλ⇒ match-eq inner-cls-2
         }
  -- Pair in analysis, focus on left: outer a&₁ eq Cls' d₂. Sibling d₂ at
  -- full Γ; lift to inner.γ via static-gradual-ana. Outer.υ_outer captures
  -- inner.υ_outer at the left × position with ⊥ on the right; bridge
  -- inner-cls's anaPos type via unmatch×-≡-fst.
  extract-pos {n = n} {υ = υ} (minA&₁ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} {d₂ = d₂} m) =
    let inner = extract-pos m
        υ-fst : ⌊ τ₁ ⌋
        υ-fst = ana-υ_outer inner
        ⊥₂ : ⌊ τ₂ ⌋
        ⊥₂ = ⊥ₛ
        n_f , Γ_f , inner-cls = ana-valid inner
        outer-υ : ⌊ τ ⌋
        outer-υ = unmatch× eq υ-fst ⊥₂
        match-eq : outer-υ .↓ ⊔ □ × □ ≡ (fst×ₛ' outer-υ eq) .↓ × (snd×ₛ outer-υ eq) .↓
        match-eq = match×ₛ outer-υ eq
        υ-fst≡fst : υ-fst .↓ ≡ (fst×ₛ' outer-υ eq) .↓
        υ-fst≡fst = unmatch×-≡-fst {τ = τ} eq υ-fst ⊥₂ match-eq
        inner-cls' : n ； (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                            at anaPos ((fst×ₛ' outer-υ eq) .↓) ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ]
        inner-cls' = subst (λ x → n ； (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                                          at anaPos x ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ])
                           υ-fst≡fst inner-cls
        d₂' = static-gradual-ana (ana-γ inner .proof) (⊑.refl {A = Exp})
                (snd×ₛ outer-υ eq .proof) d₂
    in record
         { κ       = ((ana-κ inner .↓) &₁ _) isSlice
                       ⊑&₁ (ana-κ inner .proof) (⊑.refl {A = Exp})
         ; γ       = ana-γ inner
         ; υ_outer = outer-υ
         ; focus   = ana-focus inner
         ; focus⊒  = ana-focus⊒ inner
         ; valid   = n_f , Γ_f , a&₁ match-eq inner-cls' d₂'
         }
  -- Pair in analysis, focus on right: symmetric to minA&₁.
  extract-pos {n = n} {υ = υ} (minA&₂ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} {d₁ = d₁} m) =
    let inner = extract-pos m
        υ-snd : ⌊ τ₂ ⌋
        υ-snd = ana-υ_outer inner
        ⊥₁ : ⌊ τ₁ ⌋
        ⊥₁ = ⊥ₛ
        n_f , Γ_f , inner-cls = ana-valid inner
        outer-υ : ⌊ τ ⌋
        outer-υ = unmatch× eq ⊥₁ υ-snd
        match-eq : outer-υ .↓ ⊔ □ × □ ≡ (fst×ₛ' outer-υ eq) .↓ × (snd×ₛ outer-υ eq) .↓
        match-eq = match×ₛ outer-υ eq
        υ-snd≡snd : υ-snd .↓ ≡ (snd×ₛ outer-υ eq) .↓
        υ-snd≡snd = unmatch×-≡-snd {τ = τ} eq ⊥₁ υ-snd match-eq
        inner-cls' : n ； (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                            at anaPos ((snd×ₛ outer-υ eq) .↓) ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ]
        inner-cls' = subst (λ x → n ； (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                                          at anaPos x ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ])
                           υ-snd≡snd inner-cls
        d₁' = static-gradual-ana (ana-γ inner .proof) (⊑.refl {A = Exp})
                (fst×ₛ' outer-υ eq .proof) d₁
    in record
         { κ       = (_ &₂ (ana-κ inner .↓)) isSlice
                       ⊑&₂ (⊑.refl {A = Exp}) (ana-κ inner .proof)
         ; γ       = ana-γ inner
         ; υ_outer = outer-υ
         ; focus   = ana-focus inner
         ; focus⊒  = ana-focus⊒ inner
         ; valid   = n_f , Γ_f , a&₂ match-eq d₁' inner-cls'
         }
  -- ι₁ injection in analysis: outer aι₁ eq Cls'. Construct outer.υ_outer
  -- as unmatch+ eq υ-fst ⊥ₛ (capture inner's υ at the left position, ⊥ on
  -- right). Use unmatch+-≡-fst to bridge inner-cls's anaPos type to the
  -- match's fst component.
  extract-pos {n = n} {υ = υ} (minAι₁ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} m) =
    let inner = extract-pos m
        υ-fst : ⌊ τ₁ ⌋
        υ-fst = ana-υ_outer inner
        ⊥₂ : ⌊ τ₂ ⌋
        ⊥₂ = ⊥ₛ
        n_f , Γ_f , inner-cls = ana-valid inner
        outer-υ : ⌊ τ ⌋
        outer-υ = unmatch+ eq υ-fst ⊥₂
        match-eq : outer-υ .↓ ⊔ □ + □ ≡ (fst+ₛ' outer-υ eq) .↓ + (snd+ₛ' outer-υ eq) .↓
        match-eq = match+ₛ outer-υ eq
        υ-fst≡fst : υ-fst .↓ ≡ (fst+ₛ' outer-υ eq) .↓
        υ-fst≡fst = unmatch+-≡-fst {τ = τ} eq υ-fst ⊥₂ match-eq
        inner-cls' : n ； (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                            at anaPos ((fst+ₛ' outer-υ eq) .↓) ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ]
        inner-cls' = subst (λ x → n ； (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                                          at anaPos x ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ])
                           υ-fst≡fst inner-cls
    in record
         { κ       = (ι₁ (ana-κ inner .↓)) isSlice ⊑ι₁ (ana-κ inner .proof)
         ; γ       = ana-γ inner
         ; υ_outer = outer-υ
         ; focus   = ana-focus inner
         ; focus⊒  = ana-focus⊒ inner
         ; valid   = n_f , Γ_f , aι₁ match-eq inner-cls'
         }
  -- ι₂ injection in analysis: symmetric to minAι₁ (right component).
  extract-pos {n = n} {υ = υ} (minAι₂ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} m) =
    let inner = extract-pos m
        υ-snd : ⌊ τ₂ ⌋
        υ-snd = ana-υ_outer inner
        ⊥₁ : ⌊ τ₁ ⌋
        ⊥₁ = ⊥ₛ
        n_f , Γ_f , inner-cls = ana-valid inner
        outer-υ : ⌊ τ ⌋
        outer-υ = unmatch+ eq ⊥₁ υ-snd
        match-eq : outer-υ .↓ ⊔ □ + □ ≡ (fst+ₛ' outer-υ eq) .↓ + (snd+ₛ' outer-υ eq) .↓
        match-eq = match+ₛ outer-υ eq
        υ-snd≡snd : υ-snd .↓ ≡ (snd+ₛ' outer-υ eq) .↓
        υ-snd≡snd = unmatch+-≡-snd {τ = τ} eq ⊥₁ υ-snd match-eq
        inner-cls' : n ； (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                            at anaPos ((snd+ₛ' outer-υ eq) .↓) ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ]
        inner-cls' = subst (λ x → n ； (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                                          at anaPos x ▷ n_f ； Γ_f [ ⇐mode (ana-focus inner .↓) ])
                           υ-snd≡snd inner-cls
    in record
         { κ       = (ι₂ (ana-κ inner .↓)) isSlice ⊑ι₂ (ana-κ inner .proof)
         ; γ       = ana-γ inner
         ; υ_outer = outer-υ
         ; focus   = ana-focus inner
         ; focus⊒  = ana-focus⊒ inner
         ; valid   = n_f , Γ_f , aι₂ match-eq inner-cls'
         }
  -- Case in analysis, focus on left (slice scrutinee/sibling to □).
  extract-pos (minAcase₁ m focus focus⊒ (n-f' , Γ-f' , Cls-lifted)) =
    let inner = extract-pos m
    in record
         { κ       = (case □ of (ana-κ inner .↓) ·₁ □) isSlice
                       ⊑case₁ ⊑□ (ana-κ inner .proof) ⊑□
         ; γ       = tlₛ (ana-γ inner)
         ; υ_outer = ana-υ_outer inner
         ; focus   = focus
         ; focus⊒  = focus⊒
         ; valid   = n-f' , Γ-f' , acase₁ ↦□ refl Cls-lifted (↤Sub ↦□ ~?₁)
         }
  -- Case in analysis, focus on right (symmetric).
  extract-pos (minAcase₂ m focus focus⊒ (n-f' , Γ-f' , Cls-lifted)) =
    let inner = extract-pos m
    in record
         { κ       = (case □ of₂ □ · (ana-κ inner .↓)) isSlice
                       ⊑case₂ ⊑□ ⊑□ (ana-κ inner .proof)
         ; γ       = tlₛ (ana-γ inner)
         ; υ_outer = ana-υ_outer inner
         ; focus   = focus
         ; focus⊒  = focus⊒
         ; valid   = n-f' , Γ-f' , acase₂ ↦□ refl (↤Sub ↦□ ~?₁) Cls-lifted
         }
  -- Let-binding in analysis, focus on definition: outer adef₁ Cls' d₂.
  -- Inner Cls' at synPos τ' (cross-mutual to extract). Body exp slice
  -- is □e (minimal); discharges via ↤Sub ↦□ ~?₁. υ_outer = ⊥ₛ.
  extract-pos (minAdef₁ m) =
    let inner = extract m
        _ , _ , inner-cls = inner .valid
    in record
         { κ       = (def (inner .κ .↓) ⊢₁ □) isSlice
                       ⊑def₁ (inner .κ .proof) ⊑□
         ; γ       = inner .γ
         ; υ_outer = ⊥ₛ
         ; focus   = inner .focus
         ; focus⊒  = inner .focus⊒
         ; valid   = _ , _ , adef₁ inner-cls (↤Sub ↦□ ~?₁)
         }
  -- Let-binding analysis, body focus (tightened): outer adef₂ D Cls'.
  -- Same pattern as minSdef₂ but for extract-pos (anaPos result).
  extract-pos {n = n} (minAdef₂ m focus focus⊒ (n-f' , Γ-f' , Cls-lifted)) =
    let inner = extract-pos m
    in record
         { κ       = (def □ ⊢₂ (ana-κ inner .↓)) isSlice
                       ⊑def₂ ⊑□ (ana-κ inner .proof)
         ; γ       = tlₛ (ana-γ inner)
         ; υ_outer = ana-υ_outer inner
         ; focus   = focus
         ; focus⊒  = focus⊒
         ; valid   = n-f' , Γ-f' , adef₂ ↦□ Cls-lifted
         }

-- Direct-mode projectors. These compute the same values as extract /
-- extract-pos's record fields, but WITHOUT the `with extract-pos m | ana-γ
-- inner | ana-valid inner` patterns that block reduction under abstract m.
--
-- Recurse on m directly; build outputs from inner helpers + slice
-- combinators (hdₛ, tlₛ, unmatch{⇒,×,+}, etc.). Used to state the
-- precondition of focus-coverage proofs (Slicing/Analysis/FocusCov.agda)
-- without with-blocking.
mutual

  ana-υ_outer-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                       {Cls : n ； Γ₀ ⊢ C at anaPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]} {υ}
                     → MinAnaPos Cls υ → ⌊ τ_p ⌋

  ana-γ-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                 {Cls : n ； Γ₀ ⊢ C at anaPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]} {υ}
               → MinAnaPos Cls υ → ⌊ Γ₀ ⌋

  ana-κ-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                 {Cls : n ； Γ₀ ⊢ C at anaPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]} {υ}
               → MinAnaPos Cls υ → ⌊ C ⌋

  ana-focus-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                     {Cls : n ； Γ₀ ⊢ C at anaPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]} {υ}
                   → MinAnaPos Cls υ → ⌊ τ ⌋

  syn-γ-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                 {Cls : n ； Γ₀ ⊢ C at synPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]} {υ}
               → MinAna Cls υ → ⌊ Γ₀ ⌋

  syn-κ-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                 {Cls : n ； Γ₀ ⊢ C at synPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]} {υ}
               → MinAna Cls υ → ⌊ C ⌋

  syn-focus-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                     {Cls : n ； Γ₀ ⊢ C at synPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]} {υ}
                   → MinAna Cls υ → ⌊ τ ⌋

  -- ana-υ_outer-of-m: the outer-analysis-type slice tracked by MinAnaPos.
  ana-υ_outer-of-m min□Pos                     = ⊥ₛ
  ana-υ_outer-of-m (minA○ υ)                   = υ
  ana-υ_outer-of-m (minASub _)                 = ⊥ₛ
  ana-υ_outer-of-m (minAλ: _ outer-υ _ _)      = outer-υ
  ana-υ_outer-of-m (minAλ⇒ {eq = eq} m)        =
    unmatch⇒ eq (hdₛ (ana-γ-of-m m)) (ana-υ_outer-of-m m)
  ana-υ_outer-of-m (minA&₁ {eq = eq} m)        =
    unmatch× eq (ana-υ_outer-of-m m) ⊥ₛ
  ana-υ_outer-of-m (minA&₂ {eq = eq} m)        =
    unmatch× eq ⊥ₛ (ana-υ_outer-of-m m)
  ana-υ_outer-of-m (minAι₁ {eq = eq} m)        =
    unmatch+ eq (ana-υ_outer-of-m m) ⊥ₛ
  ana-υ_outer-of-m (minAι₂ {eq = eq} m)        =
    unmatch+ eq ⊥ₛ (ana-υ_outer-of-m m)
  ana-υ_outer-of-m (minAcase₁ m _ _ _)     = ana-υ_outer-of-m m
  ana-υ_outer-of-m (minAcase₂ m _ _ _)     = ana-υ_outer-of-m m
  ana-υ_outer-of-m (minAdef₁ _)                = ⊥ₛ
  ana-υ_outer-of-m (minAdef₂ m _ _ _)              = ana-υ_outer-of-m m

  -- ana-γ-of-m: slice of the outer assumptions Γ₀.
  ana-γ-of-m min□Pos                       = ⊥ₛ
  ana-γ-of-m (minA○ _)                     = ⊥ₛ
  ana-γ-of-m (minASub m)                   = syn-γ-of-m m
  ana-γ-of-m (minAλ: m _ _ _) = tlₛ (ana-γ-of-m m)
  ana-γ-of-m (minAλ⇒ m)                    = tlₛ (ana-γ-of-m m)
  ana-γ-of-m (minA&₁ m)                    = ana-γ-of-m m
  ana-γ-of-m (minA&₂ m)                    = ana-γ-of-m m
  ana-γ-of-m (minAι₁ m)                    = ana-γ-of-m m
  ana-γ-of-m (minAι₂ m)                    = ana-γ-of-m m
  ana-γ-of-m (minAcase₁ m _ _ _)       = tlₛ (ana-γ-of-m m)
  ana-γ-of-m (minAcase₂ m _ _ _)       = tlₛ (ana-γ-of-m m)
  ana-γ-of-m (minAdef₁ m)                  = syn-γ-of-m m
  ana-γ-of-m (minAdef₂ m _ _ _)                = tlₛ (ana-γ-of-m m)

  -- ana-κ-of-m: slice of the surrounding context C.
  ana-κ-of-m min□Pos                       = ⊥ₛ
  ana-κ-of-m (minA○ _)                     = ⊥ₛ
  ana-κ-of-m (minASub m)                   = syn-κ-of-m m
  ana-κ-of-m (minAλ: m _ _ _) =
    (λ: _ ⇒ ana-κ-of-m m .↓) isSlice
      ⊑λ (hdₛ (ana-γ-of-m m) .proof) (ana-κ-of-m m .proof)
  ana-κ-of-m (minAλ⇒ m)                    =
    (λ⇒ (ana-κ-of-m m .↓)) isSlice ⊑λu (ana-κ-of-m m .proof)
  ana-κ-of-m (minA&₁ m)                    =
    ((ana-κ-of-m m .↓) &₁ _) isSlice ⊑&₁ (ana-κ-of-m m .proof) (⊑.refl {A = Exp})
  ana-κ-of-m (minA&₂ m)                    =
    (_ &₂ (ana-κ-of-m m .↓)) isSlice ⊑&₂ (⊑.refl {A = Exp}) (ana-κ-of-m m .proof)
  ana-κ-of-m (minAι₁ m)                    =
    (ι₁ (ana-κ-of-m m .↓)) isSlice ⊑ι₁ (ana-κ-of-m m .proof)
  ana-κ-of-m (minAι₂ m)                    =
    (ι₂ (ana-κ-of-m m .↓)) isSlice ⊑ι₂ (ana-κ-of-m m .proof)
  ana-κ-of-m (minAcase₁ m _ _ _)       =
    (case □ of (ana-κ-of-m m .↓) ·₁ □) isSlice
      ⊑case₁ ⊑□ (ana-κ-of-m m .proof) ⊑□
  ana-κ-of-m (minAcase₂ m _ _ _)       =
    (case □ of₂ □ · (ana-κ-of-m m .↓)) isSlice
      ⊑case₂ ⊑□ ⊑□ (ana-κ-of-m m .proof)
  ana-κ-of-m (minAdef₁ m)                  =
    (def (syn-κ-of-m m .↓) ⊢₁ _) isSlice ⊑def₁ (syn-κ-of-m m .proof) (⊑.refl {A = Exp})
  ana-κ-of-m (minAdef₂ m _ _ _)                =
    (def _ ⊢₂ (ana-κ-of-m m .↓)) isSlice ⊑def₂ (⊑.refl {A = Exp}) (ana-κ-of-m m .proof)

  -- ana-focus-of-m: slice of the focus type τ. Propagates unchanged through
  -- structural rules; equals υ at leaves and ⊥ at the bottom slice.
  ana-focus-of-m min□Pos                   = ⊥ₛ
  ana-focus-of-m (minA○ υ)                 = υ
  ana-focus-of-m (minASub m)               = syn-focus-of-m m
  ana-focus-of-m (minAλ: m _ _ _) = ana-focus-of-m m
  ana-focus-of-m (minAλ⇒ m)                = ana-focus-of-m m
  ana-focus-of-m (minA&₁ m)                = ana-focus-of-m m
  ana-focus-of-m (minA&₂ m)                = ana-focus-of-m m
  ana-focus-of-m (minAι₁ m)                = ana-focus-of-m m
  ana-focus-of-m (minAι₂ m)                = ana-focus-of-m m
  ana-focus-of-m (minAcase₁ _ focus _ _)   = focus
  ana-focus-of-m (minAcase₂ _ focus _ _)   = focus
  ana-focus-of-m (minAdef₁ m)              = syn-focus-of-m m
  ana-focus-of-m (minAdef₂ _ focus _ _)    = focus

  -- syn-γ-of-m: slice of the outer Γ₀ for MinAna (synPos position).
  syn-γ-of-m min□                          = ⊥ₛ
  syn-γ-of-m (minSλ: _ m)                  = tlₛ (syn-γ-of-m m)
  syn-γ-of-m (minS∘₁ m)                    = syn-γ-of-m m
  syn-γ-of-m (minS∘₂ _ ss _ _ _)           = ss ↓s ↓γₛ
  syn-γ-of-m (minS<>₁ m)                   = syn-γ-of-m m
  syn-γ-of-m (minS&₁ m)                    = syn-γ-of-m m
  syn-γ-of-m (minS&₂ m)                    = syn-γ-of-m m
  syn-γ-of-m (minScase₁ m _ _ _ _ _)   = tlₛ (syn-γ-of-m m)
  syn-γ-of-m (minScase₂ m _ _ _ _ _)   = tlₛ (syn-γ-of-m m)
  syn-γ-of-m (minSπ₁ m)                    = syn-γ-of-m m
  syn-γ-of-m (minSπ₂ m)                    = syn-γ-of-m m
  syn-γ-of-m (minSΛ m)                     = unshiftΓₛ (syn-γ-of-m m)
  syn-γ-of-m (minSdef₁ m)                  = syn-γ-of-m m
  syn-γ-of-m (minSdef₂ m _ _ _ _ _)        = tlₛ (syn-γ-of-m m)

  -- syn-κ-of-m: slice of the surrounding context C.
  syn-κ-of-m min□                          = ⊥ₛ
  syn-κ-of-m (minSλ: _ m)                  =
    (λ: _ ⇒ syn-κ-of-m m .↓) isSlice
      ⊑λ (hdₛ (syn-γ-of-m m) .proof) (syn-κ-of-m m .proof)
  syn-κ-of-m (minS∘₁ m)                    =
    ((syn-κ-of-m m .↓) ∘₁ _) isSlice ⊑∘₁ (syn-κ-of-m m .proof) (⊑.refl {A = Exp})
  syn-κ-of-m (minS∘₂ m ss _ _ _)           =
    ((ss ↓s ↓σ) ∘₂ (ana-κ-of-m m .↓)) isSlice
      ⊑∘₂ (ss ↓s ↓σ⊑) (ana-κ-of-m m .proof)
  syn-κ-of-m (minS<>₁ m)                   =
    ((syn-κ-of-m m .↓) < _ >₁) isSlice ⊑<>₁ (syn-κ-of-m m .proof) (⊑.refl {A = Typ})
  syn-κ-of-m (minS&₁ m)                    =
    ((syn-κ-of-m m .↓) &₁ _) isSlice ⊑&₁ (syn-κ-of-m m .proof) (⊑.refl {A = Exp})
  syn-κ-of-m (minS&₂ m)                    =
    (_ &₂ (syn-κ-of-m m .↓)) isSlice ⊑&₂ (⊑.refl {A = Exp}) (syn-κ-of-m m .proof)
  syn-κ-of-m (minScase₁ m _ _ _ _ _) =
    (case _ of (syn-κ-of-m m .↓) ·₁ _) isSlice
      ⊑case₁ (⊑.refl {A = Exp}) (syn-κ-of-m m .proof) (⊑.refl {A = Exp})
  syn-κ-of-m (minScase₂ m _ _ _ _ _) =
    (case _ of₂ _ · (syn-κ-of-m m .↓)) isSlice
      ⊑case₂ (⊑.refl {A = Exp}) (⊑.refl {A = Exp}) (syn-κ-of-m m .proof)
  syn-κ-of-m (minSπ₁ m)                    =
    (π₁ (syn-κ-of-m m .↓)) isSlice ⊑π₁ (syn-κ-of-m m .proof)
  syn-κ-of-m (minSπ₂ m)                    =
    (π₂ (syn-κ-of-m m .↓)) isSlice ⊑π₂ (syn-κ-of-m m .proof)
  syn-κ-of-m (minSΛ m)                     =
    (Λ (syn-κ-of-m m .↓)) isSlice ⊑Λ (syn-κ-of-m m .proof)
  syn-κ-of-m (minSdef₁ m)                  =
    (def (syn-κ-of-m m .↓) ⊢₁ _) isSlice ⊑def₁ (syn-κ-of-m m .proof) (⊑.refl {A = Exp})
  syn-κ-of-m (minSdef₂ m _ _ _ _ _)        =
    (def _ ⊢₂ (syn-κ-of-m m .↓)) isSlice ⊑def₂ (⊑.refl {A = Exp}) (syn-κ-of-m m .proof)

  -- syn-focus-of-m: slice of the focus type τ.
  syn-focus-of-m min□                      = ⊥ₛ
  syn-focus-of-m (minSλ: _ m)              = syn-focus-of-m m
  syn-focus-of-m (minS∘₁ m)                = syn-focus-of-m m
  syn-focus-of-m (minS∘₂ _ _ focus _ _)    = focus
  syn-focus-of-m (minS<>₁ m)               = syn-focus-of-m m
  syn-focus-of-m (minS&₁ m)                = syn-focus-of-m m
  syn-focus-of-m (minS&₂ m)                = syn-focus-of-m m
  syn-focus-of-m (minScase₁ _ _ _ focus _ _) = focus
  syn-focus-of-m (minScase₂ _ _ _ focus _ _) = focus
  syn-focus-of-m (minSπ₁ m)                = syn-focus-of-m m
  syn-focus-of-m (minSπ₂ m)                = syn-focus-of-m m
  syn-focus-of-m (minSΛ m)                 = syn-focus-of-m m
  syn-focus-of-m (minSdef₁ m)              = syn-focus-of-m m
  syn-focus-of-m (minSdef₂ _ _ _ focus _ _) = focus

-- Completeness: every minimal AnaSlice arises from some MinAna; same
-- for AnaPosSlice. Postulated for now (out of scope for this iteration).
postulate
  complete : ∀ {n Γ₀ C n_f Γ τ τ_p} {Cls : n ； Γ₀ ⊢ C at synPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]} {υ}
           → (s : AnaSlice Cls υ) → IsMinimal s
           → Σ[ m ∈ MinAna Cls υ ] (extract m) ≈ s
  completePos : ∀ {n Γ₀ C n_f Γ τ τ_p} {Cls : n ； Γ₀ ⊢ C at anaPos τ_p ▷ n_f ； Γ [ ⇐mode τ ]} {υ}
              → (s : AnaPosSlice Cls υ) → IsMinimalPos s
              → Σ[ m ∈ MinAnaPos Cls υ ] (extract-pos m) ≈ s
