{-# OPTIONS --allow-incomplete-matches #-}
open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import Core
open import Semantics.Statics
open import Semantics.Graduality using (mode-⊑; ⇐mode-⊑; ⇒mode-⊑;
                                          static-gradual-syn; static-gradual-ana;
                                          static-gradual-syn-cls; static-gradual-ana-cls)
open import Slicing.Synthesis.Synthesis using (SynSlice_◂_; MinSynSlice_◂_;
                                                 _↓s; _↓γ; _↓γₛ; _↓γ⊑; _↓σ; _↓σ⊑; _↓ϕ;
                                                 _⇑_∈_⊒_; ⊤-syn; minExists)
import Slicing.Synthesis.Synthesis as SS
open import Slicing.Analysis.Analysis
open import Slicing.Analysis.AnaSliceCalc
open import Slicing.Analysis.Alignment using (scase₁-Cls-lifted; scase₂-Cls-lifted;
                                                 acase₁-Cls-lifted; acase₂-Cls-lifted;
                                                 sdef₂-Cls-lifted; adef₂-Cls-lifted)
open import Core.Typ.Lift using (unmatch⇒; unmatch⇒-min; match⇒ₛ; cod⇒ₛ; dom⇒ₛ)
open import Core.Typ.Properties using (⊔-ann-⇒-⊑-intro-full)

-- Algorithmic construction of MinAna / MinAnaPos from a context classification + query,
-- plus the top-level `slice-ana` composing with `extract`. Mirrors `slice` in
-- Slicing.Synthesis.FixedAssmsSlicing.
-- INCOMPLETE: focus-⊑ witnesses are postulated; the s<>₁ coverage gap keeps
-- --allow-incomplete-matches in place.
-- Dissertation: §8.6 Term-Minimal Slices (analysis side).
module Slicing.Analysis.AnaSlicing where

private
  postulate
    focus-⊑ : ∀ {τ : Typ} (υ φ : ⌊ τ ⌋) → υ ⊑ₛ φ

-- Helper: construct a MinSynSlice D ◂ υ via ⊤-syn → reindex → minExists.
syn-slice : ∀ {n Γ e τ} → (D : n , Γ ⊢ e ⇑ τ) → (υ : ⌊ τ ⌋) → MinSynSlice D ◂ υ
syn-slice D υ = proj₁ (SS.minExists (SynSlice_◂_.reindex (⊤-syn D) (⊤ₛ-max υ)))

mutual
  ana-slice : ∀ {n Γ₀ C n_f Γ τ τ_p}
            → (Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ])
            → (υ : ⌊ τ ⌋)
            → MinAna Cls υ

  ana-slice-pos : ∀ {n Γ₀ C n_f Γ τ τ_p}
                → (Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ])
                → (υ : ⌊ τ ⌋)
                → MinAnaPos Cls υ

  -- min□ for υ = ⊥ₛ
  ana-slice Cls (□ isSlice ⊑□) = min□

  ana-slice (sλ: wf Cls') υ@(_ isSlice _) =
    minSλ: ⊥ₛ (ana-slice Cls' υ)

  ana-slice (s∘₁ Cls' eq d₂) υ@(_ isSlice _) =
    minS∘₁ (ana-slice Cls' υ)

  -- s∘₂: recurse on Cls' (anaPos), get a MinSynSlice for D₁ queried
  -- at unmatch⇒ eq υ-out ⊥ₛ, lift Cls' to ss.γ at position (dom⇒ₛ ψ eq).↓
  -- via static-gradual-ana-cls.
  ana-slice {τ = τ-outer} (s∘₂ {τ = τ₀} D₁ eq Cls') υ@(_ isSlice _)
    with ana-slice-pos Cls' υ
  ... | m
    with syn-slice D₁ (unmatch⇒-min {τ₀} eq (ana-υ_outer (extract-pos m)) ⊥ₛ)
  ... | ss
    with static-gradual-ana-cls (ss ↓s ↓γ⊑) (ana-κ (extract-pos m) .proof)
                                (dom⇒ₛ (SynSlice_◂_.type (ss ↓s)) eq .proof) Cls'
  ... | _ , _ , _ , _ , ⇐mode-⊑ {τ₁ = τ_f} τ_f⊑ , cls-lifted =
        minS∘₂ m ss (τ_f isSlice τ_f⊑) (focus-⊑ υ (τ_f isSlice τ_f⊑)) (_ , _ , cls-lifted)

  ana-slice (s<>₁ Cls' eq wf) υ@(_ isSlice _) =
    minS<>₁ (ana-slice Cls' υ)

  ana-slice (s&₁ Cls' d₂) υ@(_ isSlice _) =
    minS&₁ (ana-slice Cls' υ)

  ana-slice (s&₂ d₁ Cls') υ@(_ isSlice _) =
    minS&₂ (ana-slice Cls' υ)

  ana-slice (scase₁ D eq Cls' d₂ con) υ@(_ isSlice _) =
    let m = ana-slice Cls' υ
        τ_p' , τ_p'⊑ , τ_m' , τ_m'⊑ , n-f' , Γ-f' , Cls-lifted = scase₁-Cls-lifted m
        typ' = τ_p' isSlice (⊑.trans {Typ} τ_p'⊑ (extract m .type .proof))
        focus' = τ_m' isSlice (⊑.trans {Typ} τ_m'⊑ (extract m .focus .proof))
    in minScase₁ m typ' τ_p'⊑ focus' (focus-⊑ υ focus') (n-f' , Γ-f' , Cls-lifted)

  ana-slice (scase₂ D eq d₁ Cls' con) υ@(_ isSlice _) =
    let m = ana-slice Cls' υ
        τ_p' , τ_p'⊑ , τ_m' , τ_m'⊑ , n-f' , Γ-f' , Cls-lifted = scase₂-Cls-lifted m
        typ' = τ_p' isSlice (⊑.trans {Typ} τ_p'⊑ (extract m .type .proof))
        focus' = τ_m' isSlice (⊑.trans {Typ} τ_m'⊑ (extract m .focus .proof))
    in minScase₂ m typ' τ_p'⊑ focus' (focus-⊑ υ focus') (n-f' , Γ-f' , Cls-lifted)

  ana-slice (sι₁ Cls') υ@(_ isSlice _) =
    minSι₁ (ana-slice Cls' υ)

  ana-slice (sι₂ Cls') υ@(_ isSlice _) =
    minSι₂ (ana-slice Cls' υ)

  ana-slice (sπ₁ Cls' eq) υ@(_ isSlice _) =
    minSπ₁ (ana-slice Cls' υ)

  ana-slice (sπ₂ Cls' eq) υ@(_ isSlice _) =
    minSπ₂ (ana-slice Cls' υ)

  ana-slice (sΛ Cls') υ@(_ isSlice _) =
    minSΛ (ana-slice Cls' υ)

  ana-slice (sdef₁ Cls' d₂) υ@(_ isSlice _) =
    minSdef₁ (ana-slice Cls' υ)

  ana-slice (sdef₂ {e = e} D Cls') υ@(_ isSlice _) =
    let m = ana-slice Cls' υ
        τ_p' , τ_p'⊑ , τ_m' , τ_m'⊑ , n-f' , Γ-f' , Cls-lifted = sdef₂-Cls-lifted m
        typ' = τ_p' isSlice (⊑.trans {Typ} τ_p'⊑ (extract m .type .proof))
        focus' = τ_m' isSlice (⊑.trans {Typ} τ_m'⊑ (extract m .focus .proof))
    in minSdef₂ m typ' τ_p'⊑ focus' (focus-⊑ υ focus') (n-f' , Γ-f' , Cls-lifted)

  -- anaPos cases

  ana-slice-pos Cls (□ isSlice ⊑□) = min□Pos

  ana-slice-pos (a○ {τ = τ}) υ@(_ isSlice _) = minA○ υ

  ana-slice-pos (aSub Cls' c) υ@(_ isSlice _) =
    minASub (ana-slice Cls' υ)

  -- aλ:: pick outer-υ = ⊥ₛ. Then outer-υ.↓ = □, so:
  --   * outer-υ.↓ ~ hd.↓ ⇒ □ holds via ~?₂.
  --   * outer-υ.↓ ⊔ hd.↓ ⇒ □ = □ ⊔ hd.↓ ⇒ □ reduces (when hd is concrete)
  --     to hd.↓ ⇒ □; we need this to equal hd.↓ ⇒ ana-υ_outer.↓, i.e.,
  --     ana-υ_outer.↓ ≡ □. We bridge via postulate aλ-match-eq applied
  --     with all implicits explicit so Agda can solve constraints.
  -- aλ:: construct outer-υ via ⊔-ann-⇒-⊑-intro-full using hd from m's binder
  -- slice and ana-υ_outer from m. This packages the lifted match equation
  -- AND the consistency, both proved by induction on τ's shape.
  ana-slice-pos {τ_p = τ-pos} (aλ: {τ₁ = τ_a} {τ₂ = τ_b} c eq wf Cls') υ@(_ isSlice _)
    with ana-slice-pos Cls' υ
  ... | m
    with ⊔-ann-⇒-⊑-intro-full eq (hdₛ (ana-γ (extract-pos m)) .proof)
                                 (ana-υ_outer (extract-pos m) .proof)
  ... | _ , outer⊑τ , eq-built , c-built =
        minAλ: m (_ isSlice outer⊑τ) c-built eq-built

  ana-slice-pos (aλ⇒ eq Cls') υ@(_ isSlice _) =
    minAλ⇒ (ana-slice-pos Cls' υ)

  ana-slice-pos (a&₁ eq Cls' d₂) υ@(_ isSlice _) =
    minA&₁ (ana-slice-pos Cls' υ)

  ana-slice-pos (a&₂ eq d₁ Cls') υ@(_ isSlice _) =
    minA&₂ (ana-slice-pos Cls' υ)

  ana-slice-pos (aι₁ eq Cls') υ@(_ isSlice _) =
    minAι₁ (ana-slice-pos Cls' υ)

  ana-slice-pos (aι₂ eq Cls') υ@(_ isSlice _) =
    minAι₂ (ana-slice-pos Cls' υ)

  ana-slice-pos (acase₁ D eq Cls' d₂) υ@(_ isSlice _) =
    let m = ana-slice-pos Cls' υ
        τ_m' , τ_m'⊑ , n-f' , Γ-f' , Cls-lifted = acase₁-Cls-lifted m
        focus' = τ_m' isSlice (⊑.trans {Typ} τ_m'⊑ (ana-focus (extract-pos m) .proof))
    in minAcase₁ m focus' (focus-⊑ υ focus') (n-f' , Γ-f' , Cls-lifted)

  ana-slice-pos (acase₂ D eq d₁ Cls') υ@(_ isSlice _) =
    let m = ana-slice-pos Cls' υ
        τ_m' , τ_m'⊑ , n-f' , Γ-f' , Cls-lifted = acase₂-Cls-lifted m
        focus' = τ_m' isSlice (⊑.trans {Typ} τ_m'⊑ (ana-focus (extract-pos m) .proof))
    in minAcase₂ m focus' (focus-⊑ υ focus') (n-f' , Γ-f' , Cls-lifted)

  ana-slice-pos (adef₁ Cls' d₂) υ@(_ isSlice _) =
    minAdef₁ (ana-slice Cls' υ)

  ana-slice-pos (adef₂ {e = e} D Cls') υ@(_ isSlice _) =
    let m = ana-slice-pos Cls' υ
        τ_m' , τ_m'⊑ , n-f' , Γ-f' , Cls-lifted = adef₂-Cls-lifted m
        focus' = τ_m' isSlice (⊑.trans {Typ} τ_m'⊑ (ana-focus (extract-pos m) .proof))
    in minAdef₂ m focus' (focus-⊑ υ focus') (n-f' , Γ-f' , Cls-lifted)

-- Top-level: produce the extracted AnaSlice directly from a Cls and query.
slice-ana : ∀ {n Γ₀ C n_f Γ τ τ_p}
          → (Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ])
          → (υ : ⌊ τ ⌋)
          → AnaSlice Cls υ
slice-ana Cls υ = extract (ana-slice Cls υ)

slice-ana-pos : ∀ {n Γ₀ C n_f Γ τ τ_p}
              → (Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ])
              → (υ : ⌊ τ ⌋)
              → AnaPosSlice Cls υ
slice-ana-pos Cls υ = extract-pos (ana-slice-pos Cls υ)
