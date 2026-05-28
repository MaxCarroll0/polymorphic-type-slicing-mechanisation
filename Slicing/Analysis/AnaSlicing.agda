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
open import Slicing.Analysis.FocusCov using (lift-pos-cov; lift-syn-cov)
open import Slicing.Analysis.Minimality using (syn-cls-precision)
open import Core.Typ.Lift using (unmatch⇒; unmatch⇒-min; match⇒ₛ; cod⇒ₛ; dom⇒ₛ;
                                  unmatch⇒-cov-dom;
                                  unmatch+-min; match+ₛ; fst+ₛ'; snd+ₛ')
open import Core.Typ.Properties using (⊔-ann-⇒-⊑-intro-full; ⊔-⇒-⊑)
open import Core.Assms.Lift using (hdₛ; tlₛ; cons-decompₛ)

-- Algorithmic MinAna / MinAnaPos construction (Dissertation §8.6).
module Slicing.Analysis.AnaSlicing where

private
  unmatch⇒-min-dom-cov : ∀ {τ τ₁ τ₂} (eq : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂) (υ : ⌊ τ₁ ⌋)
                       → ∀ {ψ : ⌊ τ ⌋}
                       → (unmatch⇒-min {τ} {τ₁} {τ₂} eq υ (⊥ₛ {a = τ₂})) ⊑ₛ ψ
                       → υ .↓ ⊑t (dom⇒ₛ ψ eq) .↓
  unmatch⇒-min-dom-cov eq (.□ isSlice ⊑□) _ = ⊑□
  unmatch⇒-min-dom-cov {τ} {τ₁} {τ₂} eq υ@(_ isSlice ⊑*) {ψ} prec =
    unmatch⇒-cov-dom τ eq υ (⊥ₛ {a = τ₂}) prec (match⇒ₛ ψ eq)
  unmatch⇒-min-dom-cov {τ} {τ₁} {τ₂} eq υ@(_ isSlice ⊑Var) {ψ} prec =
    unmatch⇒-cov-dom τ eq υ (⊥ₛ {a = τ₂}) prec (match⇒ₛ ψ eq)
  unmatch⇒-min-dom-cov {τ} {τ₁} {τ₂} eq υ@(_ isSlice (⊑⇒ _ _)) {ψ} prec =
    unmatch⇒-cov-dom τ eq υ (⊥ₛ {a = τ₂}) prec (match⇒ₛ ψ eq)
  unmatch⇒-min-dom-cov {τ} {τ₁} {τ₂} eq υ@(_ isSlice (⊑+ _ _)) {ψ} prec =
    unmatch⇒-cov-dom τ eq υ (⊥ₛ {a = τ₂}) prec (match⇒ₛ ψ eq)
  unmatch⇒-min-dom-cov {τ} {τ₁} {τ₂} eq υ@(_ isSlice (⊑× _ _)) {ψ} prec =
    unmatch⇒-cov-dom τ eq υ (⊥ₛ {a = τ₂}) prec (match⇒ₛ ψ eq)
  unmatch⇒-min-dom-cov {τ} {τ₁} {τ₂} eq υ@(_ isSlice (⊑∀ _)) {ψ} prec =
    unmatch⇒-cov-dom τ eq υ (⊥ₛ {a = τ₂}) prec (match⇒ₛ ψ eq)

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

  ana-slice Cls (□ isSlice ⊑□) = min□

  ana-slice (sλ: wf Cls') υ@(_ isSlice _) =
    minSλ: ⊥ₛ (ana-slice Cls' υ)

  ana-slice (s∘₁ Cls' eq d₂) υ@(_ isSlice _) =
    minS∘₁ (ana-slice Cls' υ)

  ana-slice {τ = τ-outer} (s∘₂ {τ = τ₀} D₁ eq Cls') υ@(_ isSlice _)
    with ana-slice-pos Cls' υ
  ... | m
    with syn-slice D₁ (unmatch⇒-min {τ₀} eq (ana-υ_outer (extract-pos m)) ⊥ₛ)
  ... | ss
    with subst (λ x → x .↓ ⊑t (dom⇒ₛ (SynSlice_◂_.type (ss ↓s)) eq) .↓)
               (ana-υ_outer-≡ m)
               (unmatch⇒-min-dom-cov eq (ana-υ_outer (extract-pos m))
                                       {ψ = SynSlice_◂_.type (ss ↓s)}
                                       (SynSlice_◂_.valid (ss ↓s)))
  ... | pre
    with lift-pos-cov m (ss ↓s ↓γ⊑) (ana-κ (extract-pos m) .proof)
                       (dom⇒ₛ (SynSlice_◂_.type (ss ↓s)) eq .proof) pre
  ... | _ , _ , τ_f , _ , τ_f⊑ , cov , cls-lifted =
        minS∘₂ m ss (τ_f isSlice τ_f⊑) cov (_ , _ , cls-lifted)

  ana-slice (s<>₁ Cls' eq wf) υ@(_ isSlice _) =
    minS<>₁ (ana-slice Cls' υ)

  ana-slice (s&₁ Cls' d₂) υ@(_ isSlice _) =
    minS&₁ (ana-slice Cls' υ)

  ana-slice (s&₂ d₁ Cls') υ@(_ isSlice _) =
    minS&₂ (ana-slice Cls' υ)

  ana-slice (scase₁ {τ = τ₀} {τ₁ = τ₁} D eq Cls' d₂ con) υ@(_ isSlice _) =
    let m = ana-slice Cls' υ
        inner = extract m
        ss = syn-slice D (unmatch+-min {τ₀} eq (hdₛ (inner .γ)) ⊥ₛ)
        ψ = SynSlice_◂_.type (ss ↓s)
        X = fst+ₛ' ψ eq
        Γ⊑outer = ⊑∷ (X .proof) (ss ↓s ↓γ⊑)
        _ , τ_p⊑ , _ , _ , _ , _ , τ_f⊑ , cov , Cls-lifted =
          lift-syn-cov m Γ⊑outer (inner .κ .proof)
        typ' = _ isSlice (syn-cls-precision Γ⊑outer (inner .κ .proof) Cls-lifted Cls')
        focus' = _ isSlice τ_f⊑
    in minScase₁ m ss typ' focus' cov (_ , _ , Cls-lifted)

  ana-slice (scase₂ {τ = τ₀} {τ₂ = τ₂} D eq d₁ Cls' con) υ@(_ isSlice _) =
    let m = ana-slice Cls' υ
        inner = extract m
        ss = syn-slice D (unmatch+-min {τ₀} eq ⊥ₛ (hdₛ (inner .γ)))
        ψ = SynSlice_◂_.type (ss ↓s)
        X = snd+ₛ' ψ eq
        Γ⊑outer = ⊑∷ (X .proof) (ss ↓s ↓γ⊑)
        _ , τ_p⊑ , _ , _ , _ , _ , τ_f⊑ , cov , Cls-lifted =
          lift-syn-cov m Γ⊑outer (inner .κ .proof)
        typ' = _ isSlice (syn-cls-precision Γ⊑outer (inner .κ .proof) Cls-lifted Cls')
        focus' = _ isSlice τ_f⊑
    in minScase₂ m ss typ' focus' cov (_ , _ , Cls-lifted)

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

  ana-slice (sdef₂ {τ' = τ_b} D Cls') υ@(_ isSlice _) =
    let m = ana-slice Cls' υ
        inner = extract m
        ss = syn-slice D (hdₛ (inner .γ))
        ψ = SynSlice_◂_.type (ss ↓s)
        Γ⊑outer = ⊑∷ (ψ .proof) (ss ↓s ↓γ⊑)
        _ , τ_p⊑ , _ , _ , _ , _ , τ_f⊑ , cov , Cls-lifted =
          lift-syn-cov m Γ⊑outer (inner .κ .proof)
        typ' = _ isSlice (syn-cls-precision Γ⊑outer (inner .κ .proof) Cls-lifted Cls')
        focus' = _ isSlice τ_f⊑
    in minSdef₂ m ss typ' focus' cov (_ , _ , Cls-lifted)

  ana-slice-pos Cls (□ isSlice ⊑□) = min□Pos

  ana-slice-pos (a○ {τ = τ}) υ@(_ isSlice _) = minA○ υ

  ana-slice-pos (aSub Cls' c) υ@(_ isSlice _) =
    minASub (ana-slice Cls' υ)

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

  ana-slice-pos (acase₁ {τ₀ = τ₀} {τ₁ = τ₁} D eq Cls' d₂) υ@(_ isSlice _) =
    let m = ana-slice-pos Cls' υ
        inner = extract-pos m
        ss = syn-slice D (unmatch+-min {τ₀} eq (hdₛ (ana-γ inner)) ⊥ₛ)
        ψ = SynSlice_◂_.type (ss ↓s)
        X = fst+ₛ' ψ eq
        Γ⊑ : (X .↓ ∷ (ss ↓s ↓γ)) ⊑a (τ₁ ∷ _)
        Γ⊑ = ⊑∷ (X .proof) (ss ↓s ↓γ⊑)
        pre = subst (λ x → ana-υ_outer-of-m m .↓ ⊑t x .↓) (sym (ana-υ_outer-≡ m))
                     (⊑.refl {A = Typ})
        _ , _ , τ_f , _ , τ_f⊑ , cov , Cls-lifted =
          lift-pos-cov m Γ⊑ (ana-κ inner .proof) (ana-υ_outer inner .proof) pre
    in minAcase₁ m ss (τ_f isSlice τ_f⊑) cov (_ , _ , Cls-lifted)

  ana-slice-pos (acase₂ {τ₀ = τ₀} {τ₂ = τ₂} D eq d₁ Cls') υ@(_ isSlice _) =
    let m = ana-slice-pos Cls' υ
        inner = extract-pos m
        ss = syn-slice D (unmatch+-min {τ₀} eq ⊥ₛ (hdₛ (ana-γ inner)))
        ψ = SynSlice_◂_.type (ss ↓s)
        X = snd+ₛ' ψ eq
        Γ⊑ : (X .↓ ∷ (ss ↓s ↓γ)) ⊑a (τ₂ ∷ _)
        Γ⊑ = ⊑∷ (X .proof) (ss ↓s ↓γ⊑)
        pre = subst (λ x → ana-υ_outer-of-m m .↓ ⊑t x .↓) (sym (ana-υ_outer-≡ m))
                     (⊑.refl {A = Typ})
        _ , _ , τ_f , _ , τ_f⊑ , cov , Cls-lifted =
          lift-pos-cov m Γ⊑ (ana-κ inner .proof) (ana-υ_outer inner .proof) pre
    in minAcase₂ m ss (τ_f isSlice τ_f⊑) cov (_ , _ , Cls-lifted)

  ana-slice-pos (adef₁ Cls' d₂) υ@(_ isSlice _) =
    minAdef₁ (ana-slice Cls' υ)

  ana-slice-pos (adef₂ {e = e} {τ' = τ_b} D Cls') υ@(_ isSlice _) =
    let m = ana-slice-pos Cls' υ
        inner = extract-pos m
        ss = syn-slice D (hdₛ (ana-γ inner))
        ψ = SynSlice_◂_.type (ss ↓s)
        Γ⊑ : (ψ .↓ ∷ (ss ↓s ↓γ)) ⊑a (τ_b ∷ _)
        Γ⊑ = ⊑∷ (ψ .proof) (ss ↓s ↓γ⊑)
        pre = subst (λ x → ana-υ_outer-of-m m .↓ ⊑t x .↓) (sym (ana-υ_outer-≡ m))
                     (⊑.refl {A = Typ})
        _ , _ , τ_f , _ , τ_f⊑ , cov , Cls-lifted =
          lift-pos-cov m Γ⊑ (ana-κ inner .proof) (ana-υ_outer inner .proof) pre
    in minAdef₂ m ss (τ_f isSlice τ_f⊑) cov (_ , _ , Cls-lifted)

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
