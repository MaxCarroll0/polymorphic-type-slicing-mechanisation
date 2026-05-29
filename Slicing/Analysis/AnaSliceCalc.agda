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
                                  unmatch⇒-min; unmatch×-min; unmatch+-min;
                                  _⇒ₛ_; _×ₛ_; _+ₛ_; ∀·ₛ;
                                  fst×ₛ'; snd×ₛ; fst+ₛ'; snd+ₛ';
                                  dom⇒ₛ; cod⇒ₛ; body∀ₛ; match⇒ₛ; match×ₛ; match+ₛ; match∀ₛ)
open import Core.Assms.Lift using (shift-unshiftΓ; hdₛ; tlₛ; unshiftΓₛ; cons-decompₛ)
open import Relation.Binary.PropositionalEquality using (sym; subst; cong; cong₂; trans)
open import Semantics.Statics
open import Slicing.Synthesis.Synthesis using (SynSlice_◂_; _⇑_∈_⊒_; MinSynSlice_◂_; _↓s; _↓γ; _↓γₛ; _↓σ; _↓σₛ; _↓σ⊑; _↓γ⊑; _↓ϕ; _↓ϕₛ)
import Slicing.Synthesis.Synthesis as SS
open import Semantics.Graduality using (static-gradual-syn; static-gradual-ana; static-gradual-ana-cls)
open import Slicing.Synthesis.SynSliceCalc using (_⊢_◂_⇑_⊣_)
import Slicing.Synthesis.SynSliceCalc as SSC
open import Slicing.Analysis.Analysis

-- Mutually-recursive minimal analysis slice calculi (Dissertation §8.6).
module Slicing.Analysis.AnaSliceCalc where

mutual
  data MinAna : ∀ {n Γ₀ C n_f Γ τ τ_p}
              → (Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]) → ⌊ τ ⌋ → Set
  data MinAnaPos : ∀ {n Γ₀ C n_f Γ τ τ_p}
                 → (Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]) → ⌊ τ ⌋ → Set

  extract-pos : ∀ {n Γ₀ C n_f Γ τ τ_p}
                  {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
                → MinAnaPos Cls υ → AnaPosSlice Cls υ

  data MinAna where

    min□      : ∀ {n Γ₀ C n_f Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]}
              → MinAna Cls ⊥ₛ

    minSλ:    : ∀ {n Γ n_f Γ' τ₁ C τ₂ τ}
                  {wf : n ⊢wf τ₁}
                  {Cls' : n , (τ₁ ∷ Γ) ⊢ C at synPos τ₂ ▷ n_f , Γ' [ ⇐mode τ ]}
              → {υ : ⌊ τ ⌋} → (υ₁ : ⌊ τ₁ ⌋)
              → MinAna Cls' υ
              → MinAna (sλ: wf Cls') υ

    minS∘₁    : ∀ {n Γ n_f Γ' C e τ τ₁ τ₂ τ_f}
                  {Cls' : n , Γ ⊢ C at synPos τ ▷ n_f , Γ' [ ⇐mode τ_f ]}
                  {eq : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                  {d₂ : n , Γ ⊢ e ⇓ τ₁}
              → {υ : ⌊ τ_f ⌋}
              → MinAna Cls' υ
              → MinAna (s∘₁ Cls' eq d₂) υ

    minS∘₂    : ∀ {n Γ n_f Γ' e₁ C τ₀ τ₁ τ₂ τ}
                  {D₁ : n , Γ ⊢ e₁ ⇑ τ₀} {eq : τ₀ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                  {Cls' : n , Γ ⊢ C at anaPos τ₁ ▷ n_f , Γ' [ ⇐mode τ ]}
              → {υ : ⌊ τ ⌋}
              → (m : MinAnaPos Cls' υ)
              → (ss : MinSynSlice D₁ ◂ (unmatch⇒-min {τ₀} eq (ana-υ_outer (extract-pos m)) ⊥ₛ))
              → (focus : ⌊ τ ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n_f₁ ] ∃[ Γ_f₁ ]
                  (n , (ss ↓s ↓γ) ⊢ (ana-κ (extract-pos m)) .↓
                     at anaPos ((dom⇒ₛ (SynSlice_◂_.type (ss ↓s)) eq) .↓)
                     ▷ n_f₁ , Γ_f₁
                     [ ⇐mode (focus .↓) ])
              → MinAna (s∘₂ D₁ eq Cls') υ

    minS<>₁   : ∀ {n Γ n_f Γ' C τ_inner τ_fa σ τ}
                  {Cls' : n , Γ ⊢ C at synPos τ_inner ▷ n_f , Γ' [ ⇐mode τ ]}
                  {eq : τ_inner ⊔ ∀· □ ≡ ∀· τ_fa}
                  {wf : n ⊢wf σ}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (s<>₁ Cls' eq wf) υ

    minS&₁    : ∀ {n Γ n_f Γ' C e τ₁ τ₂ τ}
                  {Cls' : n , Γ ⊢ C at synPos τ₁ ▷ n_f , Γ' [ ⇐mode τ ]}
                  {d₂ : n , Γ ⊢ e ⇑ τ₂}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (s&₁ Cls' d₂) υ

    minS&₂    : ∀ {n Γ n_f Γ' C e τ₁ τ₂ τ}
                  {d₁ : n , Γ ⊢ e ⇑ τ₁}
                  {Cls' : n , Γ ⊢ C at synPos τ₂ ▷ n_f , Γ' [ ⇐mode τ ]}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (s&₂ d₁ Cls') υ

    minScase₁ : ∀ {n Γ n_f Γ' e C e' τ₀ τ₁ τ₂ τ₁' τ₂' τ}
                  {D : n , Γ ⊢ e ⇑ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {Cls' : n , (τ₁ ∷ Γ) ⊢ C at synPos τ₁' ▷ n_f , Γ' [ ⇐mode τ ]}
                  {d₂ : n , (τ₂ ∷ Γ) ⊢ e' ⇑ τ₂'}
                  {con : τ₁' ~ τ₂'}
              → {υ : ⌊ τ ⌋}
              → (m : MinAna Cls' υ)
              → (ss : MinSynSlice D ◂ (unmatch+-min {τ₀} eq (hdₛ (extract m .γ)) ⊥ₛ))
              → (typ : ⌊ τ₁' ⌋)
              → (focus : ⌊ τ ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n-f' ] ∃[ Γ-f' ]
                  (n , ((fst+ₛ' (SynSlice_◂_.type (ss ↓s)) eq) .↓ ∷ (ss ↓s ↓γ))
                     ⊢ (extract m .κ) .↓
                     at synPos (typ .↓) ▷ n-f' , Γ-f'
                     [ ⇐mode (focus .↓) ])
              → MinAna (scase₁ D eq Cls' d₂ con) υ

    minScase₂ : ∀ {n Γ n_f Γ' e e' C τ₀ τ₁ τ₂ τ₁' τ₂' τ}
                  {D : n , Γ ⊢ e ⇑ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {d₁ : n , (τ₁ ∷ Γ) ⊢ e' ⇑ τ₁'}
                  {Cls' : n , (τ₂ ∷ Γ) ⊢ C at synPos τ₂' ▷ n_f , Γ' [ ⇐mode τ ]}
                  {con : τ₁' ~ τ₂'}
              → {υ : ⌊ τ ⌋}
              → (m : MinAna Cls' υ)
              → (ss : MinSynSlice D ◂ (unmatch+-min {τ₀} eq ⊥ₛ (hdₛ (extract m .γ))))
              → (typ : ⌊ τ₂' ⌋)
              → (focus : ⌊ τ ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n-f' ] ∃[ Γ-f' ]
                  (n , ((snd+ₛ' (SynSlice_◂_.type (ss ↓s)) eq) .↓ ∷ (ss ↓s ↓γ))
                     ⊢ (extract m .κ) .↓
                     at synPos (typ .↓) ▷ n-f' , Γ-f'
                     [ ⇐mode (focus .↓) ])
              → MinAna (scase₂ D eq d₁ Cls' con) υ

    minSι₁    : ∀ {n Γ n_f Γ' C τ_inner τ}
                  {Cls' : n , Γ ⊢ C at synPos τ_inner ▷ n_f , Γ' [ ⇐mode τ ]}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (sι₁ Cls') υ

    minSι₂    : ∀ {n Γ n_f Γ' C τ_inner τ}
                  {Cls' : n , Γ ⊢ C at synPos τ_inner ▷ n_f , Γ' [ ⇐mode τ ]}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (sι₂ Cls') υ

    minSπ₁    : ∀ {n Γ n_f Γ' C τ_inner τ₁ τ₂ τ}
                  {Cls' : n , Γ ⊢ C at synPos τ_inner ▷ n_f , Γ' [ ⇐mode τ ]}
                  {eq : τ_inner ⊔ □ × □ ≡ τ₁ × τ₂}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (sπ₁ Cls' eq) υ

    minSπ₂    : ∀ {n Γ n_f Γ' C τ_inner τ₁ τ₂ τ}
                  {Cls' : n , Γ ⊢ C at synPos τ_inner ▷ n_f , Γ' [ ⇐mode τ ]}
                  {eq : τ_inner ⊔ □ × □ ≡ τ₁ × τ₂}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (sπ₂ Cls' eq) υ

    minSΛ     : ∀ {n Γ n_f Γ' C τ_body τ}
                  {Cls' : suc n , shiftΓ (suc zero) Γ ⊢ C at synPos τ_body ▷ n_f , Γ' [ ⇐mode τ ]}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAna (sΛ Cls') υ

    minSdef₁  : ∀ {n Γ n_f Γ' C e τ' τ_body τ}
                  {Cls' : n , Γ ⊢ C at synPos τ' ▷ n_f , Γ' [ ⇐mode τ_body ]}
                  {d₂ : n , (τ' ∷ Γ) ⊢ e ⇑ τ}
              → {υ : ⌊ τ_body ⌋}
              → MinAna Cls' υ
              → MinAna (sdef₁ Cls' d₂) υ

    minSdef₂  : ∀ {n Γ n_f Γ' e C τ' τ_body τ}
                  {D : n , Γ ⊢ e ⇑ τ'}
                  {Cls' : n , (τ' ∷ Γ) ⊢ C at synPos τ_body ▷ n_f , Γ' [ ⇐mode τ ]}
              → {υ : ⌊ τ ⌋}
              → (m : MinAna Cls' υ)
              → (ss : MinSynSlice D ◂ (hdₛ (extract m .γ)))
              → (typ : ⌊ τ_body ⌋)
              → (focus : ⌊ τ ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n-f' ] ∃[ Γ-f' ]
                  (n , (SynSlice_◂_.type (ss ↓s) .↓ ∷ (ss ↓s ↓γ))
                     ⊢ (extract m .κ) .↓
                     at synPos (typ .↓) ▷ n-f' , Γ-f'
                     [ ⇐mode (focus .↓) ])
              → MinAna (sdef₂ D Cls') υ

  data MinAnaPos where

    min□Pos   : ∀ {n Γ₀ C n_f Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]}
              → MinAnaPos Cls ⊥ₛ

    minA○     : ∀ {n Γ τ}
              → (υ : ⌊ τ ⌋)
              → MinAnaPos (a○ {n = n} {Γ = Γ} {τ = τ}) υ

    minASub   : ∀ {n Γ n_f Γ' C τ₀ τ' τ}
                  {Cls' : n , Γ ⊢ C at synPos τ' ▷ n_f , Γ' [ ⇐mode τ ]}
                  {con : τ₀ ~ τ'}
              → {υ : ⌊ τ ⌋}
              → MinAna Cls' υ
              → MinAnaPos (aSub {τ = τ₀} Cls' con) υ

    minAλ:    : ∀ {n Γ n_f Γ' C τ τ₁ τ₁' τ₂ τ'}
                  {c : τ ~ τ₁ ⇒ □} {eq : τ ⊔ τ₁ ⇒ □ ≡ τ₁' ⇒ τ₂}
                  {wf : n ⊢wf τ₁}
                  {Cls' : n , (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ n_f , Γ' [ ⇐mode τ' ]}
              → {υ : ⌊ τ' ⌋}
              → (m : MinAnaPos Cls' υ)
              → (outer-υ : ⌊ τ ⌋)
              → (outer-υ .↓ ~ (hdₛ (ana-γ (extract-pos m))) .↓ ⇒ □)
              → (outer-υ .↓ ⊔ (hdₛ (ana-γ (extract-pos m))) .↓ ⇒ □
                   ≡ (hdₛ (ana-γ (extract-pos m))) .↓ ⇒ (ana-υ_outer (extract-pos m)) .↓)
              -- outer-υ is the minimum among valid alternatives. Provided by
              -- AnaSlicing via ⊔-ann-⇒-⊑-intro-min, used by Minimality.
              → (∀ {υ' τ_s τ_s' τ_b'}
                  → τ_s ⊑t (hdₛ (ana-γ (extract-pos m))) .↓
                  → υ' ⊔ τ_s ⇒ □ ≡ τ_s' ⇒ τ_b'
                  → (ana-υ_outer (extract-pos m)) .↓ ⊑t τ_b'
                  → outer-υ .↓ ⊑t υ')
              → MinAnaPos (aλ: c eq wf Cls') υ

    minAλ⇒    : ∀ {n Γ n_f Γ' C τ τ₁ τ₂ τ'}
                  {eq : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                  {Cls' : n , (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ n_f , Γ' [ ⇐mode τ' ]}
              → {υ : ⌊ τ' ⌋}
              → MinAnaPos Cls' υ
              → MinAnaPos (aλ⇒ {τ = τ} eq Cls') υ

    minA&₁    : ∀ {n Γ n_f Γ' C e τ τ₁ τ₂ τf}
                  {eq : τ ⊔ □ × □ ≡ τ₁ × τ₂}
                  {Cls' : n , Γ ⊢ C at anaPos τ₁ ▷ n_f , Γ' [ ⇐mode τf ]}
                  {d₂ : n , Γ ⊢ e ⇓ τ₂}
              → {υ : ⌊ τf ⌋}
              → MinAnaPos Cls' υ
              → MinAnaPos (a&₁ {τ = τ} eq Cls' d₂) υ

    minA&₂    : ∀ {n Γ n_f Γ' C e τ τ₁ τ₂ τ'}
                  {eq : τ ⊔ □ × □ ≡ τ₁ × τ₂}
                  {d₁ : n , Γ ⊢ e ⇓ τ₁}
                  {Cls' : n , Γ ⊢ C at anaPos τ₂ ▷ n_f , Γ' [ ⇐mode τ' ]}
              → {υ : ⌊ τ' ⌋}
              → MinAnaPos Cls' υ
              → MinAnaPos (a&₂ {τ = τ} eq d₁ Cls') υ

    minAι₁    : ∀ {n Γ n_f Γ' C τ τ₁ τ₂ τ'}
                  {eq : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {Cls' : n , Γ ⊢ C at anaPos τ₁ ▷ n_f , Γ' [ ⇐mode τ' ]}
              → {υ : ⌊ τ' ⌋}
              → MinAnaPos Cls' υ
              → MinAnaPos (aι₁ {τ = τ} eq Cls') υ

    minAι₂    : ∀ {n Γ n_f Γ' C τ τ₁ τ₂ τ'}
                  {eq : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {Cls' : n , Γ ⊢ C at anaPos τ₂ ▷ n_f , Γ' [ ⇐mode τ' ]}
              → {υ : ⌊ τ' ⌋}
              → MinAnaPos Cls' υ
              → MinAnaPos (aι₂ {τ = τ} eq Cls') υ

    minAcase₁ : ∀ {n Γ n_f Γ' e C e' τ τ₀ τ₁ τ₂ τ'}
                  {D : n , Γ ⊢ e ⇑ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {Cls' : n , (τ₁ ∷ Γ) ⊢ C at anaPos τ ▷ n_f , Γ' [ ⇐mode τ' ]}
                  {d₂ : n , (τ₂ ∷ Γ) ⊢ e' ⇓ τ}
              → {υ : ⌊ τ' ⌋}
              → (m : MinAnaPos Cls' υ)
              → (ss : MinSynSlice D ◂ (unmatch+-min {τ₀} eq (hdₛ (ana-γ (extract-pos m))) ⊥ₛ))
              → (focus : ⌊ τ' ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n-f' ] ∃[ Γ-f' ]
                  (n , ((fst+ₛ' (SynSlice_◂_.type (ss ↓s)) eq) .↓ ∷ (ss ↓s ↓γ))
                     ⊢ (ana-κ (extract-pos m)) .↓
                     at anaPos ((ana-υ_outer (extract-pos m)) .↓) ▷ n-f' , Γ-f'
                     [ ⇐mode (focus .↓) ])
              → MinAnaPos (acase₁ D eq Cls' d₂) υ

    minAcase₂ : ∀ {n Γ n_f Γ' e e' C τ τ₀ τ₁ τ₂ τ'}
                  {D : n , Γ ⊢ e ⇑ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {d₁ : n , (τ₁ ∷ Γ) ⊢ e' ⇓ τ}
                  {Cls' : n , (τ₂ ∷ Γ) ⊢ C at anaPos τ ▷ n_f , Γ' [ ⇐mode τ' ]}
              → {υ : ⌊ τ' ⌋}
              → (m : MinAnaPos Cls' υ)
              → (ss : MinSynSlice D ◂ (unmatch+-min {τ₀} eq ⊥ₛ (hdₛ (ana-γ (extract-pos m)))))
              → (focus : ⌊ τ' ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n-f' ] ∃[ Γ-f' ]
                  (n , ((snd+ₛ' (SynSlice_◂_.type (ss ↓s)) eq) .↓ ∷ (ss ↓s ↓γ))
                     ⊢ (ana-κ (extract-pos m)) .↓
                     at anaPos ((ana-υ_outer (extract-pos m)) .↓) ▷ n-f' , Γ-f'
                     [ ⇐mode (focus .↓) ])
              → MinAnaPos (acase₂ D eq d₁ Cls') υ

    minAdef₁  : ∀ {n Γ n_f Γ' C e τ τ' τ''}
                  {Cls' : n , Γ ⊢ C at synPos τ' ▷ n_f , Γ' [ ⇐mode τ'' ]}
                  {d₂ : n , (τ' ∷ Γ) ⊢ e ⇓ τ}
              → {υ : ⌊ τ'' ⌋}
              → MinAna Cls' υ
              → MinAnaPos (adef₁ Cls' d₂) υ

    minAdef₂  : ∀ {n Γ n_f Γ' e C τ τ' τ''}
                  {D : n , Γ ⊢ e ⇑ τ'}
                  {Cls' : n , (τ' ∷ Γ) ⊢ C at anaPos τ ▷ n_f , Γ' [ ⇐mode τ'' ]}
              → {υ : ⌊ τ'' ⌋}
              → (m : MinAnaPos Cls' υ)
              → (ss : MinSynSlice D ◂ (hdₛ (ana-γ (extract-pos m))))
              → (focus : ⌊ τ'' ⌋)
              → (υ ⊑ₛ focus)
              → ∃[ n-f' ] ∃[ Γ-f' ]
                  (n , (SynSlice_◂_.type (ss ↓s) .↓ ∷ (ss ↓s ↓γ))
                     ⊢ (ana-κ (extract-pos m)) .↓
                     at anaPos ((ana-υ_outer (extract-pos m)) .↓) ▷ n-f' , Γ-f'
                     [ ⇐mode (focus .↓) ])
              → MinAnaPos (adef₂ D Cls') υ

  extract : ∀ {n Γ₀ C n_f Γ τ τ_p}
              {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
            → MinAna Cls υ → AnaSlice Cls υ

  extract min□ = ⊥-ana

  extract (minSλ: {n = n} {wf = wf} υ₁ m) =
    let inner = extract m
        hd-slice = hdₛ (inner .γ)
        tl-slice = tlₛ (inner .γ)
        hd⊑ = hd-slice .proof
        n_f , Γ_f , inner-cls = inner .valid
        inner-cls-decomp =
          subst (λ x → n , x ⊢ inner .κ .↓ at synPos (inner .type .↓)
                          ▷ n_f , Γ_f [ ⇐mode (inner .focus .↓) ])
                (cons-decompₛ (inner .γ)) inner-cls
    in record
         { κ      = (λ: _ ⇒ inner .κ .↓) isSlice ⊑λ hd⊑ (inner .κ .proof)
         ; γ      = tl-slice
         ; type   = hd-slice ⇒ₛ inner .type
         ; focus  = inner .focus
         ; focus⊒ = inner .focus⊒
         ; valid  = _ , _ , sλ: (wf-⊑ wf hd⊑) inner-cls-decomp
         }
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
         ; valid  = _ , _ , s∘₁ inner-cls (match⇒ₛ ψ eq) (⇓Sub ⇑□ ~?₁)
         }
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
         ; valid  = _ , _ , s&₁ inner-cls ⇑□
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
         ; valid  = _ , _ , s&₂ ⇑□ inner-cls
         }
  extract (minScase₁ {n = n} {eq = eq} {con = con} m ss typ focus focus⊒ (n-f' , Γ-f' , Cls-lifted)) =
    let inner = extract m
        fn = ss ↓s
        ψ = SynSlice_◂_.type fn
    in record
         { κ      = (case (fn ↓σ) of (inner .κ .↓) ·₁ □) isSlice
                      ⊑case₁ (fn ↓σ⊑) (inner .κ .proof) ⊑□
         ; γ      = fn ↓γₛ
         ; type   = _⊔~ₛ_ typ ⊥ₛ {c = con}
         ; focus  = focus
         ; focus⊒ = focus⊒
         ; valid  = n-f' , Γ-f' , scase₁ (SynSlice_◂_.syn fn) (match+ₛ ψ eq) Cls-lifted ⇑□ ~?₁
         }
  extract (minScase₂ {n = n} {eq = eq} {con = con} m ss typ focus focus⊒ (n-f' , Γ-f' , Cls-lifted)) =
    let inner = extract m
        fn = ss ↓s
        ψ = SynSlice_◂_.type fn
    in record
         { κ      = (case (fn ↓σ) of₂ □ · (inner .κ .↓)) isSlice
                      ⊑case₂ (fn ↓σ⊑) ⊑□ (inner .κ .proof)
         ; γ      = fn ↓γₛ
         ; type   = _⊔~ₛ_ ⊥ₛ typ {c = con}
         ; focus  = focus
         ; focus⊒ = focus⊒
         ; valid  = n-f' , Γ-f' , scase₂ (SynSlice_◂_.syn fn) (match+ₛ ψ eq) ⇑□ Cls-lifted ~?₂
         }
  extract (minSι₁ m) =
    let inner = extract m
        _ , _ , inner-cls = inner .valid
    in record
         { κ      = (ι₁ (inner .κ .↓)) isSlice ⊑ι₁ (inner .κ .proof)
         ; γ      = inner .γ
         ; type   = (inner .type) +ₛ ⊥ₛ
         ; focus  = inner .focus
         ; focus⊒ = inner .focus⊒
         ; valid  = _ , _ , sι₁ inner-cls
         }
  extract (minSι₂ m) =
    let inner = extract m
        _ , _ , inner-cls = inner .valid
    in record
         { κ      = (ι₂ (inner .κ .↓)) isSlice ⊑ι₂ (inner .κ .proof)
         ; γ      = inner .γ
         ; type   = ⊥ₛ +ₛ (inner .type)
         ; focus  = inner .focus
         ; focus⊒ = inner .focus⊒
         ; valid  = _ , _ , sι₂ inner-cls
         }
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
  extract (minSΛ {n = n} {υ = υ} m) =
    let inner = extract m
        γ-eq = shift-unshiftΓ (inner .γ .↓) (inner .γ .proof)
        n_f , Γ_f , inner-cls = inner .valid
        inner-cls' = subst (λ x → suc n , x ⊢ (inner .κ .↓) at synPos (inner .type .↓)
                                                 ▷ n_f , Γ_f [ ⇐mode (inner .focus .↓) ])
                           (sym γ-eq) inner-cls
    in record
         { κ      = (Λ (inner .κ .↓)) isSlice ⊑Λ (inner .κ .proof)
         ; γ      = unshiftΓₛ (inner .γ)
         ; type   = ∀·ₛ (inner .type)
         ; focus  = inner .focus
         ; focus⊒ = inner .focus⊒
         ; valid  = n_f , Γ_f , sΛ inner-cls'
         }
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
         ; valid  = _ , _ , sdef₁ inner-cls ⇑□
         }
  extract (minSdef₂ {n = n} m ss typ focus focus⊒ (n-f' , Γ-f' , Cls-lifted)) =
    let inner = extract m
        fn = ss ↓s
    in record
         { κ      = (def (fn ↓σ) ⊢₂ (inner .κ .↓)) isSlice
                      ⊑def₂ (fn ↓σ⊑) (inner .κ .proof)
         ; γ      = fn ↓γₛ
         ; type   = typ
         ; focus  = focus
         ; focus⊒ = focus⊒
         ; valid  = n-f' , Γ-f' , sdef₂ (SynSlice_◂_.syn fn) Cls-lifted
         }

  extract-pos min□Pos = ⊥-ana-pos

  extract-pos (minA○ {τ = τ} υ) = record
    { κ       = ⊥ₛ
    ; γ       = ⊥ₛ
    ; υ_outer = υ
    ; focus   = υ
    ; focus⊒  = ⊑ₛ.refl {A = Typ} {x = υ}
    ; valid   = _ , _ , a○
    }

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

  extract-pos {n = n} (minAλ: {wf = wf} m outer-υ c-lifted eq-lifted _) =
    let inner = extract-pos m
        hd⊑ = hdₛ (ana-γ inner) .proof
        n_f , Γ_f , inner-cls = ana-valid inner
        inner-cls-decomp =
          subst (λ x → n , x ⊢ (ana-κ inner .↓) at anaPos (ana-υ_outer inner .↓)
                          ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ])
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
          subst (λ x → n , x ⊢ (ana-κ inner .↓) at anaPos (ana-υ_outer inner .↓)
                          ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ])
                (cons-decompₛ (ana-γ inner)) inner-cls
        inner-cls-1 : n , (hd .↓ ∷ tl .↓) ⊢ (ana-κ inner .↓)
                            at anaPos ((cod⇒ₛ outer-υ eq) .↓) ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ]
        inner-cls-1 = subst (λ x → n , (hd .↓ ∷ tl .↓) ⊢ (ana-κ inner .↓)
                                          at anaPos x ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ])
                            υ-cod≡cod inner-cls-decomp
        inner-cls-2 : n , ((dom⇒ₛ outer-υ eq) .↓ ∷ tl .↓) ⊢ (ana-κ inner .↓)
                            at anaPos ((cod⇒ₛ outer-υ eq) .↓) ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ]
        inner-cls-2 = subst (λ x → n , (x ∷ tl .↓) ⊢ (ana-κ inner .↓)
                                          at anaPos ((cod⇒ₛ outer-υ eq) .↓)
                                          ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ])
                            hd≡dom inner-cls-1
    in record
         { κ       = (λ⇒ (ana-κ inner .↓)) isSlice ⊑λu (ana-κ inner .proof)
         ; γ       = tl
         ; υ_outer = outer-υ
         ; focus   = ana-focus inner
         ; focus⊒  = ana-focus⊒ inner
         ; valid   = n_f , Γ_f , aλ⇒ match-eq inner-cls-2
         }
  extract-pos {n = n} {υ = υ} (minA&₁ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} m) =
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
        inner-cls' : n , (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                            at anaPos ((fst×ₛ' outer-υ eq) .↓) ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ]
        inner-cls' = subst (λ x → n , (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                                          at anaPos x ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ])
                           υ-fst≡fst inner-cls
    in record
         { κ       = ((ana-κ inner .↓) &₁ □) isSlice
                       ⊑&₁ (ana-κ inner .proof) ⊑□
         ; γ       = ana-γ inner
         ; υ_outer = outer-υ
         ; focus   = ana-focus inner
         ; focus⊒  = ana-focus⊒ inner
         ; valid   = n_f , Γ_f , a&₁ match-eq inner-cls' (⇓Sub ⇑□ ~?₁)
         }
  extract-pos {n = n} {υ = υ} (minA&₂ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} m) =
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
        inner-cls' : n , (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                            at anaPos ((snd×ₛ outer-υ eq) .↓) ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ]
        inner-cls' = subst (λ x → n , (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                                          at anaPos x ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ])
                           υ-snd≡snd inner-cls
    in record
         { κ       = (□ &₂ (ana-κ inner .↓)) isSlice
                       ⊑&₂ ⊑□ (ana-κ inner .proof)
         ; γ       = ana-γ inner
         ; υ_outer = outer-υ
         ; focus   = ana-focus inner
         ; focus⊒  = ana-focus⊒ inner
         ; valid   = n_f , Γ_f , a&₂ match-eq (⇓Sub ⇑□ ~?₁) inner-cls'
         }
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
        inner-cls' : n , (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                            at anaPos ((fst+ₛ' outer-υ eq) .↓) ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ]
        inner-cls' = subst (λ x → n , (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                                          at anaPos x ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ])
                           υ-fst≡fst inner-cls
    in record
         { κ       = (ι₁ (ana-κ inner .↓)) isSlice ⊑ι₁ (ana-κ inner .proof)
         ; γ       = ana-γ inner
         ; υ_outer = outer-υ
         ; focus   = ana-focus inner
         ; focus⊒  = ana-focus⊒ inner
         ; valid   = n_f , Γ_f , aι₁ match-eq inner-cls'
         }
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
        inner-cls' : n , (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                            at anaPos ((snd+ₛ' outer-υ eq) .↓) ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ]
        inner-cls' = subst (λ x → n , (ana-γ inner .↓) ⊢ (ana-κ inner .↓)
                                          at anaPos x ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ])
                           υ-snd≡snd inner-cls
    in record
         { κ       = (ι₂ (ana-κ inner .↓)) isSlice ⊑ι₂ (ana-κ inner .proof)
         ; γ       = ana-γ inner
         ; υ_outer = outer-υ
         ; focus   = ana-focus inner
         ; focus⊒  = ana-focus⊒ inner
         ; valid   = n_f , Γ_f , aι₂ match-eq inner-cls'
         }
  extract-pos (minAcase₁ {eq = eq} m ss focus focus⊒ (n-f' , Γ-f' , Cls-lifted)) =
    let inner = extract-pos m
        fn = ss ↓s
        ψ = SynSlice_◂_.type fn
    in record
         { κ       = (case (fn ↓σ) of (ana-κ inner .↓) ·₁ □) isSlice
                       ⊑case₁ (fn ↓σ⊑) (ana-κ inner .proof) ⊑□
         ; γ       = fn ↓γₛ
         ; υ_outer = ana-υ_outer inner
         ; focus   = focus
         ; focus⊒  = focus⊒
         ; valid   = n-f' , Γ-f' , acase₁ (SynSlice_◂_.syn fn) (match+ₛ ψ eq)
                                            Cls-lifted (⇓Sub ⇑□ ~?₁)
         }
  extract-pos (minAcase₂ {eq = eq} m ss focus focus⊒ (n-f' , Γ-f' , Cls-lifted)) =
    let inner = extract-pos m
        fn = ss ↓s
        ψ = SynSlice_◂_.type fn
    in record
         { κ       = (case (fn ↓σ) of₂ □ · (ana-κ inner .↓)) isSlice
                       ⊑case₂ (fn ↓σ⊑) ⊑□ (ana-κ inner .proof)
         ; γ       = fn ↓γₛ
         ; υ_outer = ana-υ_outer inner
         ; focus   = focus
         ; focus⊒  = focus⊒
         ; valid   = n-f' , Γ-f' , acase₂ (SynSlice_◂_.syn fn) (match+ₛ ψ eq)
                                            (⇓Sub ⇑□ ~?₁) Cls-lifted
         }
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
         ; valid   = _ , _ , adef₁ inner-cls (⇓Sub ⇑□ ~?₁)
         }
  extract-pos {n = n} (minAdef₂ m ss focus focus⊒ (n-f' , Γ-f' , Cls-lifted)) =
    let inner = extract-pos m
        fn = ss ↓s
    in record
         { κ       = (def (fn ↓σ) ⊢₂ (ana-κ inner .↓)) isSlice
                       ⊑def₂ (fn ↓σ⊑) (ana-κ inner .proof)
         ; γ       = fn ↓γₛ
         ; υ_outer = ana-υ_outer inner
         ; focus   = focus
         ; focus⊒  = focus⊒
         ; valid   = n-f' , Γ-f' , adef₂ (SynSlice_◂_.syn fn) Cls-lifted
         }

-- Direct-mode projectors mirroring extract / extract-pos without with-blocking.
mutual

  ana-υ_outer-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                       {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
                     → MinAnaPos Cls υ → ⌊ τ_p ⌋

  ana-γ-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                 {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
               → MinAnaPos Cls υ → ⌊ Γ₀ ⌋

  ana-κ-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                 {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
               → MinAnaPos Cls υ → ⌊ C ⌋

  ana-focus-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                     {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
                   → MinAnaPos Cls υ → ⌊ τ ⌋

  syn-γ-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                 {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
               → MinAna Cls υ → ⌊ Γ₀ ⌋

  syn-κ-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                 {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
               → MinAna Cls υ → ⌊ C ⌋

  syn-focus-of-m : ∀ {n Γ₀ C n_f Γ τ τ_p}
                     {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
                   → MinAna Cls υ → ⌊ τ ⌋

  -- ana-υ_outer-of-m: the outer-analysis-type slice tracked by MinAnaPos.
  ana-υ_outer-of-m min□Pos                     = ⊥ₛ
  ana-υ_outer-of-m (minA○ υ)                   = υ
  ana-υ_outer-of-m (minASub _)                 = ⊥ₛ
  ana-υ_outer-of-m (minAλ: _ outer-υ _ _ _)    = outer-υ
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
  ana-υ_outer-of-m (minAcase₁ m _ _ _ _)   = ana-υ_outer-of-m m
  ana-υ_outer-of-m (minAcase₂ m _ _ _ _)   = ana-υ_outer-of-m m
  ana-υ_outer-of-m (minAdef₁ _)                = ⊥ₛ
  ana-υ_outer-of-m (minAdef₂ m _ _ _ _)          = ana-υ_outer-of-m m

  -- ana-γ-of-m: slice of the outer assumptions Γ₀.
  ana-γ-of-m min□Pos                       = ⊥ₛ
  ana-γ-of-m (minA○ _)                     = ⊥ₛ
  ana-γ-of-m (minASub m)                   = syn-γ-of-m m
  ana-γ-of-m (minAλ: m _ _ _ _) = tlₛ (ana-γ-of-m m)
  ana-γ-of-m (minAλ⇒ m)                    = tlₛ (ana-γ-of-m m)
  ana-γ-of-m (minA&₁ m)                    = ana-γ-of-m m
  ana-γ-of-m (minA&₂ m)                    = ana-γ-of-m m
  ana-γ-of-m (minAι₁ m)                    = ana-γ-of-m m
  ana-γ-of-m (minAι₂ m)                    = ana-γ-of-m m
  ana-γ-of-m (minAcase₁ _ ss _ _ _)        = ss ↓s ↓γₛ
  ana-γ-of-m (minAcase₂ _ ss _ _ _)        = ss ↓s ↓γₛ
  ana-γ-of-m (minAdef₁ m)                  = syn-γ-of-m m
  ana-γ-of-m (minAdef₂ _ ss _ _ _)             = ss ↓s ↓γₛ

  -- ana-κ-of-m: slice of the surrounding context C.
  ana-κ-of-m min□Pos                       = ⊥ₛ
  ana-κ-of-m (minA○ _)                     = ⊥ₛ
  ana-κ-of-m (minASub m)                   = syn-κ-of-m m
  ana-κ-of-m (minAλ: m _ _ _ _) =
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
  ana-κ-of-m (minAcase₁ m ss _ _ _)        =
    (case (ss ↓s ↓σ) of (ana-κ-of-m m .↓) ·₁ □) isSlice
      ⊑case₁ (ss ↓s ↓σ⊑) (ana-κ-of-m m .proof) ⊑□
  ana-κ-of-m (minAcase₂ m ss _ _ _)        =
    (case (ss ↓s ↓σ) of₂ □ · (ana-κ-of-m m .↓)) isSlice
      ⊑case₂ (ss ↓s ↓σ⊑) ⊑□ (ana-κ-of-m m .proof)
  ana-κ-of-m (minAdef₁ m)                  =
    (def (syn-κ-of-m m .↓) ⊢₁ _) isSlice ⊑def₁ (syn-κ-of-m m .proof) (⊑.refl {A = Exp})
  ana-κ-of-m (minAdef₂ m ss _ _ _)             =
    (def (ss ↓s ↓σ) ⊢₂ (ana-κ-of-m m .↓)) isSlice ⊑def₂ (ss ↓s ↓σ⊑) (ana-κ-of-m m .proof)

  -- ana-focus-of-m: slice of the focus type τ. Propagates unchanged through
  -- structural rules; equals υ at leaves and ⊥ at the bottom slice.
  ana-focus-of-m min□Pos                   = ⊥ₛ
  ana-focus-of-m (minA○ υ)                 = υ
  ana-focus-of-m (minASub m)               = syn-focus-of-m m
  ana-focus-of-m (minAλ: m _ _ _ _) = ana-focus-of-m m
  ana-focus-of-m (minAλ⇒ m)                = ana-focus-of-m m
  ana-focus-of-m (minA&₁ m)                = ana-focus-of-m m
  ana-focus-of-m (minA&₂ m)                = ana-focus-of-m m
  ana-focus-of-m (minAι₁ m)                = ana-focus-of-m m
  ana-focus-of-m (minAι₂ m)                = ana-focus-of-m m
  ana-focus-of-m (minAcase₁ _ _ focus _ _) = focus
  ana-focus-of-m (minAcase₂ _ _ focus _ _) = focus
  ana-focus-of-m (minAdef₁ m)              = syn-focus-of-m m
  ana-focus-of-m (minAdef₂ _ _ focus _ _)  = focus

  -- syn-γ-of-m: slice of the outer Γ₀ for MinAna (synPos position).
  syn-γ-of-m min□                          = ⊥ₛ
  syn-γ-of-m (minSλ: _ m)                  = tlₛ (syn-γ-of-m m)
  syn-γ-of-m (minS∘₁ m)                    = syn-γ-of-m m
  syn-γ-of-m (minS∘₂ _ ss _ _ _)           = ss ↓s ↓γₛ
  syn-γ-of-m (minS<>₁ m)                   = syn-γ-of-m m
  syn-γ-of-m (minS&₁ m)                    = syn-γ-of-m m
  syn-γ-of-m (minS&₂ m)                    = syn-γ-of-m m
  syn-γ-of-m (minScase₁ _ ss _ _ _ _)      = ss ↓s ↓γₛ
  syn-γ-of-m (minScase₂ _ ss _ _ _ _)      = ss ↓s ↓γₛ
  syn-γ-of-m (minSι₁ m)                    = syn-γ-of-m m
  syn-γ-of-m (minSι₂ m)                    = syn-γ-of-m m
  syn-γ-of-m (minSπ₁ m)                    = syn-γ-of-m m
  syn-γ-of-m (minSπ₂ m)                    = syn-γ-of-m m
  syn-γ-of-m (minSΛ m)                     = unshiftΓₛ (syn-γ-of-m m)
  syn-γ-of-m (minSdef₁ m)                  = syn-γ-of-m m
  syn-γ-of-m (minSdef₂ _ ss _ _ _ _)       = ss ↓s ↓γₛ

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
  syn-κ-of-m (minScase₁ m ss _ _ _ _) =
    (case (ss ↓s ↓σ) of (syn-κ-of-m m .↓) ·₁ _) isSlice
      ⊑case₁ (ss ↓s ↓σ⊑) (syn-κ-of-m m .proof) (⊑.refl {A = Exp})
  syn-κ-of-m (minScase₂ m ss _ _ _ _) =
    (case (ss ↓s ↓σ) of₂ _ · (syn-κ-of-m m .↓)) isSlice
      ⊑case₂ (ss ↓s ↓σ⊑) (⊑.refl {A = Exp}) (syn-κ-of-m m .proof)
  syn-κ-of-m (minSι₁ m)                    =
    (ι₁ (syn-κ-of-m m .↓)) isSlice ⊑ι₁ (syn-κ-of-m m .proof)
  syn-κ-of-m (minSι₂ m)                    =
    (ι₂ (syn-κ-of-m m .↓)) isSlice ⊑ι₂ (syn-κ-of-m m .proof)
  syn-κ-of-m (minSπ₁ m)                    =
    (π₁ (syn-κ-of-m m .↓)) isSlice ⊑π₁ (syn-κ-of-m m .proof)
  syn-κ-of-m (minSπ₂ m)                    =
    (π₂ (syn-κ-of-m m .↓)) isSlice ⊑π₂ (syn-κ-of-m m .proof)
  syn-κ-of-m (minSΛ m)                     =
    (Λ (syn-κ-of-m m .↓)) isSlice ⊑Λ (syn-κ-of-m m .proof)
  syn-κ-of-m (minSdef₁ m)                  =
    (def (syn-κ-of-m m .↓) ⊢₁ _) isSlice ⊑def₁ (syn-κ-of-m m .proof) (⊑.refl {A = Exp})
  syn-κ-of-m (minSdef₂ m ss _ _ _ _)       =
    (def (ss ↓s ↓σ) ⊢₂ (syn-κ-of-m m .↓)) isSlice ⊑def₂ (ss ↓s ↓σ⊑) (syn-κ-of-m m .proof)

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
  syn-focus-of-m (minSι₁ m)                = syn-focus-of-m m
  syn-focus-of-m (minSι₂ m)                = syn-focus-of-m m
  syn-focus-of-m (minSπ₁ m)                = syn-focus-of-m m
  syn-focus-of-m (minSπ₂ m)                = syn-focus-of-m m
  syn-focus-of-m (minSΛ m)                 = syn-focus-of-m m
  syn-focus-of-m (minSdef₁ m)              = syn-focus-of-m m
  syn-focus-of-m (minSdef₂ _ _ _ focus _ _) = focus

-- Equivalence lemmas: extract-pos m's structural fields (γ, υ_outer, focus)
-- equal *-of-m m by structural induction. κ-equivalence does NOT hold in
-- general: extract slices siblings to □ while *-κ-of-m uses refl-identity,
-- so the two κ representations differ syntactically.
mutual
  ana-γ-≡ : ∀ {n Γ₀ C n_f Γ τ τ_p}
              {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
            → (m : MinAnaPos Cls υ)
            → ana-γ (extract-pos m) ≡ ana-γ-of-m m

  ana-υ_outer-≡ : ∀ {n Γ₀ C n_f Γ τ τ_p}
                    {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
                  → (m : MinAnaPos Cls υ)
                  → ana-υ_outer (extract-pos m) ≡ ana-υ_outer-of-m m

  ana-focus-≡ : ∀ {n Γ₀ C n_f Γ τ τ_p}
                  {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
                → (m : MinAnaPos Cls υ)
                → ana-focus (extract-pos m) ≡ ana-focus-of-m m

  syn-γ-≡ : ∀ {n Γ₀ C n_f Γ τ τ_p}
              {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
            → (m : MinAna Cls υ)
            → AnaSlice.γ (extract m) ≡ syn-γ-of-m m

  syn-focus-≡ : ∀ {n Γ₀ C n_f Γ τ τ_p}
                  {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
                → (m : MinAna Cls υ)
                → AnaSlice.focus (extract m) ≡ syn-focus-of-m m

  ana-γ-≡ min□Pos = refl
  ana-γ-≡ (minA○ _) = refl
  ana-γ-≡ (minASub m) = syn-γ-≡ m
  ana-γ-≡ (minAλ: m _ _ _ _) = cong tlₛ (ana-γ-≡ m)
  ana-γ-≡ (minAλ⇒ m) = cong tlₛ (ana-γ-≡ m)
  ana-γ-≡ (minA&₁ m) = ana-γ-≡ m
  ana-γ-≡ (minA&₂ m) = ana-γ-≡ m
  ana-γ-≡ (minAι₁ m) = ana-γ-≡ m
  ana-γ-≡ (minAι₂ m) = ana-γ-≡ m
  ana-γ-≡ (minAcase₁ _ _ _ _ _) = refl
  ana-γ-≡ (minAcase₂ _ _ _ _ _) = refl
  ana-γ-≡ (minAdef₁ m) = syn-γ-≡ m
  ana-γ-≡ (minAdef₂ _ _ _ _ _) = refl

  ana-υ_outer-≡ min□Pos = refl
  ana-υ_outer-≡ (minA○ _) = refl
  ana-υ_outer-≡ (minASub _) = refl
  ana-υ_outer-≡ (minAλ: _ _ _ _ _) = refl
  ana-υ_outer-≡ (minAλ⇒ {eq = eq} m) = cong₂ (λ γ υ → unmatch⇒ eq (hdₛ γ) υ) (ana-γ-≡ m) (ana-υ_outer-≡ m)
  ana-υ_outer-≡ (minA&₁ {eq = eq} m) = cong (λ υ → unmatch× eq υ ⊥ₛ) (ana-υ_outer-≡ m)
  ana-υ_outer-≡ (minA&₂ {eq = eq} m) = cong (λ υ → unmatch× eq ⊥ₛ υ) (ana-υ_outer-≡ m)
  ana-υ_outer-≡ (minAι₁ {eq = eq} m) = cong (λ υ → unmatch+ eq υ ⊥ₛ) (ana-υ_outer-≡ m)
  ana-υ_outer-≡ (minAι₂ {eq = eq} m) = cong (λ υ → unmatch+ eq ⊥ₛ υ) (ana-υ_outer-≡ m)
  ana-υ_outer-≡ (minAcase₁ m _ _ _ _) = ana-υ_outer-≡ m
  ana-υ_outer-≡ (minAcase₂ m _ _ _ _) = ana-υ_outer-≡ m
  ana-υ_outer-≡ (minAdef₁ _) = refl
  ana-υ_outer-≡ (minAdef₂ m _ _ _ _) = ana-υ_outer-≡ m

  ana-focus-≡ min□Pos = refl
  ana-focus-≡ (minA○ _) = refl
  ana-focus-≡ (minASub m) = syn-focus-≡ m
  ana-focus-≡ (minAλ: m _ _ _ _) = ana-focus-≡ m
  ana-focus-≡ (minAλ⇒ m) = ana-focus-≡ m
  ana-focus-≡ (minA&₁ m) = ana-focus-≡ m
  ana-focus-≡ (minA&₂ m) = ana-focus-≡ m
  ana-focus-≡ (minAι₁ m) = ana-focus-≡ m
  ana-focus-≡ (minAι₂ m) = ana-focus-≡ m
  ana-focus-≡ (minAcase₁ _ _ _ _ _) = refl
  ana-focus-≡ (minAcase₂ _ _ _ _ _) = refl
  ana-focus-≡ (minAdef₁ m) = syn-focus-≡ m
  ana-focus-≡ (minAdef₂ _ _ _ _ _) = refl

  syn-γ-≡ min□ = refl
  syn-γ-≡ (minSλ: _ m) = cong tlₛ (syn-γ-≡ m)
  syn-γ-≡ (minS∘₁ m) = syn-γ-≡ m
  syn-γ-≡ (minS∘₂ _ _ _ _ _) = refl
  syn-γ-≡ (minS<>₁ m) = syn-γ-≡ m
  syn-γ-≡ (minS&₁ m) = syn-γ-≡ m
  syn-γ-≡ (minS&₂ m) = syn-γ-≡ m
  syn-γ-≡ (minScase₁ _ _ _ _ _ _) = refl
  syn-γ-≡ (minScase₂ _ _ _ _ _ _) = refl
  syn-γ-≡ (minSι₁ m) = syn-γ-≡ m
  syn-γ-≡ (minSι₂ m) = syn-γ-≡ m
  syn-γ-≡ (minSπ₁ m) = syn-γ-≡ m
  syn-γ-≡ (minSπ₂ m) = syn-γ-≡ m
  syn-γ-≡ (minSΛ m) = cong unshiftΓₛ (syn-γ-≡ m)
  syn-γ-≡ (minSdef₁ m) = syn-γ-≡ m
  syn-γ-≡ (minSdef₂ _ _ _ _ _ _) = refl

  syn-focus-≡ min□ = refl
  syn-focus-≡ (minSλ: _ m) = syn-focus-≡ m
  syn-focus-≡ (minS∘₁ m) = syn-focus-≡ m
  syn-focus-≡ (minS∘₂ _ _ _ _ _) = refl
  syn-focus-≡ (minS<>₁ m) = syn-focus-≡ m
  syn-focus-≡ (minS&₁ m) = syn-focus-≡ m
  syn-focus-≡ (minS&₂ m) = syn-focus-≡ m
  syn-focus-≡ (minScase₁ _ _ _ _ _ _) = refl
  syn-focus-≡ (minScase₂ _ _ _ _ _ _) = refl
  syn-focus-≡ (minSι₁ m) = syn-focus-≡ m
  syn-focus-≡ (minSι₂ m) = syn-focus-≡ m
  syn-focus-≡ (minSπ₁ m) = syn-focus-≡ m
  syn-focus-≡ (minSπ₂ m) = syn-focus-≡ m
  syn-focus-≡ (minSΛ m) = syn-focus-≡ m
  syn-focus-≡ (minSdef₁ m) = syn-focus-≡ m
  syn-focus-≡ (minSdef₂ _ _ _ _ _ _) = refl

-- Completeness: every minimal AnaSlice arises from some MinAna; same
-- for AnaPosSlice. Postulated for now (out of scope for this iteration).
postulate
  complete : ∀ {n Γ₀ C n_f Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
           → (s : AnaSlice Cls υ) → IsMinimal s
           → Σ[ m ∈ MinAna Cls υ ] (extract m) ≈ s
  completePos : ∀ {n Γ₀ C n_f Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
              → (s : AnaPosSlice Cls υ) → IsMinimalPos s
              → Σ[ m ∈ MinAnaPos Cls υ ] (extract-pos m) ≈ s
