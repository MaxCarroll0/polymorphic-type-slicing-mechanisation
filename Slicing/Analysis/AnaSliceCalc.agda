open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.List using (_∷_)
open import Core
open import Core.Typ.Lift using (unmatch⇒-min; unmatch×-min; unmatch+-min; ann-⇒-plain)
open import Semantics.Statics
open import Slicing.Synthesis.FixedAssmsCalc using (_◂_⤳_⇑_⊣_)

-- Minimal analysis slice calculi over context classifications.
-- Cls ◂ υ ⤳ κ ⊣ γ: classification Cls explains focus query υ via context
-- slice κ, using assumption entries γ.  The anaPos form additionally gives
-- υ_outer, the least analysis type the outer context must impose on the
-- sliced focus expression (jointly minimised with κ and γ).
-- Dissertation §8.6; POPL §Calculating Analysis Slices.
module Slicing.Analysis.AnaSliceCalc where

infix 4 _◂_⤳_⊣_
infix 4 _◂_⤳_⇓_⊣_

mutual
  data _◂_⤳_⊣_ {n : ℕ} {Γ₀ : Assms} : ∀ {C n_f Γ τ τ_p}
             → (Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ])
             → ⌊ τ ⌋ → ⌊ C ⌋ → ⌊ Γ₀ ⌋ → Set

  data _◂_⤳_⇓_⊣_ {n : ℕ} {Γ₀ : Assms} : ∀ {C n_f Γ τ τ_p}
             → (Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ])
             → ⌊ τ ⌋ → ⌊ C ⌋ → ⌊ τ_p ⌋ → ⌊ Γ₀ ⌋ → Set

  data _◂_⤳_⊣_ {n} {Γ₀} where

    min□    : ∀ {C n_f Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]}
            → Cls ◂ ⊥ₛ ⤳ ⊥ₛ ⊣ ⊥ₛ

    minSι₁  : ∀ {C n_f Γ' τ_inner τ}
                {Cls' : n , Γ₀ ⊢ C at synPos τ_inner ▷ n_f , Γ' [ ⇐mode τ ]}
                {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⊣ γ
            → sι₁ Cls' ◂ υ ⤳ ι₁ₖ κ ⊣ γ

    minSι₂  : ∀ {C n_f Γ' τ_inner τ}
                {Cls' : n , Γ₀ ⊢ C at synPos τ_inner ▷ n_f , Γ' [ ⇐mode τ ]}
                {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⊣ γ
            → sι₂ Cls' ◂ υ ⤳ ι₂ₖ κ ⊣ γ

    minS&₁  : ∀ {C e n_f Γ' τ₁ τ₂ τ}
                {Cls' : n , Γ₀ ⊢ C at synPos τ₁ ▷ n_f , Γ' [ ⇐mode τ ]}
                {d₂ : n , Γ₀ ⊢ e ⇑ τ₂}
                {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⊣ γ
            → s&₁ Cls' d₂ ◂ υ ⤳ κ &₁ₖ ⊥ₛ ⊣ γ

    minS&₂  : ∀ {e C n_f Γ' τ₁ τ₂ τ}
                {d₁ : n , Γ₀ ⊢ e ⇑ τ₁}
                {Cls' : n , Γ₀ ⊢ C at synPos τ₂ ▷ n_f , Γ' [ ⇐mode τ ]}
                {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⊣ γ
            → s&₂ d₁ Cls' ◂ υ ⤳ ⊥ₛ &₂ₖ κ ⊣ γ

    minSπ₁  : ∀ {C n_f Γ' τ_inner τ₁ τ₂ τ}
                {Cls' : n , Γ₀ ⊢ C at synPos τ_inner ▷ n_f , Γ' [ ⇐mode τ ]}
                {eq : τ_inner ⊔ □ × □ ≡ τ₁ × τ₂}
                {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⊣ γ
            → sπ₁ Cls' eq ◂ υ ⤳ π₁ₖ κ ⊣ γ

    minSπ₂  : ∀ {C n_f Γ' τ_inner τ₁ τ₂ τ}
                {Cls' : n , Γ₀ ⊢ C at synPos τ_inner ▷ n_f , Γ' [ ⇐mode τ ]}
                {eq : τ_inner ⊔ □ × □ ≡ τ₁ × τ₂}
                {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⊣ γ
            → sπ₂ Cls' eq ◂ υ ⤳ π₂ₖ κ ⊣ γ

    minS∘₁  : ∀ {C e n_f Γ' τ τ₁ τ₂ τ_f}
                {Cls' : n , Γ₀ ⊢ C at synPos τ ▷ n_f , Γ' [ ⇐mode τ_f ]}
                {eq : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                {d₂ : n , Γ₀ ⊢ e ⇓ τ₁}
                {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⊣ γ
            → s∘₁ Cls' eq d₂ ◂ υ ⤳ κ ∘₁ₖ ⊥ₛ ⊣ γ

    minS<>₁ : ∀ {C n_f Γ' τ_inner τ_fa σ τ}
                {Cls' : n , Γ₀ ⊢ C at synPos τ_inner ▷ n_f , Γ' [ ⇐mode τ ]}
                {eq : τ_inner ⊔ ∀· □ ≡ ∀· τ_fa}
                {wf : n ⊢wf σ}
                {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⊣ γ
            → s<>₁ Cls' eq wf ◂ υ ⤳ κ <>₁ₖ ⊥ₛ ⊣ γ

  data _◂_⤳_⇓_⊣_ {n} {Γ₀} where

    min□Pos : ∀ {C n_f Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]}
            → Cls ◂ ⊥ₛ ⤳ ⊥ₛ ⇓ ⊥ₛ ⊣ ⊥ₛ

    minA○   : ∀ {τ} (υ : ⌊ τ ⌋)
            → a○ {n = n} {Γ = Γ₀} {τ = τ} ◂ υ ⤳ ○ₖ ⇓ υ ⊣ ⊥ₛ

    minASub : ∀ {C n_f Γ' τ_o τ' τ}
                {Cls' : n , Γ₀ ⊢ C at synPos τ' ▷ n_f , Γ' [ ⇐mode τ ]}
                {con : τ_o ~ τ'}
                {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⊣ γ
            → aSub {τ = τ_o} Cls' con ◂ υ ⤳ κ ⇓ ⊥ₛ ⊣ γ

    minAι₁  : ∀ {C n_f Γ' τ τ₁ τ₂ τ_f}
                {eq : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                {Cls' : n , Γ₀ ⊢ C at anaPos τ₁ ▷ n_f , Γ' [ ⇐mode τ_f ]}
                {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {υ_b : ⌊ τ₁ ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⇓ υ_b ⊣ γ
            → aι₁ eq Cls' ◂ υ ⤳ ι₁ₖ κ ⇓ unmatch+-min {τ} eq υ_b ⊥ₛ ⊣ γ

    minAι₂  : ∀ {C n_f Γ' τ τ₁ τ₂ τ_f}
                {eq : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                {Cls' : n , Γ₀ ⊢ C at anaPos τ₂ ▷ n_f , Γ' [ ⇐mode τ_f ]}
                {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {υ_b : ⌊ τ₂ ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⇓ υ_b ⊣ γ
            → aι₂ eq Cls' ◂ υ ⤳ ι₂ₖ κ ⇓ unmatch+-min {τ} eq ⊥ₛ υ_b ⊣ γ

    minA&₁  : ∀ {C e n_f Γ' τ τ₁ τ₂ τ_f}
                {eq : τ ⊔ □ × □ ≡ τ₁ × τ₂}
                {Cls' : n , Γ₀ ⊢ C at anaPos τ₁ ▷ n_f , Γ' [ ⇐mode τ_f ]}
                {d₂ : n , Γ₀ ⊢ e ⇓ τ₂}
                {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {υ_b : ⌊ τ₁ ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⇓ υ_b ⊣ γ
            → a&₁ eq Cls' d₂ ◂ υ ⤳ κ &₁ₖ ⊥ₛ ⇓ unmatch×-min {τ} eq υ_b ⊥ₛ ⊣ γ

    minA&₂  : ∀ {e C n_f Γ' τ τ₁ τ₂ τ_f}
                {eq : τ ⊔ □ × □ ≡ τ₁ × τ₂}
                {d₁ : n , Γ₀ ⊢ e ⇓ τ₁}
                {Cls' : n , Γ₀ ⊢ C at anaPos τ₂ ▷ n_f , Γ' [ ⇐mode τ_f ]}
                {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {υ_b : ⌊ τ₂ ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⇓ υ_b ⊣ γ
            → a&₂ eq d₁ Cls' ◂ υ ⤳ ⊥ₛ &₂ₖ κ ⇓ unmatch×-min {τ} eq ⊥ₛ υ_b ⊣ γ

