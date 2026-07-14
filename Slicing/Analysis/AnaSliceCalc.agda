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

    minS∘₂  : ∀ {e C n_f Γ' τ₀ τ₁ τ₂ τ}
                {D₁ : n , Γ₀ ⊢ e ⇑ τ₀} {eq : τ₀ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                {Cls' : n , Γ₀ ⊢ C at anaPos τ₁ ▷ n_f , Γ' [ ⇐mode τ ]}
                {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {υ_outer : ⌊ τ₁ ⌋} {γ' : ⌊ Γ₀ ⌋}
                {σ : ⌊ e ⌋} {ψ : ⌊ τ₀ ⌋} {γ₁ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⇓ υ_outer ⊣ γ'
            → D₁ ◂ (unmatch⇒-min {τ₀} eq υ_outer ⊥ₛ) ⤳ σ ⇑ ψ ⊣ γ₁
            → s∘₂ D₁ eq Cls' ◂ υ ⤳ σ ∘₂ₖ κ ⊣ (γ₁ ⊔ₛ γ')

    minSλ:  : ∀ {C n_f Γ' τ₁ τ₂ τ}
                {wf : n ⊢wf τ₁}
                {Cls' : n , (τ₁ ∷ Γ₀) ⊢ C at synPos τ₂ ▷ n_f , Γ' [ ⇐mode τ ]}
                {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {ϕ₁ : ⌊ τ₁ ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⊣ (ϕ₁ ∷ₛ γ)
            → sλ: wf Cls' ◂ υ ⤳ λ:ₖ ϕ₁ κ ⊣ γ

    minSΛ   : ∀ {C n_f Γ' τ_body τ}
                {Cls' : suc n , shiftΓ (suc zero) Γ₀ ⊢ C at synPos τ_body ▷ n_f , Γ' [ ⇐mode τ ]}
                {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {γ' : ⌊ shiftΓ (suc zero) Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⊣ γ'
            → sΛ Cls' ◂ υ ⤳ Λₖ κ ⊣ unshiftΓₛ γ'

    minSdef₁ : ∀ {C e n_f Γ' τ' τ τ_f}
                 {Cls' : n , Γ₀ ⊢ C at synPos τ' ▷ n_f , Γ' [ ⇐mode τ_f ]}
                 {d₂ : n , (τ' ∷ Γ₀) ⊢ e ⇑ τ}
                 {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
             → Cls' ◂ υ ⤳ κ ⊣ γ
             → sdef₁ Cls' d₂ ◂ υ ⤳ def₁ₖ κ ⊥ₛ ⊣ γ

    minSdef₂ : ∀ {e C n_f Γ' τ' τ_b τ_f}
                 {D : n , Γ₀ ⊢ e ⇑ τ'}
                 {Cls' : n , (τ' ∷ Γ₀) ⊢ C at synPos τ_b ▷ n_f , Γ' [ ⇐mode τ_f ]}
                 {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {ς : ⌊ τ' ⌋} {γ₂ : ⌊ Γ₀ ⌋}
                 {σ₁ : ⌊ e ⌋} {ψ₁ : ⌊ τ' ⌋} {γ₁ : ⌊ Γ₀ ⌋}
             → Cls' ◂ υ ⤳ κ ⊣ (ς ∷ₛ γ₂)
             → D ◂ ς ⤳ σ₁ ⇑ ψ₁ ⊣ γ₁
             → sdef₂ D Cls' ◂ υ ⤳ def₂ₖ σ₁ κ ⊣ (γ₁ ⊔ₛ γ₂)

    minScase₀ : ∀ {C e₁ e₂ n_f Γ' τ₀ τ₁ τ₂ τ₁' τ₂' τ_f}
                  {Cls' : n , Γ₀ ⊢ C at synPos τ₀ ▷ n_f , Γ' [ ⇐mode τ_f ]}
                  {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {d₁ : n , (τ₁ ∷ Γ₀) ⊢ e₁ ⇑ τ₁'} {d₂ : n , (τ₂ ∷ Γ₀) ⊢ e₂ ⇑ τ₂'}
                  {con : τ₁' ~ τ₂'}
                  {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
              → Cls' ◂ υ ⤳ κ ⊣ γ
              → scase₀ Cls' eq d₁ d₂ con ◂ υ ⤳ case₀ₖ κ ⊥ₛ ⊥ₛ ⊣ γ

    minScase₁ : ∀ {e C e' n_f Γ' τ₀ τ₁ τ₂ τ₁' τ₂' τ_f}
                  {D : n , Γ₀ ⊢ e ⇑ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {Cls' : n , (τ₁ ∷ Γ₀) ⊢ C at synPos τ₁' ▷ n_f , Γ' [ ⇐mode τ_f ]}
                  {d₂ : n , (τ₂ ∷ Γ₀) ⊢ e' ⇑ τ₂'} {con : τ₁' ~ τ₂'}
                  {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {ς₁ : ⌊ τ₁ ⌋} {γ₁ : ⌊ Γ₀ ⌋}
                  {σ₀ : ⌊ e ⌋} {ψ₀ : ⌊ τ₀ ⌋} {γ₀ : ⌊ Γ₀ ⌋}
              → Cls' ◂ υ ⤳ κ ⊣ (ς₁ ∷ₛ γ₁)
              → D ◂ (unmatch+-min {τ₀} eq ς₁ ⊥ₛ) ⤳ σ₀ ⇑ ψ₀ ⊣ γ₀
              → scase₁ D eq Cls' d₂ con ◂ υ ⤳ case₁ₖ σ₀ κ ⊥ₛ ⊣ (γ₀ ⊔ₛ γ₁)

    minScase₂ : ∀ {e e' C n_f Γ' τ₀ τ₁ τ₂ τ₁' τ₂' τ_f}
                  {D : n , Γ₀ ⊢ e ⇑ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {d₁ : n , (τ₁ ∷ Γ₀) ⊢ e' ⇑ τ₁'}
                  {Cls' : n , (τ₂ ∷ Γ₀) ⊢ C at synPos τ₂' ▷ n_f , Γ' [ ⇐mode τ_f ]}
                  {con : τ₁' ~ τ₂'}
                  {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {ς₂ : ⌊ τ₂ ⌋} {γ₂ : ⌊ Γ₀ ⌋}
                  {σ₀ : ⌊ e ⌋} {ψ₀ : ⌊ τ₀ ⌋} {γ₀ : ⌊ Γ₀ ⌋}
              → Cls' ◂ υ ⤳ κ ⊣ (ς₂ ∷ₛ γ₂)
              → D ◂ (unmatch+-min {τ₀} eq ⊥ₛ ς₂) ⤳ σ₀ ⇑ ψ₀ ⊣ γ₀
              → scase₂ D eq d₁ Cls' con ◂ υ ⤳ case₂ₖ σ₀ ⊥ₛ κ ⊣ (γ₀ ⊔ₛ γ₂)

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

    minAλ⇒  : ∀ {C n_f Γ' τ τ₁ τ₂ τ_f}
                {eq : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                {Cls' : n , (τ₁ ∷ Γ₀) ⊢ C at anaPos τ₂ ▷ n_f , Γ' [ ⇐mode τ_f ]}
                {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {ς₁ : ⌊ τ₁ ⌋} {υ_b : ⌊ τ₂ ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⇓ υ_b ⊣ (ς₁ ∷ₛ γ)
            → aλ⇒ eq Cls' ◂ υ ⤳ λ⇒ₖ κ ⇓ unmatch⇒-min {τ} eq ς₁ υ_b ⊣ γ

    minAλ:  : ∀ {C n_f Γ' τ τ₁ τ₁' τ₂ τ_f}
                {con : τ ~ τ₁ ⇒ □} {eq : τ ⊔ τ₁ ⇒ □ ≡ τ₁' ⇒ τ₂}
                {wf : n ⊢wf τ₁}
                {Cls' : n , (τ₁ ∷ Γ₀) ⊢ C at anaPos τ₂ ▷ n_f , Γ' [ ⇐mode τ_f ]}
                {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {ς₁ : ⌊ τ₁ ⌋} {υ_b : ⌊ τ₂ ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls' ◂ υ ⤳ κ ⇓ υ_b ⊣ (ς₁ ∷ₛ γ)
            → aλ: con eq wf Cls' ◂ υ
              ⤳ λ:ₖ ς₁ κ ⇓ unmatch⇒-min {τ} (proj₂ (ann-⇒-plain {τ} {τ₁} eq)) ⊥ₛ υ_b ⊣ γ

    minAdef₁ : ∀ {C e n_f Γ' τ' τ τ_f}
                 {Cls' : n , Γ₀ ⊢ C at synPos τ' ▷ n_f , Γ' [ ⇐mode τ_f ]}
                 {d₂ : n , (τ' ∷ Γ₀) ⊢ e ⇓ τ}
                 {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
             → Cls' ◂ υ ⤳ κ ⊣ γ
             → adef₁ Cls' d₂ ◂ υ ⤳ def₁ₖ κ ⊥ₛ ⇓ ⊥ₛ ⊣ γ

    minAdef₂ : ∀ {e C n_f Γ' τ' τ τ_f}
                 {D : n , Γ₀ ⊢ e ⇑ τ'}
                 {Cls' : n , (τ' ∷ Γ₀) ⊢ C at anaPos τ ▷ n_f , Γ' [ ⇐mode τ_f ]}
                 {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {υ_b : ⌊ τ ⌋} {ς : ⌊ τ' ⌋} {γ₂ : ⌊ Γ₀ ⌋}
                 {σ₁ : ⌊ e ⌋} {ψ₁ : ⌊ τ' ⌋} {γ₁ : ⌊ Γ₀ ⌋}
             → Cls' ◂ υ ⤳ κ ⇓ υ_b ⊣ (ς ∷ₛ γ₂)
             → D ◂ ς ⤳ σ₁ ⇑ ψ₁ ⊣ γ₁
             → adef₂ D Cls' ◂ υ ⤳ def₂ₖ σ₁ κ ⇓ υ_b ⊣ (γ₁ ⊔ₛ γ₂)

    minAcase₀ : ∀ {C e₁ e₂ n_f Γ' τ₀ τ₁ τ₂ τ τ_f}
                  {Cls' : n , Γ₀ ⊢ C at synPos τ₀ ▷ n_f , Γ' [ ⇐mode τ_f ]}
                  {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {d₁ : n , (τ₁ ∷ Γ₀) ⊢ e₁ ⇓ τ} {d₂ : n , (τ₂ ∷ Γ₀) ⊢ e₂ ⇓ τ}
                  {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
              → Cls' ◂ υ ⤳ κ ⊣ γ
              → acase₀ Cls' eq d₁ d₂ ◂ υ ⤳ case₀ₖ κ ⊥ₛ ⊥ₛ ⇓ ⊥ₛ ⊣ γ

    minAcase₁ : ∀ {e C e' n_f Γ' τ₀ τ₁ τ₂ τ τ_f}
                  {D : n , Γ₀ ⊢ e ⇑ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {Cls' : n , (τ₁ ∷ Γ₀) ⊢ C at anaPos τ ▷ n_f , Γ' [ ⇐mode τ_f ]}
                  {d₂ : n , (τ₂ ∷ Γ₀) ⊢ e' ⇓ τ}
                  {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {υ_b : ⌊ τ ⌋} {ς₁ : ⌊ τ₁ ⌋} {γ₁ : ⌊ Γ₀ ⌋}
                  {σ₀ : ⌊ e ⌋} {ψ₀ : ⌊ τ₀ ⌋} {γ₀ : ⌊ Γ₀ ⌋}
              → Cls' ◂ υ ⤳ κ ⇓ υ_b ⊣ (ς₁ ∷ₛ γ₁)
              → D ◂ (unmatch+-min {τ₀} eq ς₁ ⊥ₛ) ⤳ σ₀ ⇑ ψ₀ ⊣ γ₀
              → acase₁ D eq Cls' d₂ ◂ υ ⤳ case₁ₖ σ₀ κ ⊥ₛ ⇓ υ_b ⊣ (γ₀ ⊔ₛ γ₁)

    minAcase₂ : ∀ {e e' C n_f Γ' τ₀ τ₁ τ₂ τ τ_f}
                  {D : n , Γ₀ ⊢ e ⇑ τ₀} {eq : τ₀ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {d₁ : n , (τ₁ ∷ Γ₀) ⊢ e' ⇓ τ}
                  {Cls' : n , (τ₂ ∷ Γ₀) ⊢ C at anaPos τ ▷ n_f , Γ' [ ⇐mode τ_f ]}
                  {υ : ⌊ τ_f ⌋} {κ : ⌊ C ⌋} {υ_b : ⌊ τ ⌋} {ς₂ : ⌊ τ₂ ⌋} {γ₂ : ⌊ Γ₀ ⌋}
                  {σ₀ : ⌊ e ⌋} {ψ₀ : ⌊ τ₀ ⌋} {γ₀ : ⌊ Γ₀ ⌋}
              → Cls' ◂ υ ⤳ κ ⇓ υ_b ⊣ (ς₂ ∷ₛ γ₂)
              → D ◂ (unmatch+-min {τ₀} eq ⊥ₛ ς₂) ⤳ σ₀ ⇑ ψ₀ ⊣ γ₀
              → acase₂ D eq d₁ Cls' ◂ υ ⤳ case₂ₖ σ₀ ⊥ₛ κ ⇓ υ_b ⊣ (γ₀ ⊔ₛ γ₂)
