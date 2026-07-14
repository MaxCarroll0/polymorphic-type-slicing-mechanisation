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

