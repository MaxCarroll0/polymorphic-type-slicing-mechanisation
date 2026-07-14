open import Data.Nat using (ℕ)
open import Core
open import Semantics.Statics
open import Slicing.Synthesis.FixedAssmsCalc using (_◂_⤳_⇑_⊣_)

-- Inductive calculation of full synthesis slices.  The two judgments walk
-- synthesis and analysis positions respectively, while carrying the same
-- focused synthesis derivation.  Their outputs are the context slice, the
-- focused expression slice, and the external assumptions; the analysis form
-- additionally returns the least outer analysis type.
module Slicing.Full.FullSliceCalc where

infix 4 _,_◂_⤳_∣_⊣_
infix 4 _,_◂_⤳_∣_⇓_⊣_

mutual
  data _,_◂_⤳_∣_⊣_ {n : ℕ} {Γ₀ : Assms} :
      ∀ {C n_f Γ e τ τₚ}
      → (Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ])
      → (D : n_f , Γ ⊢ e ⇑ τ)
      → ⌊ τ ⌋ → ⌊ C ⌋ → ⌊ e ⌋ → ⌊ Γ₀ ⌋ → Set

  data _,_◂_⤳_∣_⇓_⊣_ {n : ℕ} {Γ₀ : Assms} :
      ∀ {C n_f Γ e τ τₚ}
      → (Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n_f , Γ [ ⇒mode τ ])
      → (D : n_f , Γ ⊢ e ⇑ τ)
      → ⌊ τ ⌋ → ⌊ C ⌋ → ⌊ e ⌋ → ⌊ τₚ ⌋ → ⌊ Γ₀ ⌋ → Set

  data _,_◂_⤳_∣_⊣_ {n} {Γ₀} where

    minS○ : ∀ {e τ} {D : n , Γ₀ ⊢ e ⇑ τ}
              {u : ⌊ τ ⌋} {σ : ⌊ e ⌋} {ψ : ⌊ τ ⌋} {γ : ⌊ Γ₀ ⌋}
          → D ◂ u ⤳ σ ⇑ ψ ⊣ γ
          → s○ , D ◂ u ⤳ ○ₖ ∣ σ ⊣ γ

  data _,_◂_⤳_∣_⇓_⊣_ {n} {Γ₀} where

    minASub : ∀ {C n_f Γ e τ τₒ τₚ}
                {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                {D : n_f , Γ ⊢ e ⇑ τ} {con : τₒ ~ τₚ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
            → aSub Cls con , D ◂ u ⤳ κ ∣ σ ⇓ ⊥ₛ ⊣ γ
