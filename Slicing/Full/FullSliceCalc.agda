open import Data.Nat using (ℕ)
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core
open import Core.Typ.Lift using
  (unmatch⇒-min; unmatch×-min; unmatch+-min)
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

    minSι₁ : ∀ {C n_f Γ e τᵢ τ}
                {Cls : n , Γ₀ ⊢ C at synPos τᵢ ▷ n_f , Γ [ ⇒mode τ ]}
                {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
            → sι₁ Cls , D ◂ u ⤳ ι₁ₖ κ ∣ σ ⊣ γ

    minSι₂ : ∀ {C n_f Γ e τᵢ τ}
                {Cls : n , Γ₀ ⊢ C at synPos τᵢ ▷ n_f , Γ [ ⇒mode τ ]}
                {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
            → sι₂ Cls , D ◂ u ⤳ ι₂ₖ κ ∣ σ ⊣ γ

    minS&₁ : ∀ {C e₂ n_f Γ e τ₁ τ₂ τ}
                {Cls : n , Γ₀ ⊢ C at synPos τ₁ ▷ n_f , Γ [ ⇒mode τ ]}
                {d₂ : n , Γ₀ ⊢ e₂ ⇑ τ₂} {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
            → s&₁ Cls d₂ , D ◂ u ⤳ κ &₁ₖ ⊥ₛ ∣ σ ⊣ γ

    minS&₂ : ∀ {e₁ C n_f Γ e τ₁ τ₂ τ}
                {d₁ : n , Γ₀ ⊢ e₁ ⇑ τ₁}
                {Cls : n , Γ₀ ⊢ C at synPos τ₂ ▷ n_f , Γ [ ⇒mode τ ]}
                {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
            → s&₂ d₁ Cls , D ◂ u ⤳ ⊥ₛ &₂ₖ κ ∣ σ ⊣ γ

    minSπ₁ : ∀ {C n_f Γ e τᵢ τ₁ τ₂ τ}
                {Cls : n , Γ₀ ⊢ C at synPos τᵢ ▷ n_f , Γ [ ⇒mode τ ]}
                {eq : τᵢ ⊔ □ × □ ≡ τ₁ × τ₂} {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
            → sπ₁ Cls eq , D ◂ u ⤳ π₁ₖ κ ∣ σ ⊣ γ

    minSπ₂ : ∀ {C n_f Γ e τᵢ τ₁ τ₂ τ}
                {Cls : n , Γ₀ ⊢ C at synPos τᵢ ▷ n_f , Γ [ ⇒mode τ ]}
                {eq : τᵢ ⊔ □ × □ ≡ τ₁ × τ₂} {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
            → sπ₂ Cls eq , D ◂ u ⤳ π₂ₖ κ ∣ σ ⊣ γ

    minS∘₁ : ∀ {C e₂ n_f Γ e τᵢ τ₁ τ₂ τ}
                {Cls : n , Γ₀ ⊢ C at synPos τᵢ ▷ n_f , Γ [ ⇒mode τ ]}
                {eq : τᵢ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                {d₂ : n , Γ₀ ⊢ e₂ ⇓ τ₁} {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
            → s∘₁ Cls eq d₂ , D ◂ u ⤳ κ ∘₁ₖ ⊥ₛ ∣ σ ⊣ γ

    minS<>₁ : ∀ {C n_f Γ e τᵢ τ' τₐ τ}
                 {Cls : n , Γ₀ ⊢ C at synPos τᵢ ▷ n_f , Γ [ ⇒mode τ ]}
                 {eq : τᵢ ⊔ ∀· □ ≡ ∀· τ'} {wf : n ⊢wf τₐ}
                 {D : n_f , Γ ⊢ e ⇑ τ}
                 {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
             → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
             → s<>₁ Cls eq wf , D ◂ u ⤳ κ <>₁ₖ ⊥ₛ ∣ σ ⊣ γ

    minS∘₂ : ∀ {e₁ C n_f Γ e τ₀ τ₁ τ₂ τ}
                {D₁ : n , Γ₀ ⊢ e₁ ⇑ τ₀} {eq : τ₀ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                {Cls : n , Γ₀ ⊢ C at anaPos τ₁ ▷ n_f , Γ [ ⇒mode τ ]}
                {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {uₒ : ⌊ τ₁ ⌋}
                {γ' : ⌊ Γ₀ ⌋} {σ : ⌊ e ⌋}
                {σ₁ : ⌊ e₁ ⌋} {ψ₁ : ⌊ τ₀ ⌋} {γ₁ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⇓ uₒ ⊣ γ'
            → D₁ ◂ unmatch⇒-min {τ₀} eq uₒ ⊥ₛ ⤳ σ₁ ⇑ ψ₁ ⊣ γ₁
            → s∘₂ D₁ eq Cls , D ◂ u ⤳ σ₁ ∘₂ₖ κ ∣ σ ⊣ (γ₁ ⊔ₛ γ')

    minSdef₁ : ∀ {C e₂ n_f Γ e τ' τ₂ τ}
                 {Cls : n , Γ₀ ⊢ C at synPos τ' ▷ n_f , Γ [ ⇒mode τ ]}
                 {d₂ : n , (τ' ∷ Γ₀) ⊢ e₂ ⇑ τ₂} {D : n_f , Γ ⊢ e ⇑ τ}
                 {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
             → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
             → sdef₁ Cls d₂ , D ◂ u ⤳ def₁ₖ κ ⊥ₛ ∣ σ ⊣ γ

  data _,_◂_⤳_∣_⇓_⊣_ {n} {Γ₀} where

    minASub : ∀ {C n_f Γ e τ τₒ τₚ}
                {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                {D : n_f , Γ ⊢ e ⇑ τ} {con : τₒ ~ τₚ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
            → aSub Cls con , D ◂ u ⤳ κ ∣ σ ⇓ ⊥ₛ ⊣ γ

    minAι₁ : ∀ {C n_f Γ e τₒ τ₁ τ₂ τ}
                {eq : τₒ ⊔ □ + □ ≡ τ₁ + τ₂}
                {Cls : n , Γ₀ ⊢ C at anaPos τ₁ ▷ n_f , Γ [ ⇒mode τ ]}
                {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋}
                {uᵢ : ⌊ τ₁ ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⇓ uᵢ ⊣ γ
            → aι₁ eq Cls , D ◂ u
              ⤳ ι₁ₖ κ ∣ σ ⇓ unmatch+-min {τₒ} eq uᵢ ⊥ₛ ⊣ γ

    minAι₂ : ∀ {C n_f Γ e τₒ τ₁ τ₂ τ}
                {eq : τₒ ⊔ □ + □ ≡ τ₁ + τ₂}
                {Cls : n , Γ₀ ⊢ C at anaPos τ₂ ▷ n_f , Γ [ ⇒mode τ ]}
                {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋}
                {uᵢ : ⌊ τ₂ ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⇓ uᵢ ⊣ γ
            → aι₂ eq Cls , D ◂ u
              ⤳ ι₂ₖ κ ∣ σ ⇓ unmatch+-min {τₒ} eq ⊥ₛ uᵢ ⊣ γ

    minA&₁ : ∀ {C e₂ n_f Γ e τₒ τ₁ τ₂ τ}
                {eq : τₒ ⊔ □ × □ ≡ τ₁ × τ₂}
                {Cls : n , Γ₀ ⊢ C at anaPos τ₁ ▷ n_f , Γ [ ⇒mode τ ]}
                {d₂ : n , Γ₀ ⊢ e₂ ⇓ τ₂} {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋}
                {uᵢ : ⌊ τ₁ ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⇓ uᵢ ⊣ γ
            → a&₁ eq Cls d₂ , D ◂ u
              ⤳ κ &₁ₖ ⊥ₛ ∣ σ ⇓ unmatch×-min {τₒ} eq uᵢ ⊥ₛ ⊣ γ

    minA&₂ : ∀ {e₁ C n_f Γ e τₒ τ₁ τ₂ τ}
                {eq : τₒ ⊔ □ × □ ≡ τ₁ × τ₂}
                {d₁ : n , Γ₀ ⊢ e₁ ⇓ τ₁}
                {Cls : n , Γ₀ ⊢ C at anaPos τ₂ ▷ n_f , Γ [ ⇒mode τ ]}
                {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋}
                {uᵢ : ⌊ τ₂ ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⇓ uᵢ ⊣ γ
            → a&₂ eq d₁ Cls , D ◂ u
              ⤳ ⊥ₛ &₂ₖ κ ∣ σ ⇓ unmatch×-min {τₒ} eq ⊥ₛ uᵢ ⊣ γ

    minAdef₁ : ∀ {C e₂ n_f Γ e τ' τ₂ τ}
                 {Cls : n , Γ₀ ⊢ C at synPos τ' ▷ n_f , Γ [ ⇒mode τ ]}
                 {d₂ : n , (τ' ∷ Γ₀) ⊢ e₂ ⇓ τ₂} {D : n_f , Γ ⊢ e ⇑ τ}
                 {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
             → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
             → adef₁ Cls d₂ , D ◂ u ⤳ def₁ₖ κ ⊥ₛ ∣ σ ⇓ ⊥ₛ ⊣ γ
