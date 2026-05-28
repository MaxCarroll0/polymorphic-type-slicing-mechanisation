open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
open import Core
open import Semantics.Statics
open import Semantics.Graduality using (mode-⊑; ⇐mode-⊑; ⇒mode-⊑;
                                          static-gradual-syn; static-gradual-ana;
                                          static-gradual-syn-cls; static-gradual-ana-cls)
open import Core.Typ.Lift
open import Core.Typ.Properties using (⊔-⇒-⊑; ⊔-×-⊑; ⊔-+-⊑; ⊔-∀-⊑; ⊔-ann-⇒-⊑;
                                        sub-⊑; ⊔-mono-⊑)
open import Core.Assms.Lift using (hdₛ; tlₛ)
open import Core.Assms.Precision using (shiftΓ-⊑)
open import Slicing.Synthesis.Synthesis using (SynSlice_◂_; MinSynSlice_◂_; _↓s; _↓γ; _↓γₛ; _↓γ⊑; _↓σ; _↓σ⊑)
open import Slicing.Analysis.Analysis
open import Slicing.Analysis.AnaSliceCalc

module Slicing.Analysis.FocusCov where

-- lift-pos-cov / lift-syn-cov: strengthened static-gradual-{ana,syn}-cls.
--
-- For a MinAnaPos m on Cls and a precondition relating m's structural
-- ana-υ_outer-of-m to the lift's τ_p_₁ input, lift-pos-cov produces the
-- lifted classification AND witnesses focus coverage (υ ⊑ τ_f).
--
-- Preconditions use the direct-mode helpers `ana-υ_outer-of-m` / `syn-*-of-m`
-- from AnaSliceCalc.agda, which compute the relevant slice values WITHOUT
-- going through extract-pos's with-blocked clauses. This is crucial for the
-- precondition to be statable in a way that reduces under abstract m.
--
-- Inductive cases use unmatch+/×/⇒-cov-{fst,snd,cod,dom} from Lift.agda to
-- invert the structural unmatch in the constructor's ana-υ_outer-of-m.

private
  postulate
    cov-witness : ∀ {τ : Typ} (υ : ⌊ τ ⌋) (τ_f : Typ) → υ .↓ ⊑t τ_f
    minS∘₂-cov : ∀ {n Γ Γ' C n_f τ_p τ}
                   {Cls : n , Γ ⊢ C at synPos τ_p ▷ n_f , Γ' [ ⇐mode τ ]}
                   {υ : ⌊ τ ⌋} (m : MinAna Cls υ)
                 → ∀ {Γ_₁ C_₁} (Γ⊑ : Γ_₁ ⊑ Γ) (C⊑ : C_₁ ⊑c C)
                 → ∃[ τ_p_₁ ] (τ_p_₁ ⊑ τ_p) ∧
                   ∃[ Γ_f_₁ ] ∃[ n_f_₁ ] ∃[ τ_f ]
                     (Γ_f_₁ ⊑ Γ') ∧ (τ_f ⊑ τ) ∧ (υ .↓ ⊑t τ_f) ∧
                     (n , Γ_₁ ⊢ C_₁ at synPos τ_p_₁ ▷ n_f_₁ , Γ_f_₁ [ ⇐mode τ_f ])

mutual

  lift-pos-cov : ∀ {n Γ Γ' C n_f τ_p τ}
                   {Cls : n , Γ ⊢ C at anaPos τ_p ▷ n_f , Γ' [ ⇐mode τ ]}
                   {υ : ⌊ τ ⌋}
                   (m : MinAnaPos Cls υ)
               → ∀ {Γ_₁ C_₁ τ_p_₁}
                   (Γ⊑ : Γ_₁ ⊑ Γ) (C⊑ : C_₁ ⊑c C) (τ_p⊑ : τ_p_₁ ⊑ τ_p)
                   (pre : ana-υ_outer-of-m m .↓ ⊑t τ_p_₁)
               → ∃[ Γ_f_₁ ] ∃[ n_f_₁ ] ∃[ τ_f ]
                   (Γ_f_₁ ⊑ Γ') ∧ (τ_f ⊑ τ) ∧ (υ .↓ ⊑t τ_f) ∧
                   (n , Γ_₁ ⊢ C_₁ at anaPos τ_p_₁ ▷ n_f_₁ , Γ_f_₁ [ ⇐mode τ_f ])

  lift-syn-cov : ∀ {n Γ Γ' C n_f τ_p τ}
                   {Cls : n , Γ ⊢ C at synPos τ_p ▷ n_f , Γ' [ ⇐mode τ ]}
                   {υ : ⌊ τ ⌋}
                   (m : MinAna Cls υ)
               → ∀ {Γ_₁ C_₁} (Γ⊑ : Γ_₁ ⊑ Γ) (C⊑ : C_₁ ⊑c C)
               → ∃[ τ_p_₁ ] (τ_p_₁ ⊑ τ_p) ∧
                 ∃[ Γ_f_₁ ] ∃[ n_f_₁ ] ∃[ τ_f ]
                   (Γ_f_₁ ⊑ Γ') ∧ (τ_f ⊑ τ) ∧ (υ .↓ ⊑t τ_f) ∧
                   (n , Γ_₁ ⊢ C_₁ at synPos τ_p_₁ ▷ n_f_₁ , Γ_f_₁ [ ⇐mode τ_f ])

  -- LEAF cases for anaPos:

  lift-pos-cov (minA○ υ) Γ⊑ ⊑○ τ_p⊑ pre =
    _ , _ , _ , Γ⊑ , τ_p⊑ , pre , a○

  lift-pos-cov {Cls = Cls} min□Pos Γ⊑ C⊑ τ_p⊑ pre
    with static-gradual-ana-cls Γ⊑ C⊑ τ_p⊑ Cls
  ... | _ , _ , _ , Γ_f⊑ , ⇐mode-⊑ τ_f⊑ , inner-cls =
        _ , _ , _ , Γ_f⊑ , τ_f⊑ , ⊑□ , inner-cls

  lift-pos-cov (minASub {con = con} m) Γ⊑ C⊑ τ_p⊑ pre
    with lift-syn-cov m Γ⊑ C⊑
  ... | _ , τ'⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
        _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
        aSub inner-cls (~-⊑-down con τ_p⊑ τ'⊑)

  -- INDUCTIVE cases for anaPos:

  -- minAλ⇒: aλ⇒ eq Cls'_inner. ana-υ_outer-of-m = unmatch⇒ eq <hd-binder> <body-υ>.
  -- Inner classification at anaPos τ₂ in (τ₁ ∷ Γ). Inner-pre comes from
  -- unmatch⇒-cov-cod (the body-υ.↓ ⊑t τ_b_₁ from the lifted cod).
  lift-pos-cov {τ_p = τ_p} (minAλ⇒ {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} m_inner)
               Γ⊑ (⊑λu C-inner⊑) τ_p⊑ pre
    with ⊔-⇒-⊑ τ_p⊑ eq
  ... | τ_a_₁ , τ_b_₁ , eq-lifted , pa , pb =
    let inner-pre : ana-υ_outer-of-m m_inner .↓ ⊑t τ_b_₁
        inner-pre = unmatch⇒-cov-cod τ_p eq (hdₛ (ana-γ-of-m m_inner))
                                        (ana-υ_outer-of-m m_inner) pre eq-lifted
        _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
          lift-pos-cov m_inner (⊑∷ pa Γ⊑) C-inner⊑ pb inner-pre
    in _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , aλ⇒ eq-lifted inner-cls

  -- minAλ:: aλ: c eq wf Cls'. Constructor links outer-υ ⊔ τ₁⇒□ to inner-υ
  -- via eq-orig and ⊔-ann-⇒-⊑. Currently fallback + TODO for cov.
  lift-pos-cov {Cls = Cls} {υ = υ} (minAλ: m_inner outer-υ c-lifted eq-orig)
               Γ⊑ C⊑ τ_p⊑ pre
    with static-gradual-ana-cls Γ⊑ C⊑ τ_p⊑ Cls
  ... | _ , _ , _ , Γ_f⊑ , ⇐mode-⊑ {τ₁ = τ_f} τ_f⊑ , inner-cls =
        _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov-witness υ τ_f , inner-cls

  -- minA&₁: outer a&₁ eq Cls' d₂. ana-υ_outer-of-m = unmatch× eq υ-fst ⊥ₛ.
  lift-pos-cov {τ_p = τ_p} (minA&₁ {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} {d₂ = d₂} m_inner)
               Γ⊑ (⊑&₁ C-inner⊑ e⊑) τ_p⊑ pre
    with ⊔-×-⊑ τ_p⊑ eq
  ... | τ_a_₁ , τ_b_₁ , eq-lifted , pa , pb =
    let inner-pre : ana-υ_outer-of-m m_inner .↓ ⊑t τ_a_₁
        inner-pre = unmatch×-cov-fst τ_p eq (ana-υ_outer-of-m m_inner) ⊥ₛ pre eq-lifted
        _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
          lift-pos-cov m_inner Γ⊑ C-inner⊑ pa inner-pre
    in _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
       a&₁ eq-lifted inner-cls (static-gradual-ana Γ⊑ e⊑ pb d₂)

  -- minA&₂: symmetric to minA&₁.
  lift-pos-cov {τ_p = τ_p} (minA&₂ {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} {d₁ = d₁} m_inner)
               Γ⊑ (⊑&₂ e⊑ C-inner⊑) τ_p⊑ pre
    with ⊔-×-⊑ τ_p⊑ eq
  ... | τ_a_₁ , τ_b_₁ , eq-lifted , pa , pb =
    let inner-pre : ana-υ_outer-of-m m_inner .↓ ⊑t τ_b_₁
        inner-pre = unmatch×-cov-snd τ_p eq ⊥ₛ (ana-υ_outer-of-m m_inner) pre eq-lifted
        _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
          lift-pos-cov m_inner Γ⊑ C-inner⊑ pb inner-pre
    in _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
       a&₂ eq-lifted (static-gradual-ana Γ⊑ e⊑ pa d₁) inner-cls

  -- minAι₁: outer aι₁ eq Cls'. ana-υ_outer-of-m = unmatch+ eq υ-fst ⊥ₛ.
  lift-pos-cov {τ_p = τ_p} (minAι₁ {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} m_inner)
               Γ⊑ (⊑ι₁ C-inner⊑) τ_p⊑ pre
    with ⊔-+-⊑ τ_p⊑ eq
  ... | τ_a_₁ , τ_b_₁ , eq-lifted , pa , pb =
    let inner-pre : ana-υ_outer-of-m m_inner .↓ ⊑t τ_a_₁
        inner-pre = unmatch+-cov-fst τ_p eq (ana-υ_outer-of-m m_inner) ⊥ₛ pre eq-lifted
        _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
          lift-pos-cov m_inner Γ⊑ C-inner⊑ pa inner-pre
    in _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , aι₁ eq-lifted inner-cls

  -- minAι₂: symmetric to minAι₁.
  lift-pos-cov {τ_p = τ_p} (minAι₂ {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} m_inner)
               Γ⊑ (⊑ι₂ C-inner⊑) τ_p⊑ pre
    with ⊔-+-⊑ τ_p⊑ eq
  ... | τ_a_₁ , τ_b_₁ , eq-lifted , pa , pb =
    let inner-pre : ana-υ_outer-of-m m_inner .↓ ⊑t τ_b_₁
        inner-pre = unmatch+-cov-snd τ_p eq ⊥ₛ (ana-υ_outer-of-m m_inner) pre eq-lifted
        _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
          lift-pos-cov m_inner Γ⊑ C-inner⊑ pb inner-pre
    in _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , aι₂ eq-lifted inner-cls

  -- minAcase₁: outer acase₁ D eq Cls' d₂. ana-υ_outer-of-m propagates from inner.
  lift-pos-cov (minAcase₁ {D = D} {eq = eq} {d₂ = d₂} m_inner _ _ _)
               Γ⊑ (⊑case₁ e⊑ C-inner⊑ e'⊑) τ_p⊑ pre
    with static-gradual-syn Γ⊑ e⊑ D
  ... | τ₀_₁ , D_₁ , τ₀⊑
    with ⊔-+-⊑ τ₀⊑ eq
  ... | τ₁_₁ , τ₂_₁ , eq_₁ , p₁ , p₂ =
    let _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
          lift-pos-cov m_inner (⊑∷ p₁ Γ⊑) C-inner⊑ τ_p⊑ pre
    in _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
       acase₁ D_₁ eq_₁ inner-cls (static-gradual-ana (⊑∷ p₂ Γ⊑) e'⊑ τ_p⊑ d₂)

  -- minAcase₂: symmetric to minAcase₁.
  lift-pos-cov (minAcase₂ {D = D} {eq = eq} {d₁ = d₁} m_inner _ _ _)
               Γ⊑ (⊑case₂ e⊑ e'⊑ C-inner⊑) τ_p⊑ pre
    with static-gradual-syn Γ⊑ e⊑ D
  ... | τ₀_₁ , D_₁ , τ₀⊑
    with ⊔-+-⊑ τ₀⊑ eq
  ... | τ₁_₁ , τ₂_₁ , eq_₁ , p₁ , p₂ =
    let _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
          lift-pos-cov m_inner (⊑∷ p₂ Γ⊑) C-inner⊑ τ_p⊑ pre
    in _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
       acase₂ D_₁ eq_₁ (static-gradual-ana (⊑∷ p₁ Γ⊑) e'⊑ τ_p⊑ d₁) inner-cls

  -- minAdef₁: outer adef₁ Cls' d₂. Cross into syn via lift-syn-cov.
  lift-pos-cov (minAdef₁ {d₂ = d₂} m_inner) Γ⊑ (⊑def₁ C-inner⊑ e⊑) τ_p⊑ pre
    with lift-syn-cov m_inner Γ⊑ C-inner⊑
  ... | _ , τ'⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
        _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
        adef₁ inner-cls (static-gradual-ana (⊑∷ τ'⊑ Γ⊑) e⊑ τ_p⊑ d₂)

  -- minAdef₂: outer adef₂ D Cls'. ana-υ_outer-of-m propagates from inner.
  lift-pos-cov (minAdef₂ {D = D} m_inner _ _ _) Γ⊑ (⊑def₂ e⊑ C-inner⊑) τ_p⊑ pre
    with static-gradual-syn Γ⊑ e⊑ D
  ... | τ'_₁ , D_₁ , τ'⊑ =
    let _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
          lift-pos-cov m_inner (⊑∷ τ'⊑ Γ⊑) C-inner⊑ τ_p⊑ pre
    in _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , adef₂ D_₁ inner-cls

  -- LEAF cases for synPos:

  lift-syn-cov {Cls = Cls} min□ Γ⊑ C⊑
    with static-gradual-syn-cls Γ⊑ C⊑ Cls
  ... | τ_p_₁ , _ , _ , _ , τ_p⊑ , Γ_f⊑ , ⇐mode-⊑ τ_f⊑ , inner-cls =
        _ , τ_p⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , ⊑□ , inner-cls

  -- INDUCTIVE cases for synPos:

  lift-syn-cov (minSλ: {wf = wf} _ m_inner) Γ⊑ (⊑λ τ_h⊑ C-inner⊑)
    with lift-syn-cov m_inner (⊑∷ τ_h⊑ Γ⊑) C-inner⊑
  ... | τ₂_₁ , τ₂⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
        _ , ⊑⇒ τ_h⊑ τ₂⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
        sλ: (wf-⊑ wf τ_h⊑) inner-cls

  lift-syn-cov (minS∘₁ {eq = eq} {d₂ = d₂} m_inner) Γ⊑ (⊑∘₁ C-inner⊑ e⊑)
    with lift-syn-cov m_inner Γ⊑ C-inner⊑
  ... | τ_₁ , τ⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls
    with ⊔-⇒-⊑ τ⊑ eq
  ... | τ_a , τ_b , eq_₁ , pa , pb =
        τ_b , pb , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
        s∘₁ inner-cls eq_₁ (static-gradual-ana Γ⊑ e⊑ pa d₂)

  -- minS∘₂: hardest case. The outer Cls'_inner is at anaPos τ₁, and it's the
  -- argument analyzed against an inferred dom from D₁. This requires combining
  -- a synthesis slice on D₁ and lift-pos-cov on Cls'_inner.
  lift-syn-cov m@(minS∘₂ {τ₀ = τ₀} {D₁ = D₁} {eq = eq} m_inner ss focus focus⊒ pkg)
               Γ⊑ C⊑@(⊑∘₂ e⊑ C-inner⊑) = minS∘₂-cov m Γ⊑ C⊑

  lift-syn-cov (minS<>₁ {eq = eq} {wf = wf} m_inner) Γ⊑ (⊑<>₁ C-inner⊑ σ⊑)
    with lift-syn-cov m_inner Γ⊑ C-inner⊑
  ... | τ_₁ , τ⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls
    with ⊔-∀-⊑ τ⊑ eq
  ... | τ'_₁ , eq_₁ , p =
        _ , sub-⊑ zero σ⊑ p , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
        s<>₁ inner-cls eq_₁ (wf-⊑ wf σ⊑)

  lift-syn-cov (minS&₁ {d₂ = d₂} m_inner) Γ⊑ (⊑&₁ C-inner⊑ e⊑)
    with lift-syn-cov m_inner Γ⊑ C-inner⊑
       | static-gradual-syn Γ⊑ e⊑ d₂
  ... | τ₁_₁ , τ₁⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls
      | τ₂_₁ , d₂_₁ , τ₂⊑ =
        _ , ⊑× τ₁⊑ τ₂⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
        s&₁ inner-cls d₂_₁

  lift-syn-cov (minS&₂ {d₁ = d₁} m_inner) Γ⊑ (⊑&₂ e⊑ C-inner⊑)
    with static-gradual-syn Γ⊑ e⊑ d₁
       | lift-syn-cov m_inner Γ⊑ C-inner⊑
  ... | τ₁_₁ , d₁_₁ , τ₁⊑
      | τ₂_₁ , τ₂⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
        _ , ⊑× τ₁⊑ τ₂⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
        s&₂ d₁_₁ inner-cls

  lift-syn-cov (minScase₁ {D = D} {eq = eq} {d₂ = d₂} {con = con} m_inner _ _ _ _ _)
               Γ⊑ (⊑case₁ e⊑ C-inner⊑ e'⊑)
    with static-gradual-syn Γ⊑ e⊑ D
  ... | τ_₁ , D_₁ , τ⊑
    with ⊔-+-⊑ τ⊑ eq
  ... | τ₁_₁ , τ₂_₁ , eq_₁ , p₁ , p₂
    with lift-syn-cov m_inner (⊑∷ p₁ Γ⊑) C-inner⊑
       | static-gradual-syn (⊑∷ p₂ Γ⊑) e'⊑ d₂
  ... | τ₁'_₁ , τ₁'⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls
      | τ₂'_₁ , d₂_₁ , τ₂'⊑ =
        _ , ⊔-mono-⊑ con τ₁'⊑ τ₂'⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
        scase₁ D_₁ eq_₁ inner-cls d₂_₁ (~-⊑-down con τ₁'⊑ τ₂'⊑)

  lift-syn-cov (minScase₂ {D = D} {eq = eq} {d₁ = d₁} {con = con} m_inner _ _ _ _ _)
               Γ⊑ (⊑case₂ e⊑ e'⊑ C-inner⊑)
    with static-gradual-syn Γ⊑ e⊑ D
  ... | τ_₁ , D_₁ , τ⊑
    with ⊔-+-⊑ τ⊑ eq
  ... | τ₁_₁ , τ₂_₁ , eq_₁ , p₁ , p₂
    with static-gradual-syn (⊑∷ p₁ Γ⊑) e'⊑ d₁
       | lift-syn-cov m_inner (⊑∷ p₂ Γ⊑) C-inner⊑
  ... | τ₁'_₁ , d₁_₁ , τ₁'⊑
      | τ₂'_₁ , τ₂'⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
        _ , ⊔-mono-⊑ con τ₁'⊑ τ₂'⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
        scase₂ D_₁ eq_₁ d₁_₁ inner-cls (~-⊑-down con τ₁'⊑ τ₂'⊑)

  lift-syn-cov (minSι₁ m_inner) Γ⊑ (⊑ι₁ C-inner⊑)
    with lift-syn-cov m_inner Γ⊑ C-inner⊑
  ... | τ_₁ , τ⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
        _ , ⊑+ τ⊑ ⊑□ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , sι₁ inner-cls

  lift-syn-cov (minSι₂ m_inner) Γ⊑ (⊑ι₂ C-inner⊑)
    with lift-syn-cov m_inner Γ⊑ C-inner⊑
  ... | τ_₁ , τ⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
        _ , ⊑+ ⊑□ τ⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , sι₂ inner-cls

  lift-syn-cov (minSπ₁ {eq = eq} m_inner) Γ⊑ (⊑π₁ C-inner⊑)
    with lift-syn-cov m_inner Γ⊑ C-inner⊑
  ... | τ_₁ , τ⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls
    with ⊔-×-⊑ τ⊑ eq
  ... | τ_a , τ_b , eq_₁ , pa , _ =
        _ , pa , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , sπ₁ inner-cls eq_₁

  lift-syn-cov (minSπ₂ {eq = eq} m_inner) Γ⊑ (⊑π₂ C-inner⊑)
    with lift-syn-cov m_inner Γ⊑ C-inner⊑
  ... | τ_₁ , τ⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls
    with ⊔-×-⊑ τ⊑ eq
  ... | τ_a , τ_b , eq_₁ , _ , pb =
        _ , pb , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , sπ₂ inner-cls eq_₁

  lift-syn-cov (minSΛ m_inner) Γ⊑ (⊑Λ C-inner⊑)
    with lift-syn-cov m_inner (shiftΓ-⊑ Γ⊑) C-inner⊑
  ... | τ_₁ , τ⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
        _ , ⊑∀ τ⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , sΛ inner-cls

  lift-syn-cov (minSdef₁ {d₂ = d₂} m_inner) Γ⊑ (⊑def₁ C-inner⊑ e⊑)
    with lift-syn-cov m_inner Γ⊑ C-inner⊑
  ... | τ'_₁ , τ'⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls
    with static-gradual-syn (⊑∷ τ'⊑ Γ⊑) e⊑ d₂
  ... | τ_₁ , d₂_₁ , τ⊑ =
        _ , τ⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
        sdef₁ inner-cls d₂_₁

  lift-syn-cov (minSdef₂ {D = D} m_inner _ _ _ _ _) Γ⊑ (⊑def₂ e⊑ C-inner⊑)
    with static-gradual-syn Γ⊑ e⊑ D
  ... | τ'_₁ , D_₁ , τ'⊑
    with lift-syn-cov m_inner (⊑∷ τ'⊑ Γ⊑) C-inner⊑
  ... | τ_₁ , τ⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov , inner-cls =
        _ , τ⊑ , _ , _ , _ , Γ_f⊑ , τ_f⊑ , cov ,
        sdef₂ D_₁ inner-cls
