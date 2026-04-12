module Semantics.Metatheory where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (_⊎_)
open import Data.Product using (∃; Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core
open import Core.IntExp as I
open import Core.Typ.Consistency using (~-isCompatibility; IsCompatibility; _~_)
open import Core.Typ.Precision using (⊑to~)
open import Core.Typ.Properties using (⊔-⇒-~; ⊔-+-~; ⊔-×-~; ⊔-∀-~; ⊔-~-result)
open import Core.Typ.Lattice using (module ~)
open import Semantics.Statics.Typing
open import Semantics.Dynamics.Typing as IT
open import Semantics.Dynamics.Values
open import Semantics.Dynamics.EvalCtx
open import Semantics.Dynamics.Step
open import Semantics.Elaboration

-- Postulated: well-formedness of join components (needs wf of analysis type as precondition)
-- These hold when the analysis type τ is well-formed, which is a standard assumption
-- in a well-formed typing context but is not explicitly tracked by the elaboration rules.
postulate
  ⊔-⇒-wf₁  : ∀ {n τ τ₁ τ₂} → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂ → n ⊢wf τ₁
  ⊔-+-wf₁  : ∀ {n τ τ₁ τ₂} → τ ⊔ □ + □ ≡ τ₁ + τ₂ → n ⊢wf τ₁
  ⊔-+-wf₂  : ∀ {n τ τ₁ τ₂} → τ ⊔ □ + □ ≡ τ₁ + τ₂ → n ⊢wf τ₂

-- Elaboration Completeness
mutual
  elab-complete-syn : ∀ {n Γ e τ} →
    n ； Γ ⊢ e ↦ τ → ∃ λ d → n ； Γ ⊢ e ⇑ τ ↝ d
  elab-complete-syn ↦* =
    * , elab↦*
  elab-complete-syn ↦□ =
    □ , elab↦□
  elab-complete-syn (↦Var p) =
    ⟨ _ ⟩ , elab↦Var p
  elab-complete-syn (↦λ: wf D)
    with elab-complete-syn D
  ... | d , ed =
    λ: _ ⇒ d , elab↦λ: wf ed
  elab-complete-syn (↦def D₁ D₂)
    with elab-complete-syn D₁ | elab-complete-syn D₂
  ... | d₁ , ed₁ | d₂ , ed₂ =
    def d₁ ⊢ d₂ , elab↦def ed₁ ed₂
  elab-complete-syn (↦Λ D)
    with elab-complete-syn D
  ... | d , ed =
    Λ d , elab↦Λ ed
  elab-complete-syn (↦∘ D₁ m D₂)
    with elab-complete-syn D₁ | elab-complete-ana D₂
  ... | d₁ , ed₁ | d₂ , ed₂ =
    (d₁ ⟪ _ ⇛ _ ⟫) ∘ d₂ , elab↦∘ ed₁ m ed₂
  elab-complete-syn (↦<> D m wf)
    with elab-complete-syn D
  ... | d , ed =
    (d ⟪ _ ⇛ _ ⟫) < _ > , elab↦<> ed m wf
  elab-complete-syn (↦& D₁ D₂)
    with elab-complete-syn D₁ | elab-complete-syn D₂
  ... | d₁ , ed₁ | d₂ , ed₂ =
    d₁ & d₂ , elab↦& ed₁ ed₂
  elab-complete-syn (↦π₁ D m)
    with elab-complete-syn D
  ... | d , ed =
    π₁ (d ⟪ _ ⇛ _ ⟫) , elab↦π₁ ed m
  elab-complete-syn (↦π₂ D m)
    with elab-complete-syn D
  ... | d , ed =
    π₂ (d ⟪ _ ⇛ _ ⟫) , elab↦π₂ ed m
  elab-complete-syn (↦case D m D₁ D₂ c)
    with elab-complete-syn D | elab-complete-syn D₁ | elab-complete-syn D₂
  ... | d , ed | d₁ , ed₁ | d₂ , ed₂ =
    case (d ⟪ _ ⇛ _ ⟫) of (d₁ ⟪ _ ⇛ _ ⟫) · (d₂ ⟪ _ ⇛ _ ⟫)
    , elab↦case ed m ed₁ ed₂ c

  elab-complete-ana : ∀ {n Γ e τ} →
    n ； Γ ⊢ e ↤ τ → ∃ λ d → n ； Γ ⊢ e ⇓ τ ↝ d
  elab-complete-ana (↤Sub D c)
    with elab-complete-syn D
  ... | d , ed =
    d ⟪ _ ⇛ _ ⟫ , elab↤sub ed c
  elab-complete-ana (↤λ m D)
    with elab-complete-ana D
  ... | d , ed =
    (λ: _ ⇒ d) ⟪ _ ⇛ _ ⟫ , elab↤λ m ed
  elab-complete-ana (↤case D m D₁ D₂)
    with elab-complete-syn D | elab-complete-ana D₁ | elab-complete-ana D₂
  ... | d , ed | d₁ , ed₁ | d₂ , ed₂ =
    case (d ⟪ _ ⇛ _ ⟫) of d₁ · d₂ , elab↤case ed m ed₁ ed₂
  elab-complete-ana (↤ι₁ m D)
    with elab-complete-ana D
  ... | d , ed =
    (ι₁ d) ⟪ _ ⇛ _ ⟫ , elab↤ι₁ m ed
  elab-complete-ana (↤ι₂ m D)
    with elab-complete-ana D
  ... | d , ed =
    (ι₂ d) ⟪ _ ⇛ _ ⟫ , elab↤ι₂ m ed
  elab-complete-ana (↤& m D₁ D₂)
    with elab-complete-ana D₁ | elab-complete-ana D₂
  ... | d₁ , ed₁ | d₂ , ed₂ =
    (d₁ & d₂) ⟪ _ ⇛ _ ⟫ , elab↤& m ed₁ ed₂
  elab-complete-ana (↤λ: c m wf D)
    with elab-complete-ana D
  ... | d , ed =
    (λ: _ ⇒ d) ⟪ _ ⇛ _ ⟫ , elab↤λ: c m wf ed
  elab-complete-ana (↤def D₁ D₂)
    with elab-complete-syn D₁ | elab-complete-ana D₂
  ... | d₁ , ed₁ | d₂ , ed₂ =
    def d₁ ⊢ d₂ , elab↤def ed₁ ed₂

-- Elaboration Soundness
mutual
  elab-sound-int-syn : ∀ {n Γ e τ d} →
    n ； Γ ⊢ e ⇑ τ ↝ d → n ； Γ ⊢ d ∶ τ
  elab-sound-int-syn elab↦*             = ∶*
  elab-sound-int-syn elab↦□             = ∶□
  elab-sound-int-syn (elab↦Var p)       = ∶Var p
  elab-sound-int-syn (elab↦λ: wf ed)    = ∶λ wf (elab-sound-int-syn ed)
  elab-sound-int-syn (elab↦Λ ed)        = ∶Λ (elab-sound-int-syn ed)
  elab-sound-int-syn (elab↦∘ ed₁ m ed₂) =
    ∶∘ (∶cast (elab-sound-int-syn ed₁) (⊔-~-result (⊔-⇒-~ m) m)) (elab-sound-int-ana ed₂)
  elab-sound-int-syn (elab↦<> ed m wf)  =
    ∶<> (∶cast (elab-sound-int-syn ed) (⊔-~-result (⊔-∀-~ m) m)) wf
  elab-sound-int-syn (elab↦& ed₁ ed₂)   =
    ∶& (elab-sound-int-syn ed₁) (elab-sound-int-syn ed₂)
  elab-sound-int-syn (elab↦π₁ ed m)     =
    ∶π₁ (∶cast (elab-sound-int-syn ed) (⊔-~-result (⊔-×-~ m) m))
  elab-sound-int-syn (elab↦π₂ ed m)     =
    ∶π₂ (∶cast (elab-sound-int-syn ed) (⊔-~-result (⊔-×-~ m) m))
  elab-sound-int-syn (elab↦def ed₁ ed₂) =
    ∶def (elab-sound-int-syn ed₁) (elab-sound-int-syn ed₂)
  elab-sound-int-syn (elab↦case ed m ed₁ ed₂ c) =
    ∶case (∶cast (elab-sound-int-syn ed) (⊔-~-result (⊔-+-~ m) m))
          (∶cast (elab-sound-int-syn ed₁) (⊑to~ (~.⊔-ub₁ c)))
          (∶cast (elab-sound-int-syn ed₂) (⊑to~ (~.⊔-ub₂ c)))

  elab-sound-int-ana : ∀ {n Γ e τ d} →
    n ； Γ ⊢ e ⇓ τ ↝ d → n IT.； Γ ⊢ d ∶ τ
  elab-sound-int-ana (elab↤sub ed c) =
    ∶cast (elab-sound-int-syn ed) (~.sym c)
  elab-sound-int-ana (elab↤λ {τ = τ} m ed) =
    ∶cast (∶λ (⊔-⇒-wf₁ {τ = τ} m) (elab-sound-int-ana ed)) (~.sym (⊔-~-result (⊔-⇒-~ m) m))
  elab-sound-int-ana (elab↤λ: c m wf ed) =
    ∶cast (∶λ wf (elab-sound-int-ana ed)) (~.sym (⊔-~-result c m))
  elab-sound-int-ana (elab↤ι₁ {τ = τ} m ed) =
    ∶cast (∶ι₁ (⊔-+-wf₂ {τ = τ} m) (elab-sound-int-ana ed)) (~.sym (⊔-~-result (⊔-+-~ m) m))
  elab-sound-int-ana (elab↤ι₂ {τ = τ} m ed) =
    ∶cast (∶ι₂ (⊔-+-wf₁ {τ = τ} m) (elab-sound-int-ana ed)) (~.sym (⊔-~-result (⊔-+-~ m) m))
  elab-sound-int-ana (elab↤& m ed₁ ed₂) =
    ∶cast (∶& (elab-sound-int-ana ed₁) (elab-sound-int-ana ed₂)) (~.sym (⊔-~-result (⊔-×-~ m) m))
  elab-sound-int-ana (elab↤case ed m ed₁ ed₂) =
    ∶case (∶cast (elab-sound-int-syn ed) (⊔-~-result (⊔-+-~ m) m))
          (elab-sound-int-ana ed₁) (elab-sound-int-ana ed₂)
  elab-sound-int-ana (elab↤def ed₁ ed₂) =
    ∶def (elab-sound-int-syn ed₁) (elab-sound-int-ana ed₂)

postulate
  elab-sound-ext-syn : ∀ {n Γ e τ d} →
    n ； Γ ⊢ e ⇑ τ ↝ d → n ； Γ ⊢ e ↦ τ
  elab-sound-ext-ana : ∀ {n Γ e τ d} →
    n ； Γ ⊢ e ⇓ τ ↝ d → n ； Γ ⊢ e ↤ τ

-- Type Safety
-- TODO: Preservation needs substitution lemma for IntExp typing + plug decomposition.
-- Progress needs canonical forms lemma.
postulate
  preservation : ∀ {n Γ d d' τ} →
    n ； Γ ⊢ d ∶ τ → d ↦ d' → n ； Γ ⊢ d' ∶ τ

  progress : ∀ {d τ} →
    zero IT.； [] ⊢ d ∶ τ → Final d ⊎ (∃ λ d' → d ↦ d')

-- Gradual Guarantee
-- TODO: Needs precision/typing monotonicity
postulate
  static-gradual-syn : ∀ {n Γ₁ Γ₂ e₁ e₂ τ₁} →
    e₁ ⊑ e₂ → Γ₁ ⊑ Γ₂ →
    n ； Γ₁ ⊢ e₁ ↦ τ₁ →
    ∃ λ τ₂ → n ； Γ₂ ⊢ e₂ ↦ τ₂
