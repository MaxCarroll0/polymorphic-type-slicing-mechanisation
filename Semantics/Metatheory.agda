-- Metatheoretic well-formedness preservation lemmas for the elaboration relation.
module Semantics.Metatheory where
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat hiding (_+_; _⊔_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Sum using (_⊎_)
open import Data.Product using (∃; Σ; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core
open import Core.IntExp as I
open import Core.Typ.Consistency using (~-isCompatibility; IsCompatibility; _~_)
open import Core.Typ.Precision using (⊑to~)
open import Core.Typ.Properties
open import Core.Typ.Lattice using (module ~)
open import Semantics.Statics.Typing
open import Semantics.Dynamics.Typing as IT
open import Semantics.Dynamics.Values
open import Semantics.Dynamics.EvalCtx
open import Semantics.Dynamics.Step
open import Semantics.Elaboration

-- Lookup preserves Well-formedness 
wfΓ-lookup : ∀ {n Γ k τ} → n ⊢wfΓ Γ → Γ at k ≡ just τ → n ⊢wf τ
wfΓ-lookup wfΓ[]                    ()
wfΓ-lookup {k = zero}  (wfΓ∷ wfτ _) refl = wfτ
wfΓ-lookup {k = suc _} (wfΓ∷ _ wfΓ) eq   = wfΓ-lookup wfΓ eq

-- Synthesized types are well-formed (given a well-formed context)
syn-wf : ∀ {n Γ e τ d} → n ⊢wfΓ Γ → n , Γ ⊢ e ⇑ τ ↝ d → n ⊢wf τ
syn-wf wfΓ elab⇑*                     = wf*
syn-wf wfΓ elab⇑□                     = wf□
syn-wf wfΓ (elab⇑Var p)               = wfΓ-lookup wfΓ p
syn-wf wfΓ (elab⇑λ: wf ed)            = wf⇒ wf (syn-wf (wfΓ∷ wf wfΓ) ed)
syn-wf wfΓ (elab⇑Λ ed)                = wf∀ (syn-wf (shiftΓ₁-preserves-wf wfΓ) ed)
syn-wf wfΓ (elab⇑∘ ed₁ m ed₂)         = ⊔-⇒-wf₂ (syn-wf wfΓ ed₁) m
syn-wf wfΓ (elab⇑<> ed m wf)          = sub-preserves-wf wf (⊔-∀-wf (syn-wf wfΓ ed) m)
syn-wf wfΓ (elab⇑& ed₁ ed₂)           = wf× (syn-wf wfΓ ed₁) (syn-wf wfΓ ed₂)
syn-wf wfΓ (elab⇑π₁ ed m)             = ⊔-×-wf₁ (syn-wf wfΓ ed) m
syn-wf wfΓ (elab⇑π₂ ed m)             = ⊔-×-wf₂ (syn-wf wfΓ ed) m
syn-wf wfΓ (elab⇑def ed₁ ed₂)         = syn-wf (wfΓ∷ (syn-wf wfΓ ed₁) wfΓ) ed₂
syn-wf wfΓ (elab⇑case ed m ed₁ ed₂ c) =
  let wfτ = syn-wf wfΓ ed
  in ⊔-wf (syn-wf (wfΓ∷ (⊔-+-wf₁ wfτ m) wfΓ) ed₁)
           (syn-wf (wfΓ∷ (⊔-+-wf₂ wfτ m) wfΓ) ed₂)
           c
syn-wf wfΓ (elab⇑ι₁ ed)               = wf+ (syn-wf wfΓ ed) wf□
syn-wf wfΓ (elab⇑ι₂ ed)               = wf+ wf□ (syn-wf wfΓ ed)

-- Elaboration Completeness
mutual
  elab-complete-syn : ∀ {n Γ e τ}
                      → n , Γ ⊢ e ⇑ τ →
                      ∃[ d ] n , Γ ⊢ e ⇑ τ ↝ d
  elab-complete-syn ⇑* = * , elab⇑*
  elab-complete-syn ⇑□ = □ , elab⇑□
  elab-complete-syn (⇑Var p) = ⟨ _ ⟩ , elab⇑Var p
  elab-complete-syn (⇑λ: wf D)
    with elab-complete-syn D
  ...  | d , ed = λ: _ ⇒ d , elab⇑λ: wf ed
  elab-complete-syn (⇑def D₁ D₂)
    with elab-complete-syn D₁ | elab-complete-syn D₂
  ...  | d₁ , ed₁             | d₂ , ed₂
       = def d₁ ⊢ d₂ , elab⇑def ed₁ ed₂
  elab-complete-syn (⇑Λ D)
    with elab-complete-syn D
  ...  | d , ed = Λ d , elab⇑Λ ed
  elab-complete-syn (⇑∘ D₁ m D₂)
    with elab-complete-syn D₁ | elab-complete-ana D₂
  ...  | d₁ , ed₁             | d₂ , ed₂
       = (d₁ ⟪ _ ⇛ _ ⟫) ∘ d₂ , elab⇑∘ ed₁ m ed₂
  elab-complete-syn (⇑<> D m wf)
    with elab-complete-syn D
  ...  | d , ed = (d ⟪ _ ⇛ _ ⟫) < _ > , elab⇑<> ed m wf
  elab-complete-syn (⇑& D₁ D₂)
    with elab-complete-syn D₁ | elab-complete-syn D₂
  ...  | d₁ , ed₁ | d₂ , ed₂ = d₁ & d₂ , elab⇑& ed₁ ed₂
  elab-complete-syn (⇑π₁ D m)
    with elab-complete-syn D
  ...  | d , ed = π₁ (d ⟪ _ ⇛ _ ⟫) , elab⇑π₁ ed m
  elab-complete-syn (⇑π₂ D m)
    with elab-complete-syn D
  ...  | d , ed = π₂ (d ⟪ _ ⇛ _ ⟫) , elab⇑π₂ ed m
  elab-complete-syn (⇑case D m D₁ D₂ c)
    with elab-complete-syn D | elab-complete-syn D₁ | elab-complete-syn D₂
  ...  | d , ed              | d₁ , ed₁             | d₂ , ed₂
       = case (d ⟪ _ ⇛ _ ⟫) of (d₁ ⟪ _ ⇛ _ ⟫) · (d₂ ⟪ _ ⇛ _ ⟫)
         , elab⇑case ed m ed₁ ed₂ c
  elab-complete-syn (⇑ι₁ D)
    with elab-complete-syn D
  ...  | d , ed = ι₁ d , elab⇑ι₁ ed
  elab-complete-syn (⇑ι₂ D)
    with elab-complete-syn D
  ...  | d , ed = ι₂ d , elab⇑ι₂ ed

  elab-complete-ana : ∀ {n Γ e τ}
                      → n , Γ ⊢ e ⇓ τ →
                      ∃[ d ] n , Γ ⊢ e ⇓ τ ↝ d
  elab-complete-ana (⇓Sub D c)
    with elab-complete-syn D
  ...  | d , ed = d ⟪ _ ⇛ _ ⟫ , elab⇓sub ed c
  elab-complete-ana (⇓λ m D)
    with elab-complete-ana D
  ...  | d , ed = (λ: _ ⇒ d) ⟪ _ ⇛ _ ⟫ , elab⇓λ m ed
  elab-complete-ana (⇓case D m D₁ D₂)
    with elab-complete-syn D | elab-complete-ana D₁ | elab-complete-ana D₂
  ...  | d , ed              | d₁ , ed₁             | d₂ , ed₂
       = case (d ⟪ _ ⇛ _ ⟫) of d₁ · d₂ , elab⇓case ed m ed₁ ed₂
  elab-complete-ana (⇓ι₁ m D)
    with elab-complete-ana D
  ...  | d , ed = (ι₁ d) ⟪ _ ⇛ _ ⟫ , elab⇓ι₁ m ed
  elab-complete-ana (⇓ι₂ m D)
    with elab-complete-ana D
  ...  | d , ed = (ι₂ d) ⟪ _ ⇛ _ ⟫ , elab⇓ι₂ m ed
  elab-complete-ana (⇓& m D₁ D₂)
    with elab-complete-ana D₁ | elab-complete-ana D₂
  ...  | d₁ , ed₁ | d₂ , ed₂ = (d₁ & d₂) ⟪ _ ⇛ _ ⟫ , elab⇓& m ed₁ ed₂
  elab-complete-ana (⇓λ: c m wf D)
    with elab-complete-ana D
  ...  | d , ed = (λ: _ ⇒ d) ⟪ _ ⇛ _ ⟫ ⟪ _ ⇛ _ ⟫ , elab⇓λ: c m wf ed
  elab-complete-ana (⇓def D₁ D₂)
    with elab-complete-syn D₁ | elab-complete-ana D₂
  ...  | d₁ , ed₁             | d₂ , ed₂
       = def d₁ ⊢ d₂ , elab⇓def ed₁ ed₂

-- Elaboration Soundness
mutual
  elab-sound-int-syn : ∀ {n Γ e τ d}
                       → n ⊢wfΓ Γ
                       → n , Γ ⊢ e ⇑ τ ↝ d
                       → n , Γ ⊢ d ∶ τ
  elab-sound-int-syn wfΓ elab⇑*             = ∶*
  elab-sound-int-syn wfΓ elab⇑□             = ∶□
  elab-sound-int-syn wfΓ (elab⇑Var p)       = ∶Var p
  elab-sound-int-syn wfΓ (elab⇑λ: wf ed)    = ∶λ   wf (elab-sound-int-syn (wfΓ∷ wf wfΓ) ed)
  elab-sound-int-syn wfΓ (elab⇑Λ ed)        = ∶Λ   (elab-sound-int-syn (shiftΓ₁-preserves-wf wfΓ) ed)
  elab-sound-int-syn wfΓ (elab⇑∘ ed₁ m ed₂) = ∶∘   (∶cast (elab-sound-int-syn wfΓ ed₁)
                                                          (⊔-~-result (⊔-⇒-~ m) m))
                                                   (elab-sound-int-ana wfΓ
                                                     (⊔-⇒-wf₁ (syn-wf wfΓ ed₁) m) ed₂)
  elab-sound-int-syn wfΓ (elab⇑<> ed m wf)  = ∶<>  (∶cast (elab-sound-int-syn wfΓ ed)
                                                          (⊔-~-result (⊔-∀-~ m) m))
                                                   wf
  elab-sound-int-syn wfΓ (elab⇑& ed₁ ed₂)   = ∶&   (elab-sound-int-syn wfΓ ed₁)
                                                   (elab-sound-int-syn wfΓ ed₂)
  elab-sound-int-syn wfΓ (elab⇑π₁ ed m)     = ∶π₁  (∶cast (elab-sound-int-syn wfΓ ed)
                                                          (⊔-~-result (⊔-×-~ m) m))
  elab-sound-int-syn wfΓ (elab⇑π₂ ed m)     = ∶π₂  (∶cast (elab-sound-int-syn wfΓ ed)
                                                          (⊔-~-result (⊔-×-~ m) m))
  elab-sound-int-syn wfΓ (elab⇑def ed₁ ed₂) = ∶def (elab-sound-int-syn wfΓ ed₁)
                                                   (elab-sound-int-syn (wfΓ∷ (syn-wf wfΓ ed₁) wfΓ) ed₂)
  elab-sound-int-syn wfΓ (elab⇑case ed m ed₁ ed₂ c) =
    let wfτ = syn-wf wfΓ ed
    in ∶case (∶cast (elab-sound-int-syn wfΓ ed) (⊔-~-result (⊔-+-~ m) m))
             (∶cast (elab-sound-int-syn (wfΓ∷ (⊔-+-wf₁ wfτ m) wfΓ) ed₁)
                    (⊑to~ (~.⊔-ub₁ c)))
             (∶cast (elab-sound-int-syn (wfΓ∷ (⊔-+-wf₂ wfτ m) wfΓ) ed₂)
                    (⊑to~ (~.⊔-ub₂ c)))
  elab-sound-int-syn wfΓ (elab⇑ι₁ ed)       = ∶ι₁  wf□ (elab-sound-int-syn wfΓ ed)
  elab-sound-int-syn wfΓ (elab⇑ι₂ ed)       = ∶ι₂  wf□ (elab-sound-int-syn wfΓ ed)

  elab-sound-int-ana : ∀ {n Γ e τ d}
                       → n ⊢wfΓ Γ → n ⊢wf τ
                       → n , Γ ⊢ e ⇓ τ ↝ d
                       → n , Γ ⊢ d ∶ τ
  elab-sound-int-ana wfΓ wfτ (elab⇓sub ed c)     = ∶cast (elab-sound-int-syn wfΓ ed)
                                                         (~.sym c)
  elab-sound-int-ana wfΓ wfτ (elab⇓λ m ed)       = ∶cast (∶λ (⊔-⇒-wf₁ wfτ m)
                                                             (elab-sound-int-ana
                                                               (wfΓ∷ (⊔-⇒-wf₁ wfτ m) wfΓ)
                                                               (⊔-⇒-wf₂ wfτ m) ed))
                                                         (~.sym (⊔-~-result (⊔-⇒-~ m) m))
  elab-sound-int-ana wfΓ wfτ (elab⇓λ: c m wf ed)
    = ∶cast (∶cast (∶λ wf (elab-sound-int-ana (wfΓ∷ wf wfΓ) (⊔-ann-⇒-wf₂ wfτ wf m) ed))
                   (⊔-ann-⇒-~λ c m))
            (~.sym (⊔-~-result c m))
  elab-sound-int-ana wfΓ wfτ (elab⇓ι₁ m ed)      = ∶cast (∶ι₁ (⊔-+-wf₂ wfτ m)
                                                              (elab-sound-int-ana wfΓ
                                                                (⊔-+-wf₁ wfτ m) ed))
                                                         (~.sym (⊔-~-result (⊔-+-~ m) m))
  elab-sound-int-ana wfΓ wfτ (elab⇓ι₂ m ed)      = ∶cast (∶ι₂ (⊔-+-wf₁ wfτ m)
                                                              (elab-sound-int-ana wfΓ
                                                                (⊔-+-wf₂ wfτ m) ed))
                                                         (~.sym (⊔-~-result (⊔-+-~ m) m))
  elab-sound-int-ana wfΓ wfτ (elab⇓& m ed₁ ed₂)  = ∶cast (∶& (elab-sound-int-ana wfΓ
                                                                 (⊔-×-wf₁ wfτ m) ed₁)
                                                              (elab-sound-int-ana wfΓ
                                                                 (⊔-×-wf₂ wfτ m) ed₂))
                                                         (~.sym (⊔-~-result (⊔-×-~ m) m))
  elab-sound-int-ana wfΓ wfτ (elab⇓case ed m ed₁ ed₂)
    = let wfτ₀ = syn-wf wfΓ ed
      in ∶case (∶cast (elab-sound-int-syn wfΓ ed) (⊔-~-result (⊔-+-~ m) m))
               (elab-sound-int-ana (wfΓ∷ (⊔-+-wf₁ wfτ₀ m) wfΓ) wfτ ed₁)
               (elab-sound-int-ana (wfΓ∷ (⊔-+-wf₂ wfτ₀ m) wfΓ) wfτ ed₂)
  elab-sound-int-ana wfΓ wfτ (elab⇓def ed₁ ed₂)  = ∶def  (elab-sound-int-syn wfΓ ed₁)
                                                         (elab-sound-int-ana
                                                           (wfΓ∷ (syn-wf wfΓ ed₁) wfΓ)
                                                           wfτ ed₂)

mutual
  elab-sound-ext-syn : ∀ {n Γ e τ d} → n , Γ ⊢ e ⇑ τ ↝ d → n , Γ ⊢ e ⇑ τ
  elab-sound-ext-syn elab⇑*                   = ⇑*
  elab-sound-ext-syn elab⇑□                   = ⇑□
  elab-sound-ext-syn (elab⇑Var p)             = ⇑Var p
  elab-sound-ext-syn (elab⇑λ: wf ed)          = ⇑λ:  wf (elab-sound-ext-syn ed)
  elab-sound-ext-syn (elab⇑Λ ed)              = ⇑Λ   (elab-sound-ext-syn ed)
  elab-sound-ext-syn (elab⇑∘ ed₁ m ed₂)       = ⇑∘   (elab-sound-ext-syn ed₁) m
                                                     (elab-sound-ext-ana ed₂)
  elab-sound-ext-syn (elab⇑<> ed m wf)        = ⇑<>  (elab-sound-ext-syn ed) m wf
  elab-sound-ext-syn (elab⇑& ed₁ ed₂)         = ⇑&   (elab-sound-ext-syn ed₁)
                                                     (elab-sound-ext-syn ed₂)
  elab-sound-ext-syn (elab⇑π₁ ed m)           = ⇑π₁  (elab-sound-ext-syn ed) m
  elab-sound-ext-syn (elab⇑π₂ ed m)           = ⇑π₂  (elab-sound-ext-syn ed) m
  elab-sound-ext-syn (elab⇑def ed₁ ed₂)       = ⇑def (elab-sound-ext-syn ed₁)
                                                     (elab-sound-ext-syn ed₂)
  elab-sound-ext-syn (elab⇑case ed m ed₁ ed₂ c) =
    ⇑case (elab-sound-ext-syn ed) m (elab-sound-ext-syn ed₁) (elab-sound-ext-syn ed₂) c
  elab-sound-ext-syn (elab⇑ι₁ ed)             = ⇑ι₁ (elab-sound-ext-syn ed)
  elab-sound-ext-syn (elab⇑ι₂ ed)             = ⇑ι₂ (elab-sound-ext-syn ed)

  elab-sound-ext-ana : ∀ {n Γ e τ d} →
    n , Γ ⊢ e ⇓ τ ↝ d → n , Γ ⊢ e ⇓ τ
  elab-sound-ext-ana (elab⇓sub ed c)          = ⇓Sub  (elab-sound-ext-syn ed) c
  elab-sound-ext-ana (elab⇓λ m ed)            = ⇓λ    m (elab-sound-ext-ana ed)
  elab-sound-ext-ana (elab⇓λ: c m wf ed)      = ⇓λ:   c m wf (elab-sound-ext-ana ed)
  elab-sound-ext-ana (elab⇓ι₁ m ed)           = ⇓ι₁   m (elab-sound-ext-ana ed)
  elab-sound-ext-ana (elab⇓ι₂ m ed)           = ⇓ι₂   m (elab-sound-ext-ana ed)
  elab-sound-ext-ana (elab⇓& m ed₁ ed₂)       = ⇓&    m (elab-sound-ext-ana ed₁)
                                                      (elab-sound-ext-ana ed₂)
  elab-sound-ext-ana (elab⇓case ed m ed₁ ed₂) = ⇓case (elab-sound-ext-syn ed) m
                                                      (elab-sound-ext-ana ed₁)
                                                      (elab-sound-ext-ana ed₂)
  elab-sound-ext-ana (elab⇓def ed₁ ed₂)       = ⇓def  (elab-sound-ext-syn ed₁)
                                                      (elab-sound-ext-ana ed₂)

-- Type Safety
-- TODO: Preservation needs substitution lemma for IntExp typing + plug decomposition.
-- Progress needs canonical forms lemma.
postulate
  preservation : ∀ {n Γ d d' τ} →
    n , Γ ⊢ d ∶ τ → d ↦ d' → n , Γ ⊢ d' ∶ τ

  progress : ∀ {d τ} →
    zero , [] ⊢ d ∶ τ → Final d ⊎ (∃[ d' ] d ↦ d')

-- Gradual Guarantee
open import Semantics.Graduality public
  using (static-gradual-syn; static-gradual-ana)
