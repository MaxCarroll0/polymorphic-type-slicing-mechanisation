module Semantics.Marking.Metatheory where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (∃; Σ; _,_; ∃-syntax)
open import Data.Product using () renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Core
open import Core.MExp
open import Core.Typ.Base as T using (Typ; _⇒_; _+_; _×_; ∀·)
  renaming (□ to T□; * to T*)
open import Core.Typ.Consistency using (_~?_; _~_)
open import Semantics.Statics.Typing
open import Semantics.Marking.Judgment
open import Semantics.Marking.Erasure

-- Well-formedness: erasure recovers original expression
mutual
  mark-wf-syn : ∀ {n Γ e ě τ} →
    n ； Γ ⊢ e ↬ ě ⇑ τ → erase ě ≡ e
  mark-wf-syn mark↦*            = refl
  mark-wf-syn mark↦□            = refl
  mark-wf-syn (mark↦Var _)      = refl
  mark-wf-syn (mark↦Var⇑ _)     = refl
  mark-wf-syn (mark↦λ: _ d)     = cong (λ: _ ⇒_) (mark-wf-syn d)
  mark-wf-syn (mark↦Λ d)        = cong Λ (mark-wf-syn d)
  mark-wf-syn (mark↦∘ d₁ _ d₂)  = cong₂ _∘_ (mark-wf-syn d₁) (mark-wf-ana d₂)
  mark-wf-syn (mark↦∘⇑ d₁ _ d₂) = cong₂ _∘_ (mark-wf-syn d₁) (mark-wf-ana d₂)
  mark-wf-syn (mark↦<> d _ _)   = cong (_< _ >) (mark-wf-syn d)
  mark-wf-syn (mark↦<>⇑ d _ _)  = cong (_< _ >) (mark-wf-syn d)
  mark-wf-syn (mark↦& d₁ d₂)    = cong₂ _&_ (mark-wf-syn d₁) (mark-wf-syn d₂)
  mark-wf-syn (mark↦def d₁ d₂)  = cong₂ (def_⊢_) (mark-wf-syn d₁) (mark-wf-syn d₂)
  mark-wf-syn (mark↦π₁ d _)     = cong π₁ (mark-wf-syn d)
  mark-wf-syn (mark↦π₁⇑ d _)    = cong π₁ (mark-wf-syn d)
  mark-wf-syn (mark↦π₂ d _)     = cong π₂ (mark-wf-syn d)
  mark-wf-syn (mark↦π₂⇑ d _)    = cong π₂ (mark-wf-syn d)
  mark-wf-syn (mark↦case d _ d₁ d₂ _)
    rewrite mark-wf-syn d | mark-wf-syn d₁ | mark-wf-syn d₂ = refl
  mark-wf-syn (mark↦case⇑ d _ d₁ d₂)
    rewrite mark-wf-syn d | mark-wf-syn d₁ | mark-wf-syn d₂ = refl
  mark-wf-syn (mark↦case≁ d _ d₁ d₂ _)
    rewrite mark-wf-syn d | mark-wf-syn d₁ | mark-wf-syn d₂ = refl
  mark-wf-syn (mark↦λ⇒ d)       = cong λ⇒_ (mark-wf-ana d)
  mark-wf-syn (mark↦ι₁ d)       = cong ι₁ (mark-wf-ana d)
  mark-wf-syn (mark↦ι₂ d)       = cong ι₂ (mark-wf-ana d)

  mark-wf-ana : ∀ {n Γ e ě τ} →
    n ； Γ ⊢ e ↬ ě ⇓ τ → erase ě ≡ e
  mark-wf-ana (mark↤sub d _)    = mark-wf-syn d
  mark-wf-ana (mark↤sub⇑ d _)   = mark-wf-syn d
  mark-wf-ana (mark↤λ _ d)      = cong λ⇒_ (mark-wf-ana d)
  mark-wf-ana (mark↤λ⇑ _ d)     = cong λ⇒_ (mark-wf-ana d)
  mark-wf-ana (mark↤λ: _ _ d)   = cong (λ: _ ⇒_) (mark-wf-ana d)
  mark-wf-ana (mark↤ι₁ _ d)     = cong ι₁ (mark-wf-ana d)
  mark-wf-ana (mark↤ι₂ _ d)     = cong ι₂ (mark-wf-ana d)
  mark-wf-ana (mark↤& _ d₁ d₂)  = cong₂ _&_ (mark-wf-ana d₁) (mark-wf-ana d₂)
  mark-wf-ana (mark↤def d₁ d₂)  = cong₂ (def_⊢_) (mark-wf-syn d₁) (mark-wf-ana d₂)
  mark-wf-ana (mark↤case d _ d₁ d₂)
    rewrite mark-wf-syn d | mark-wf-ana d₁ | mark-wf-ana d₂ = refl
  mark-wf-ana (mark↤case⇑ d _ d₁ d₂)
    rewrite mark-wf-syn d | mark-wf-ana d₁ | mark-wf-ana d₂ = refl

-- All type annotations in an expression are well-formed under n type variables
data _⊢wf-ann_ : ℕ → Exp → Set where
  wfa□    : ∀ {n}                                      → n ⊢wf-ann □
  wfa*    : ∀ {n}                                      → n ⊢wf-ann *
  wfaVar  : ∀ {n k}                                    → n ⊢wf-ann ⟨ k ⟩
  wfaλ:   : ∀ {n τ e}    → n ⊢wf τ      → n ⊢wf-ann e  → n ⊢wf-ann (λ: τ ⇒ e)
  wfaλ⇒   : ∀ {n e}      → n ⊢wf-ann e                 → n ⊢wf-ann (λ⇒ e)
  wfa∘    : ∀ {n e₁ e₂}  → n ⊢wf-ann e₁ → n ⊢wf-ann e₂ → n ⊢wf-ann (e₁ ∘ e₂)
  wfa<>   : ∀ {n e σ}    → n ⊢wf-ann e  → n ⊢wf σ      → n ⊢wf-ann (e < σ >)
  wfa&    : ∀ {n e₁ e₂}  → n ⊢wf-ann e₁ → n ⊢wf-ann e₂ → n ⊢wf-ann (e₁ & e₂)
  wfaι₁   : ∀ {n e}      → n ⊢wf-ann e                 → n ⊢wf-ann (ι₁ e)
  wfaι₂   : ∀ {n e}      → n ⊢wf-ann e                 → n ⊢wf-ann (ι₂ e)
  wfacase : ∀ {n e e₁ e₂}
            → n ⊢wf-ann e → n ⊢wf-ann e₁ → n ⊢wf-ann e₂ → n ⊢wf-ann (case e of e₁ · e₂)
  wfaπ₁   : ∀ {n e}      → n ⊢wf-ann e                  → n ⊢wf-ann (π₁ e)
  wfaπ₂   : ∀ {n e}      → n ⊢wf-ann e                  → n ⊢wf-ann (π₂ e)
  wfaΛ    : ∀ {n e}      → suc n ⊢wf-ann e              → n ⊢wf-ann (Λ e)
  wfadef  : ∀ {n e₁ e₂}  → n ⊢wf-ann e₁  → n ⊢wf-ann e₂ → n ⊢wf-ann (def e₁ ⊢ e₂)

-- Decidable type shape matching (a la hazelnut error-localization formalisation)
-- Rest of my codebase uses joins to express matching
private
  open T using (⟨_⟩)

  match⇒ : (τ : Typ) → Dec (∃[ τ₁ ] ∃[ τ₂ ] τ ≡ τ₁ ⇒ τ₂)
  match⇒ (_ ⇒ _)     = yes (_ , _ , refl)
  match⇒ ⟨ _ ⟩       = no λ where (_ , _ , ())
  match⇒ T*          = no λ where (_ , _ , ())
  match⇒ T□          = no λ where (_ , _ , ())
  match⇒ (T._+_ _ _) = no λ where (_ , _ , ())
  match⇒ (T._×_ _ _) = no λ where (_ , _ , ())
  match⇒ (∀· _)      = no λ where (_ , _ , ())

  match+ : (τ : Typ) → Dec (∃ λ τ₁ → ∃ λ τ₂ → τ ≡ τ₁ + τ₂)
  match+ (T._+_ _ _) = yes (_ , _ , refl)
  match+ ⟨ _ ⟩       = no λ where (_ , _ , ())
  match+ T*          = no λ where (_ , _ , ())
  match+ T□          = no λ where (_ , _ , ())
  match+ (_ ⇒ _)     = no λ where (_ , _ , ())
  match+ (T._×_ _ _) = no λ where (_ , _ , ())
  match+ (∀· _)      = no λ where (_ , _ , ())

  match× : (τ : Typ) → Dec (∃ λ τ₁ → ∃ λ τ₂ → τ ≡ τ₁ T.× τ₂)
  match× (T._×_ _ _) = yes (_ , _ , refl)
  match× ⟨ _ ⟩       = no λ where (_ , _ , ())
  match× T*          = no λ where (_ , _ , ())
  match× T□          = no λ where (_ , _ , ())
  match× (_ ⇒ _)     = no λ where (_ , _ , ())
  match× (T._+_ _ _) = no λ where (_ , _ , ())
  match× (∀· _)      = no λ where (_ , _ , ())

  match∀ : (τ : Typ) → Dec (∃ λ τ' → τ ≡ ∀· τ')
  match∀ (∀· _)      = yes (_ , refl)
  match∀ ⟨ _ ⟩       = no λ where (_ , ())
  match∀ T*          = no λ where (_ , ())
  match∀ T□          = no λ where (_ , ())
  match∀ (_ ⇒ _)     = no λ where (_ , ())
  match∀ (T._+_ _ _) = no λ where (_ , ())
  match∀ (T._×_ _ _) = no λ where (_ , ())

  ¬match₂ : ∀ {ρ : Typ} → ¬ (∃[ τ₁ ] ∃[ τ₂ ] ρ ≡ τ₁ ⇒ τ₂) → ∀ {τ₁ τ₂} → ρ ≢ τ₁ ⇒ τ₂
  ¬match₂ ¬m eq = ¬m (_ , _ , eq)

  ¬match₃ : ∀ {ρ : Typ} → ¬ (∃[ τ₁ ] ∃[ τ₂ ] ρ ≡ τ₁ + τ₂) → ∀ {τ₁ τ₂} → ρ ≢ τ₁ + τ₂
  ¬match₃ ¬m eq = ¬m (_ , _ , eq)

  ¬match₄ : ∀ {ρ : Typ} → ¬ (∃[ τ₁ ] ∃[ τ₂ ] ρ ≡ τ₁ T.× τ₂) → ∀ {τ₁ τ₂} → ρ ≢ τ₁ T.× τ₂
  ¬match₄ ¬m eq = ¬m (_ , _ , eq)

  ¬match₅ : ∀ {ρ : Typ} → ¬ (∃[ τ' ] ρ ≡ ∀· τ') → ∀ {τ'} → ρ ≢ ∀· τ'
  ¬match₅ ¬m eq = ¬m (_ , eq)

-- Totality: every well-annotated expression can be marked
-- As long as the annotations are well-scoped. TODO: add marks for type scoping issues
mutual
  mark-total-syn : ∀ {n} (Γ : Assms) (e : Exp) → n ⊢wf-ann e →
                   ∃[ ě ] ∃[ τ ] n ； Γ ⊢ e ↬ ě ⇑ τ

  mark-total-syn Γ * wfa* = * , T* , mark↦*
  mark-total-syn Γ □ wfa□ = □ , T□ , mark↦□
  mark-total-syn Γ ⟨ k ⟩ wfaVar
    with Γ at k in eq
  ...  | just τ  = ⟨ k ⟩ , τ , mark↦Var eq
  ...  | nothing = ⟨ k ⟩⇑ , T□ , mark↦Var⇑ eq
  mark-total-syn Γ (λ: τ ⇒ e) (wfaλ: wfτ wfe)
    with mark-total-syn (τ ∷ Γ) e wfe
  ...  | ě , τ₂ , d = (λ: τ ⇒ ě) , (τ ⇒ τ₂) , mark↦λ: wfτ d

  -- Analysis-only forms in synthesis position
  mark-total-syn Γ (λ⇒ e) (wfaλ⇒ wfe)
    with mark-total-ana Γ e T□ wfe
  ...  | ě , d     = (λ⇒ ě) ⦅~⇒⦆ , T□ , mark↦λ⇒ d
  mark-total-syn Γ (ι₁ e) (wfaι₁ wfe)
    with mark-total-ana Γ e T□ wfe
  ...  | ě , d     = (ι₁ ě) ⦅~+⦆ , T□ , mark↦ι₁ d
  mark-total-syn Γ (ι₂ e) (wfaι₂ wfe)
    with mark-total-ana Γ e T□ wfe
  ...  | ě , d     = ((ι₂ ě) ⦅~+⦆) , T□ , mark↦ι₂ d
  mark-total-syn Γ (Λ e) (wfaΛ wfe)
    with mark-total-syn (shiftΓ _ Γ) e wfe
  ...  | ě , τ , d = Λ ě , ∀· τ , mark↦Λ d

  mark-total-syn Γ (e₁ ∘ e₂) (wfa∘ wf₁ wf₂)
    with mark-total-syn Γ e₁ wf₁
  ...  | ě₁ , τ , d₁
       with match⇒ (τ ⊔ T□ ⇒ T□)
  ...     | yes (τ₁ , τ₂ , eq)
          with mark-total-ana Γ e₂ τ₁ wf₂
  ...        | ě₂ , d₂ = (ě₁ ∘ ě₂) , τ₂ , mark↦∘ d₁ eq d₂
  mark-total-syn Γ (e₁ ∘ e₂) (wfa∘ wf₁ wf₂)
       | ě₁ , τ , d₁
          | no ¬m -- Note: corresponds to the match⇒ above, TODO: use parallel with to make this proof more readable in general...
          with mark-total-ana Γ e₂ T□ wf₂
  ...        | ě₂ , d₂
               = ((ě₁ ⦅▸⇒⦆) ∘ ě₂) , T□ , mark↦∘⇑ d₁ (¬match₂ ¬m) d₂

  mark-total-syn Γ (e < σ >) (wfa<> wfe wfσ)
    with mark-total-syn Γ e wfe
  ...  | ě , τ , d
       with match∀ (τ ⊔ ∀· T□)
  ...     | yes (τ' , eq)
            = (ě < σ >) , _ , mark↦<> d eq wfσ
  ...     | no ¬m
            = ((ě ⦅▸∀⦆) < σ >) , T□ , mark↦<>⇑ d (¬match₅ ¬m) wfσ

  mark-total-syn Γ (e₁ & e₂) (wfa& wf₁ wf₂)
    with mark-total-syn Γ e₁ wf₁ | mark-total-syn Γ e₂ wf₂
  ...  | ě₁ , τ₁ , d₁            | ě₂ , τ₂ , d₂
         = (ě₁ & ě₂) , (τ₁ × τ₂) , mark↦& d₁ d₂

  mark-total-syn Γ (π₁ e) (wfaπ₁ wfe)
    with mark-total-syn Γ e wfe
  ...  | ě , τ , d
       with match× (τ ⊔ T□ T.× T□)
  ...     | yes (τ₁ , τ₂ , eq)
            = π₁ ě , τ₁ , mark↦π₁ d eq
  ...     | no ¬m
            = π₁ (ě ⦅▸×⦆) , T□ , mark↦π₁⇑ d (¬match₄ ¬m)

  mark-total-syn Γ (π₂ e) (wfaπ₂ wfe)
    with mark-total-syn Γ e wfe
  ...  | ě , τ , d
       with match× (τ ⊔ T□ T.× T□)
  ...     | yes (τ₁ , τ₂ , eq)
            = π₂ ě , τ₂ , mark↦π₂ d eq
  ...     | no ¬m
            = π₂ (ě ⦅▸×⦆) , T□ , mark↦π₂⇑ d (¬match₄ ¬m)

  mark-total-syn Γ (def e₁ ⊢ e₂) (wfadef wf₁ wf₂)
    with mark-total-syn Γ e₁ wf₁
  ...  | ě₁ , τ₁ , d₁
       with mark-total-syn (τ₁ ∷ Γ) e₂ wf₂
  ...     | ě₂ , τ₂ , d₂ = (def ě₁ ⊢ ě₂) , τ₂ , mark↦def d₁ d₂

  mark-total-syn Γ (case e of e₁ · e₂) (wfacase wfe wf₁ wf₂)
    with mark-total-syn Γ e wfe
  ... | ě , τ , d
      with match+ (τ ⊔ T□ + T□)
  ...    | no ¬m
         with mark-total-syn Γ e₁ wf₁ | mark-total-syn Γ e₂ wf₂
  ...       | ě₁ , _ , d₁             | ě₂ , _ , d₂
              = (case (ě ⦅▸+⦆) of ě₁ · ě₂) , T□
                , mark↦case⇑ d (¬match₃ ¬m) d₁ d₂
  mark-total-syn Γ (case e of e₁ · e₂) (wfacase wfe wf₁ wf₂)
      | ě , τ , d
         | yes (τ₁ , τ₂ , eq)
          with mark-total-syn (τ₁ ∷ Γ) e₁ wf₁ | mark-total-syn (τ₂ ∷ Γ) e₂ wf₂
  ...        | ě₁ , τ₁' , d₁                  | ě₂ , τ₂' , d₂
             with τ₁' ~? τ₂'
  ...           | yes c = (case ě of ě₁ · ě₂) , (τ₁' ⊔ τ₂')
                          , mark↦case d eq d₁ d₂ c
  ...           | no ¬c = (case ě of ě₁ · ě₂) , T□
                          , mark↦case≁ d eq d₁ d₂ ¬c

  -- analysis
  mark-total-ana : ∀ {n} (Γ : Assms) (e : Exp)  (τ : Typ)
                   → n ⊢wf-ann e →
                   ∃[ ě ] n ； Γ ⊢ e ↬ ě ⇓ τ
  mark-total-ana Γ (λ⇒ e) τ (wfaλ⇒ wfe)
    with match⇒ (τ ⊔ T□ ⇒ T□)
  ...  | yes (τ₁ , τ₂ , eq)
       with mark-total-ana (τ₁ ∷ Γ) e τ₂ wfe
  ...     | ě , d = λ⇒ ě , mark↤λ eq d
  mark-total-ana Γ (λ⇒ e) τ (wfaλ⇒ wfe)
       | no ¬m
       with mark-total-ana Γ e T□ wfe
  ...     | ě , d = (λ⇒ ě) ⦅~⇒⦆ , mark↤λ⇑ (¬match₂ ¬m) d

  -- Subsumption
  mark-total-ana Γ e τ wfa
    with mark-total-syn Γ e wfa
  ...  | ě , τ' , d'
       with τ ~? τ'
  ...     | yes c  = ě , mark↤sub d' c
  ...     | no  ¬c = (ě ⦅≁ τ ⦆) , mark↤sub⇑ d' ¬c

-- Unicity: marking is deterministic. TODO
postulate
  mark-unique-syn : ∀ {n Γ e ě₁ ě₂ τ₁ τ₂} →
    n ； Γ ⊢ e ↬ ě₁ ⇑ τ₁ →
    n ； Γ ⊢ e ↬ ě₂ ⇑ τ₂ →
    ě₁ ≡ ě₂ ∧ τ₁ ≡ τ₂

  mark-unique-ana : ∀ {n Γ e ě₁ ě₂ τ} →
    n ； Γ ⊢ e ↬ ě₁ ⇓ τ →
    n ； Γ ⊢ e ↬ ě₂ ⇓ τ →
    ě₁ ≡ ě₂
