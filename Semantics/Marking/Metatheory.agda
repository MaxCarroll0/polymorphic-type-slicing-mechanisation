module Semantics.Marking.Metatheory where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (∃; Σ; _,_)
open import Data.Product using () renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Core
open import Core.MExp as M
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
  mark-wf-syn mark↦*                          = refl
  mark-wf-syn mark↦□                          = refl
  mark-wf-syn (mark↦Var _)                    = refl
  mark-wf-syn (mark↦Var⇑ _)                   = refl
  mark-wf-syn (mark↦λ: _ d)                   = cong (Exp.λ: _ ⇒_) (mark-wf-syn d)
  mark-wf-syn (mark↦Λ d)                      = cong Exp.Λ (mark-wf-syn d)
  mark-wf-syn (mark↦∘ d₁ _ d₂)                = cong₂ Exp._∘_ (mark-wf-syn d₁) (mark-wf-ana d₂)
  mark-wf-syn (mark↦∘⇑ d₁ _ d₂)               = cong₂ Exp._∘_ (mark-wf-syn d₁) (mark-wf-ana d₂)
  mark-wf-syn (mark↦<> d _ _)                 = cong (Exp._< _ >) (mark-wf-syn d)
  mark-wf-syn (mark↦<>⇑ d _ _)                = cong (Exp._< _ >) (mark-wf-syn d)
  mark-wf-syn (mark↦& d₁ d₂)                  = cong₂ Exp._&_ (mark-wf-syn d₁) (mark-wf-syn d₂)
  mark-wf-syn (mark↦def d₁ d₂)                = cong₂ (Exp.def_⊢_) (mark-wf-syn d₁) (mark-wf-syn d₂)
  mark-wf-syn (mark↦π₁ d _)                   = cong Exp.π₁ (mark-wf-syn d)
  mark-wf-syn (mark↦π₁⇑ d _)                  = cong Exp.π₁ (mark-wf-syn d)
  mark-wf-syn (mark↦π₂ d _)                   = cong Exp.π₂ (mark-wf-syn d)
  mark-wf-syn (mark↦π₂⇑ d _)                  = cong Exp.π₂ (mark-wf-syn d)
  mark-wf-syn (mark↦case d _ d₁ d₂ _)
    rewrite mark-wf-syn d | mark-wf-syn d₁ | mark-wf-syn d₂ = refl
  mark-wf-syn (mark↦case⇑ d _ d₁ d₂)
    rewrite mark-wf-syn d | mark-wf-syn d₁ | mark-wf-syn d₂ = refl
  mark-wf-syn (mark↦case≁ d _ d₁ d₂ _)
    rewrite mark-wf-syn d | mark-wf-syn d₁ | mark-wf-syn d₂ = refl
  mark-wf-syn (mark↦λ⇒ d)                     = cong Exp.λ⇒_ (mark-wf-ana d)
  mark-wf-syn (mark↦ι₁ d)                     = cong Exp.ι₁ (mark-wf-ana d)
  mark-wf-syn (mark↦ι₂ d)                     = cong Exp.ι₂ (mark-wf-ana d)

  mark-wf-ana : ∀ {n Γ e ě τ} →
    n ； Γ ⊢ e ↬ ě ⇓ τ → erase ě ≡ e
  mark-wf-ana (mark↤sub d _)                  = mark-wf-syn d
  mark-wf-ana (mark↤sub⇑ d _)                 = mark-wf-syn d
  mark-wf-ana (mark↤λ _ d)                    = cong Exp.λ⇒_ (mark-wf-ana d)
  mark-wf-ana (mark↤λ⇑ _ d)                   = cong Exp.λ⇒_ (mark-wf-ana d)
  mark-wf-ana (mark↤λ: _ _ _ d)               = cong (Exp.λ: _ ⇒_) (mark-wf-ana d)
  mark-wf-ana (mark↤ι₁ _ d)                   = cong Exp.ι₁ (mark-wf-ana d)
  mark-wf-ana (mark↤ι₂ _ d)                   = cong Exp.ι₂ (mark-wf-ana d)
  mark-wf-ana (mark↤& _ d₁ d₂)                = cong₂ Exp._&_ (mark-wf-ana d₁) (mark-wf-ana d₂)
  mark-wf-ana (mark↤def d₁ d₂)                = cong₂ (Exp.def_⊢_) (mark-wf-syn d₁) (mark-wf-ana d₂)
  mark-wf-ana (mark↤case d _ d₁ d₂)
    rewrite mark-wf-syn d | mark-wf-ana d₁ | mark-wf-ana d₂ = refl
  mark-wf-ana (mark↤case⇑ d _ d₁ d₂)
    rewrite mark-wf-syn d | mark-wf-ana d₁ | mark-wf-ana d₂ = refl

-- All type annotations in an expression are well-formed under n type variables
data _⊢wf-ann_ : ℕ → Exp → Set where
  wfa□    : ∀ {n}                                                 → n ⊢wf-ann Exp.□
  wfa*    : ∀ {n}                                                 → n ⊢wf-ann Exp.*
  wfaVar  : ∀ {n k}                                               → n ⊢wf-ann Exp.⟨ k ⟩
  wfaλ:   : ∀ {n τ e}    → n ⊢wf τ  → n ⊢wf-ann e               → n ⊢wf-ann (Exp.λ: τ ⇒ e)
  wfaλ⇒   : ∀ {n e}      → n ⊢wf-ann e                           → n ⊢wf-ann (Exp.λ⇒ e)
  wfa∘    : ∀ {n e₁ e₂}  → n ⊢wf-ann e₁  → n ⊢wf-ann e₂         → n ⊢wf-ann (e₁ Exp.∘ e₂)
  wfa<>   : ∀ {n e σ}    → n ⊢wf-ann e  → n ⊢wf σ               → n ⊢wf-ann (e Exp.< σ >)
  wfa&    : ∀ {n e₁ e₂}  → n ⊢wf-ann e₁  → n ⊢wf-ann e₂         → n ⊢wf-ann (e₁ Exp.& e₂)
  wfaι₁   : ∀ {n e}      → n ⊢wf-ann e                           → n ⊢wf-ann (Exp.ι₁ e)
  wfaι₂   : ∀ {n e}      → n ⊢wf-ann e                           → n ⊢wf-ann (Exp.ι₂ e)
  wfacase : ∀ {n e e₁ e₂} → n ⊢wf-ann e → n ⊢wf-ann e₁ → n ⊢wf-ann e₂
                                                                   → n ⊢wf-ann (Exp.case e of e₁ · e₂)
  wfaπ₁   : ∀ {n e}      → n ⊢wf-ann e                           → n ⊢wf-ann (Exp.π₁ e)
  wfaπ₂   : ∀ {n e}      → n ⊢wf-ann e                           → n ⊢wf-ann (Exp.π₂ e)
  wfaΛ    : ∀ {n e}      → suc n ⊢wf-ann e                       → n ⊢wf-ann (Exp.Λ e)
  wfadef  : ∀ {n e₁ e₂}  → n ⊢wf-ann e₁  → n ⊢wf-ann e₂         → n ⊢wf-ann (Exp.def e₁ ⊢ e₂)

-- Decidable type shape matching (à la hazelnut error-localization)
private
  open T using (⟨_⟩)

  match⇒ : (τ : Typ) → Dec (∃ λ τ₁ → ∃ λ τ₂ → τ ≡ τ₁ ⇒ τ₂)
  match⇒ (_ ⇒ _)     = yes (_ , _ , refl)
  match⇒ ⟨ _ ⟩        = no λ where (_ , _ , ())
  match⇒ T*          = no λ where (_ , _ , ())
  match⇒ T□          = no λ where (_ , _ , ())
  match⇒ (T._+_ _ _) = no λ where (_ , _ , ())
  match⇒ (T._×_ _ _) = no λ where (_ , _ , ())
  match⇒ (∀· _)      = no λ where (_ , _ , ())

  match+ : (τ : Typ) → Dec (∃ λ τ₁ → ∃ λ τ₂ → τ ≡ τ₁ + τ₂)
  match+ (T._+_ _ _) = yes (_ , _ , refl)
  match+ ⟨ _ ⟩        = no λ where (_ , _ , ())
  match+ T*          = no λ where (_ , _ , ())
  match+ T□          = no λ where (_ , _ , ())
  match+ (_ ⇒ _)     = no λ where (_ , _ , ())
  match+ (T._×_ _ _) = no λ where (_ , _ , ())
  match+ (∀· _)      = no λ where (_ , _ , ())

  match× : (τ : Typ) → Dec (∃ λ τ₁ → ∃ λ τ₂ → τ ≡ τ₁ T.× τ₂)
  match× (T._×_ _ _) = yes (_ , _ , refl)
  match× ⟨ _ ⟩        = no λ where (_ , _ , ())
  match× T*          = no λ where (_ , _ , ())
  match× T□          = no λ where (_ , _ , ())
  match× (_ ⇒ _)     = no λ where (_ , _ , ())
  match× (T._+_ _ _) = no λ where (_ , _ , ())
  match× (∀· _)      = no λ where (_ , _ , ())

  match∀ : (τ : Typ) → Dec (∃ λ τ' → τ ≡ ∀· τ')
  match∀ (∀· _)      = yes (_ , refl)
  match∀ ⟨ _ ⟩        = no λ where (_ , ())
  match∀ T*          = no λ where (_ , ())
  match∀ T□          = no λ where (_ , ())
  match∀ (_ ⇒ _)     = no λ where (_ , ())
  match∀ (T._+_ _ _) = no λ where (_ , ())
  match∀ (T._×_ _ _) = no λ where (_ , ())

  ¬match₂ : ∀ {ρ : Typ} → ¬ (∃ λ τ₁ → ∃ λ τ₂ → ρ ≡ τ₁ ⇒ τ₂) → ∀ {τ₁ τ₂} → ρ ≢ τ₁ ⇒ τ₂
  ¬match₂ ¬m eq = ¬m (_ , _ , eq)

  ¬match₃ : ∀ {ρ : Typ} → ¬ (∃ λ τ₁ → ∃ λ τ₂ → ρ ≡ τ₁ + τ₂) → ∀ {τ₁ τ₂} → ρ ≢ τ₁ + τ₂
  ¬match₃ ¬m eq = ¬m (_ , _ , eq)

  ¬match₄ : ∀ {ρ : Typ} → ¬ (∃ λ τ₁ → ∃ λ τ₂ → ρ ≡ τ₁ T.× τ₂) → ∀ {τ₁ τ₂} → ρ ≢ τ₁ T.× τ₂
  ¬match₄ ¬m eq = ¬m (_ , _ , eq)

  ¬match₅ : ∀ {ρ : Typ} → ¬ (∃ λ τ' → ρ ≡ ∀· τ') → ∀ {τ'} → ρ ≢ ∀· τ'
  ¬match₅ ¬m eq = ¬m (_ , eq)

-- Totality: every well-annotated expression can be marked.
mutual
  mark-total-syn : ∀ {n} (Γ : Assms) (e : Exp) → n ⊢wf-ann e →
    ∃ λ ě → ∃ λ τ → n ； Γ ⊢ e ↬ ě ⇑ τ

  mark-total-syn Γ Exp.* wfa* = M.* , T* , mark↦*
  mark-total-syn Γ Exp.□ wfa□ = M.□ , T□ , mark↦□

  mark-total-syn Γ Exp.⟨ k ⟩ wfaVar with Γ at k in eq
  ... | just τ  = M.⟨ k ⟩ , τ , mark↦Var eq
  ... | nothing = M.⟨ k ⟩⇑ , T□ , mark↦Var⇑ eq

  mark-total-syn Γ (Exp.λ: τ ⇒ e) (wfaλ: wfτ wfe)
    with mark-total-syn (τ ∷ Γ) e wfe
  ... | ě , τ₂ , d = (M.λ: τ ⇒ ě) , (τ ⇒ τ₂) , mark↦λ: wfτ d

  -- Analysis-only forms in synthesis position: mark as errors
  mark-total-syn Γ (Exp.λ⇒ e) (wfaλ⇒ wfe)
    with mark-total-ana Γ e T□ wfe
  ... | ě , d = ((M.λ⇒ ě) ⦅~⇒⦆) , T□ , mark↦λ⇒ d

  mark-total-syn Γ (Exp.ι₁ e) (wfaι₁ wfe)
    with mark-total-ana Γ e T□ wfe
  ... | ě , d = ((M.ι₁ ě) ⦅~+⦆) , T□ , mark↦ι₁ d

  mark-total-syn Γ (Exp.ι₂ e) (wfaι₂ wfe)
    with mark-total-ana Γ e T□ wfe
  ... | ě , d = ((M.ι₂ ě) ⦅~+⦆) , T□ , mark↦ι₂ d

  mark-total-syn Γ (Exp.Λ e) (wfaΛ wfe)
    with mark-total-syn (shiftΓ _ Γ) e wfe
  ... | ě , τ , d = M.Λ ě , ∀· τ , mark↦Λ d

  mark-total-syn Γ (e₁ Exp.∘ e₂) (wfa∘ wf₁ wf₂)
    with mark-total-syn Γ e₁ wf₁
  ... | ě₁ , τ , d₁ with match⇒ (τ ⊔ T□ ⇒ T□)
  ...   | yes (τ₁ , τ₂ , eq) with mark-total-ana Γ e₂ τ₁ wf₂
  ...     | ě₂ , d₂ = (ě₁ M.∘ ě₂) , τ₂ , mark↦∘ d₁ eq d₂
  mark-total-syn Γ (e₁ Exp.∘ e₂) (wfa∘ wf₁ wf₂)
    | ě₁ , τ , d₁ | no ¬m with mark-total-ana Γ e₂ T□ wf₂
  ...     | ě₂ , d₂ = ((ě₁ ⦅▸⇒⦆) M.∘ ě₂) , T□ , mark↦∘⇑ d₁ (¬match₂ ¬m) d₂

  mark-total-syn Γ (e Exp.< σ >) (wfa<> wfe wfσ)
    with mark-total-syn Γ e wfe
  ... | ě , τ , d with match∀ (τ ⊔ ∀· T□)
  ...   | yes (τ' , eq) = (ě M.< σ >) , _ , mark↦<> d eq wfσ
  ...   | no ¬m         = ((ě ⦅▸∀⦆) M.< σ >) , T□ , mark↦<>⇑ d (¬match₅ ¬m) wfσ

  mark-total-syn Γ (e₁ Exp.& e₂) (wfa& wf₁ wf₂)
    with mark-total-syn Γ e₁ wf₁ | mark-total-syn Γ e₂ wf₂
  ... | ě₁ , τ₁ , d₁ | ě₂ , τ₂ , d₂ = (ě₁ M.& ě₂) , (τ₁ × τ₂) , mark↦& d₁ d₂

  mark-total-syn Γ (Exp.π₁ e) (wfaπ₁ wfe)
    with mark-total-syn Γ e wfe
  ... | ě , τ , d with match× (τ ⊔ T□ T.× T□)
  ...   | yes (τ₁ , τ₂ , eq) = M.π₁ ě , τ₁ , mark↦π₁ d eq
  ...   | no ¬m              = M.π₁ (ě ⦅▸×⦆) , T□ , mark↦π₁⇑ d (¬match₄ ¬m)

  mark-total-syn Γ (Exp.π₂ e) (wfaπ₂ wfe)
    with mark-total-syn Γ e wfe
  ... | ě , τ , d with match× (τ ⊔ T□ T.× T□)
  ...   | yes (τ₁ , τ₂ , eq) = M.π₂ ě , τ₂ , mark↦π₂ d eq
  ...   | no ¬m              = M.π₂ (ě ⦅▸×⦆) , T□ , mark↦π₂⇑ d (¬match₄ ¬m)

  mark-total-syn Γ (Exp.def e₁ ⊢ e₂) (wfadef wf₁ wf₂)
    with mark-total-syn Γ e₁ wf₁
  ... | ě₁ , τ₁ , d₁ with mark-total-syn (τ₁ ∷ Γ) e₂ wf₂
  ...   | ě₂ , τ₂ , d₂ = (M.def ě₁ ⊢ ě₂) , τ₂ , mark↦def d₁ d₂

  mark-total-syn Γ (Exp.case e of e₁ · e₂) (wfacase wfe wf₁ wf₂)
    with mark-total-syn Γ e wfe
  ... | ě , τ , d with match+ (τ ⊔ T□ + T□)
  ...   | no ¬m with mark-total-syn Γ e₁ wf₁ | mark-total-syn Γ e₂ wf₂
  ...     | ě₁ , _ , d₁ | ě₂ , _ , d₂ =
    (M.case (ě ⦅▸+⦆) of ě₁ · ě₂) , T□ , mark↦case⇑ d (¬match₃ ¬m) d₁ d₂
  mark-total-syn Γ (Exp.case e of e₁ · e₂) (wfacase wfe wf₁ wf₂)
    | ě , τ , d | yes (τ₁ , τ₂ , eq)
    with mark-total-syn (τ₁ ∷ Γ) e₁ wf₁ | mark-total-syn (τ₂ ∷ Γ) e₂ wf₂
  ...   | ě₁ , τ₁' , d₁ | ě₂ , τ₂' , d₂ with τ₁' ~? τ₂'
  ...     | yes c = (M.case ě of ě₁ · ě₂) , (τ₁' ⊔ τ₂') , mark↦case d eq d₁ d₂ c
  ...     | no ¬c = (M.case ě of ě₁ · ě₂) , T□ , mark↦case≁ d eq d₁ d₂ ¬c

  -- Analysis totality: subsumption or form-specific rules
  mark-total-ana : ∀ {n} (Γ : Assms) (e : Exp) (τ : Typ) → n ⊢wf-ann e →
    ∃ λ ě → n ； Γ ⊢ e ↬ ě ⇓ τ

  -- Unannotated lambda
  mark-total-ana Γ (Exp.λ⇒ e) τ (wfaλ⇒ wfe) with match⇒ (τ ⊔ T□ ⇒ T□)
  ... | yes (τ₁ , τ₂ , eq) with mark-total-ana (τ₁ ∷ Γ) e τ₂ wfe
  ...   | ě , d = M.λ⇒ ě , mark↤λ eq d
  mark-total-ana Γ (Exp.λ⇒ e) τ (wfaλ⇒ wfe) | no ¬m
    with mark-total-ana Γ e T□ wfe
  ...   | ě , d = (M.λ⇒ ě) ⦅~⇒⦆ , mark↤λ⇑ (¬match₂ ¬m) d

  -- Default: fall through to subsumption
  mark-total-ana Γ e τ wfa with mark-total-syn Γ e wfa
  ... | ě , τ' , d' with τ ~? τ'
  ...   | yes c  = ě , mark↤sub d' c
  ...   | no  ¬c = (ě ⦅≁ τ ⦆) , mark↤sub⇑ d' ¬c

-- Unicity: marking is deterministic. Note: I'm not sure this will hold with my formalisation
postulate
  mark-unique-syn : ∀ {n Γ e ě₁ ě₂ τ₁ τ₂} →
    n ； Γ ⊢ e ↬ ě₁ ⇑ τ₁ →
    n ； Γ ⊢ e ↬ ě₂ ⇑ τ₂ →
    ě₁ ≡ ě₂ ∧ τ₁ ≡ τ₂

  mark-unique-ana : ∀ {n Γ e ě₁ ě₂ τ} →
    n ； Γ ⊢ e ↬ ě₁ ⇓ τ →
    n ； Γ ⊢ e ↬ ě₂ ⇓ τ →
    ě₁ ≡ ě₂
