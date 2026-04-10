open import Data.Nat hiding (_+_; _⊔_)
open import Data.List using (_∷_)
open import Data.Product using (Σ; _,_; ∃) renaming (_×_ to _×'_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core
open import Semantics.Statics.Typing

module Semantics.Statics.CtxTyping where

-- The mode a context expects its focus to be in
data CtxMode : Set where
  ⇒mode  : CtxMode
  ⇐mode  : Typ → CtxMode

-- The position of a context in the derivation
data Position : Set where
  synPos  : Position
  anaPos  : Typ → Position

FocusTyping : ℕ → Assms → Exp → CtxMode → Set
FocusTyping n Γ' e ⇒mode       = ∃ λ τ' → n ； Γ' ⊢ e ↦ τ'
FocusTyping n Γ' e (⇐mode τ')  = n ； Γ' ⊢ e ↤ τ'

-- Context classification judgement
-- n ； Γ ⊢ C at p ▷ Γ' [ m ] means:
--   Under type depth n and outer assumptions Γ, context C in position p
--   has its focus under assumptions Γ' in mode m
data _；_⊢_at_▷_[_] : ℕ → Assms → Ctx → Position → Assms → CtxMode → Set where
  s○      : ∀ {n Γ}                                                                                →
            n ； Γ ⊢ ○ at synPos ▷ Γ [ ⇒mode ]

  a○      : ∀ {n Γ τ}                                                                              →
            n ； Γ ⊢ ○ at anaPos τ ▷ Γ [ ⇐mode τ ]

  -- Subsumption: any synthesis classification works for analysis too
  aSub    : ∀ {n Γ Γ' C τ m}     → n ； Γ ⊢ C at synPos ▷ Γ' [ m ]                                 →
            n ； Γ ⊢ C at anaPos τ ▷ Γ' [ m ]

  sλ:     : ∀ {n Γ Γ' τ C m}     → n ⊢wf τ
                                  → n ； (τ ∷ Γ) ⊢ C at synPos ▷ Γ' [ m ]                          →
            n ； Γ ⊢ λ: τ ⇒ C at synPos ▷ Γ' [ m ]

  aλ:     : ∀ {n Γ Γ' C τ τ₁ τ₂ m}
            → τ ~ τ₁ ⇒ □       → τ ⊔ τ₁ ⇒ □ ≡ τ₁ ⇒ τ₂
            → n ⊢wf τ₁
            → n ； (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ Γ' [ m ]                                            →
            n ； Γ ⊢ λ: τ₁ ⇒ C at anaPos τ ▷ Γ' [ m ]

  aλ⇒     : ∀ {n Γ Γ' C τ τ₁ τ₂ m}
            → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂
            → n ； (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ Γ' [ m ]                                            →
            n ； Γ ⊢ λ⇒ C at anaPos τ ▷ Γ' [ m ]

  s∘₁     : ∀ {n Γ Γ' C e m}     → n ； Γ ⊢ C at synPos ▷ Γ' [ m ]                                →
            n ； Γ ⊢ C ∘₁ e at synPos ▷ Γ' [ m ]

  s∘₂     : ∀ {n Γ Γ' e C τ τ₁ τ₂ m}
            → n ； Γ ⊢ e ↦ τ   → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂
            → n ； Γ ⊢ C at anaPos τ₁ ▷ Γ' [ m ]                                                   →
            n ； Γ ⊢ e ∘₂ C at synPos ▷ Γ' [ m ]

  s<>₁    : ∀ {n Γ Γ' C τ m}     → n ； Γ ⊢ C at synPos ▷ Γ' [ m ]                                →
            n ； Γ ⊢ C < τ >₁ at synPos ▷ Γ' [ m ]

  s&₁     : ∀ {n Γ Γ' C e m}     → n ； Γ ⊢ C at synPos ▷ Γ' [ m ]                                →
            n ； Γ ⊢ C &₁ e at synPos ▷ Γ' [ m ]

  s&₂     : ∀ {n Γ Γ' C e m}     → n ； Γ ⊢ C at synPos ▷ Γ' [ m ]                                →
            n ； Γ ⊢ e &₂ C at synPos ▷ Γ' [ m ]

  a&₁     : ∀ {n Γ Γ' C e τ τ₁ τ₂ m}
            → τ ⊔ □ × □ ≡ τ₁ × τ₂
            → n ； Γ ⊢ C at anaPos τ₁ ▷ Γ' [ m ]                                                   →
            n ； Γ ⊢ C &₁ e at anaPos τ ▷ Γ' [ m ]

  a&₂     : ∀ {n Γ Γ' C e τ τ₁ τ₂ m}
            → τ ⊔ □ × □ ≡ τ₁ × τ₂
            → n ； Γ ⊢ C at anaPos τ₂ ▷ Γ' [ m ]                                                   →
            n ； Γ ⊢ e &₂ C at anaPos τ ▷ Γ' [ m ]

  aι₁     : ∀ {n Γ Γ' C τ τ₁ τ₂ m}
            → τ ⊔ □ + □ ≡ τ₁ + τ₂
            → n ； Γ ⊢ C at anaPos τ₁ ▷ Γ' [ m ]                                                   →
            n ； Γ ⊢ ι₁ C at anaPos τ ▷ Γ' [ m ]

  aι₂     : ∀ {n Γ Γ' C τ τ₁ τ₂ m}
            → τ ⊔ □ + □ ≡ τ₁ + τ₂
            → n ； Γ ⊢ C at anaPos τ₂ ▷ Γ' [ m ]                                                   →
            n ； Γ ⊢ ι₂ C at anaPos τ ▷ Γ' [ m ]

  scase₁  : ∀ {n Γ Γ' e C e' τ τ₁ τ₂ m}
            → n ； Γ ⊢ e ↦ τ   → τ ⊔ □ + □ ≡ τ₁ + τ₂
            → n ； (τ₁ ∷ Γ) ⊢ C at synPos ▷ Γ' [ m ]                                              →
            n ； Γ ⊢ case e of C ·₁ e' at synPos ▷ Γ' [ m ]

  scase₂  : ∀ {n Γ Γ' e e' C τ τ₁ τ₂ m}
            → n ； Γ ⊢ e ↦ τ   → τ ⊔ □ + □ ≡ τ₁ + τ₂
            → n ； (τ₂ ∷ Γ) ⊢ C at synPos ▷ Γ' [ m ]                                              →
            n ； Γ ⊢ case e of₂ e' · C at synPos ▷ Γ' [ m ]

  acase₁  : ∀ {n Γ Γ' e C e' τ τ₀ τ₁ τ₂ m}
            → n ； Γ ⊢ e ↦ τ₀  → τ₀ ⊔ □ + □ ≡ τ₁ + τ₂
            → n ； (τ₁ ∷ Γ) ⊢ C at anaPos τ ▷ Γ' [ m ]                                            →
            n ； Γ ⊢ case e of C ·₁ e' at anaPos τ ▷ Γ' [ m ]

  acase₂  : ∀ {n Γ Γ' e e' C τ τ₀ τ₁ τ₂ m}
            → n ； Γ ⊢ e ↦ τ₀  → τ₀ ⊔ □ + □ ≡ τ₁ + τ₂
            → n ； (τ₂ ∷ Γ) ⊢ C at anaPos τ ▷ Γ' [ m ]                                            →
            n ； Γ ⊢ case e of₂ e' · C at anaPos τ ▷ Γ' [ m ]

  sπ₁     : ∀ {n Γ Γ' C m}       → n ； Γ ⊢ C at synPos ▷ Γ' [ m ]                                →
            n ； Γ ⊢ π₁ C at synPos ▷ Γ' [ m ]

  sπ₂     : ∀ {n Γ Γ' C m}       → n ； Γ ⊢ C at synPos ▷ Γ' [ m ]                                →
            n ； Γ ⊢ π₂ C at synPos ▷ Γ' [ m ]

  sΛ      : ∀ {n Γ Γ' C m}       → suc n ； shiftΓ (suc zero) Γ ⊢ C at synPos ▷ Γ' [ m ]          →
            n ； Γ ⊢ Λ C at synPos ▷ Γ' [ m ]

  sdef₁   : ∀ {n Γ Γ' C e m}     → n ； Γ ⊢ C at synPos ▷ Γ' [ m ]                                →
            n ； Γ ⊢ def C ⊢₁ e at synPos ▷ Γ' [ m ]

  sdef₂   : ∀ {n Γ Γ' e C τ' m}
            → n ； Γ ⊢ e ↦ τ'  → n ； (τ' ∷ Γ) ⊢ C at synPos ▷ Γ' [ m ]                           →
            n ； Γ ⊢ def e ⊢₂ C at synPos ▷ Γ' [ m ]

  adef₁   : ∀ {n Γ Γ' C e τ m}   → n ； Γ ⊢ C at synPos ▷ Γ' [ m ]                                →
            n ； Γ ⊢ def C ⊢₁ e at anaPos τ ▷ Γ' [ m ]

  adef₂   : ∀ {n Γ Γ' e C τ τ' m}
            → n ； Γ ⊢ e ↦ τ'  → n ； (τ' ∷ Γ) ⊢ C at anaPos τ ▷ Γ' [ m ]                         →
            n ； Γ ⊢ def e ⊢₂ C at anaPos τ ▷ Γ' [ m ]

-- Result type for plug decomposition
PlugResult : ℕ → Assms → Ctx → Exp → Position → Set
PlugResult n Γ C e p = Σ ℕ λ n' → Σ Assms λ Γ' → Σ CtxMode λ m → n ； Γ ⊢ C at p ▷ Γ' [ m ] ×' FocusTyping n' Γ' e m

-- Plug decomposition theorem
mutual
  plug-syn : ∀ {n Γ e τ} (C : Ctx) → n ； Γ ⊢ plug C e ↦ τ → PlugResult n Γ C e synPos

  plug-syn ○ d =
    _ , _ , ⇒mode , s○ , _ , d
  plug-syn (λ: τ ⇒ C) (↦λ: wf d) with plug-syn C d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sλ: wf cls , ft
  plug-syn (λ⇒ C) ()
  plug-syn (C ∘₁ e₂) (↦∘ d₁ _ _) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , s∘₁ cls , ft
  plug-syn (e₁ ∘₂ C) (↦∘ d₁ eq d₂) with plug-ana C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , s∘₂ d₁ eq cls , ft
  plug-syn (C < τ >₁) (↦<> d₁ _ _) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , s<>₁ cls , ft
  plug-syn (C &₁ e₂) (↦& d₁ _) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , s&₁ cls , ft
  plug-syn (e₁ &₂ C) (↦& _ d₂) with plug-syn C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , s&₂ cls , ft
  plug-syn (ι₁ C) ()
  plug-syn (ι₂ C) ()
  plug-syn (case e₀ of C ·₁ e₂) (↦case d₀ eq d₁ _ _) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , scase₁ d₀ eq cls , ft
  plug-syn (case e₀ of₂ e₁ · C) (↦case d₀ eq _ d₂ _) with plug-syn C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , scase₂ d₀ eq cls , ft
  plug-syn (π₁ C) (↦π₁ d₁ _) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sπ₁ cls , ft
  plug-syn (π₂ C) (↦π₂ d₁ _) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sπ₂ cls , ft
  plug-syn (Λ C) (↦Λ d₁) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sΛ cls , ft
  plug-syn (def C ⊢₁ e₂) (↦def d₁ _) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sdef₁ cls , ft
  plug-syn (def e₁ ⊢₂ C) (↦def d₁ d₂) with plug-syn C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sdef₂ d₁ cls , ft

  plug-ana : ∀ {n Γ e τ} (C : Ctx) → n ； Γ ⊢ plug C e ↤ τ → PlugResult n Γ C e (anaPos τ)

  plug-ana ○ (↤Sub d _) =
    _ , _ , ⇒mode , aSub s○ , _ , d
  plug-ana ○ d =
    _ , _ , ⇐mode _ , a○ , d
  plug-ana (λ: τ ⇒ C) (↤Sub d _) with plug-syn (λ: τ ⇒ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls , ft
  plug-ana (λ: τ₁ ⇒ C) (↤λ: c eq wf d) with plug-ana C d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aλ: c eq wf cls , ft
  plug-ana (λ⇒ C) (↤Sub () _)
  plug-ana (λ⇒ C) (↤λ eq d) with plug-ana C d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aλ⇒ eq cls , ft
  plug-ana (C ∘₁ e₂) (↤Sub d _) with plug-syn (C ∘₁ e₂) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls , ft
  plug-ana (e₁ ∘₂ C) (↤Sub d _) with plug-syn (e₁ ∘₂ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls , ft
  plug-ana (C < τ >₁) (↤Sub d _) with plug-syn (C < τ >₁) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls , ft
  plug-ana (C &₁ e₂) (↤Sub d _) with plug-syn (C &₁ e₂) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls , ft
  plug-ana (C &₁ e₂) (↤& eq d₁ _) with plug-ana C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , a&₁ eq cls , ft
  plug-ana (e₁ &₂ C) (↤Sub d _) with plug-syn (e₁ &₂ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls , ft
  plug-ana (e₁ &₂ C) (↤& eq _ d₂) with plug-ana C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , a&₂ eq cls , ft
  plug-ana (ι₁ C) (↤Sub () _)
  plug-ana (ι₁ C) (↤ι₁ eq d) with plug-ana C d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aι₁ eq cls , ft
  plug-ana (ι₂ C) (↤Sub () _)
  plug-ana (ι₂ C) (↤ι₂ eq d) with plug-ana C d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aι₂ eq cls , ft
  plug-ana (case e₀ of C ·₁ e₂) (↤Sub d _) with plug-syn (case e₀ of C ·₁ e₂) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls , ft
  plug-ana (case e₀ of C ·₁ e₂) (↤case d₀ eq d₁ _) with plug-ana C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , acase₁ d₀ eq cls , ft
  plug-ana (case e₀ of₂ e₁ · C) (↤Sub d _) with plug-syn (case e₀ of₂ e₁ · C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls , ft
  plug-ana (case e₀ of₂ e₁ · C) (↤case d₀ eq _ d₂) with plug-ana C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , acase₂ d₀ eq cls , ft
  plug-ana (π₁ C) (↤Sub d _) with plug-syn (π₁ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls , ft
  plug-ana (π₂ C) (↤Sub d _) with plug-syn (π₂ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls , ft
  plug-ana (Λ C) (↤Sub d _) with plug-syn (Λ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls , ft
  plug-ana (def C ⊢₁ e₂) (↤Sub d _) with plug-syn (def C ⊢₁ e₂) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls , ft
  plug-ana (def C ⊢₁ e₂) (↤def d₁ _) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , adef₁ cls , ft
  plug-ana (def e₁ ⊢₂ C) (↤Sub d _) with plug-syn (def e₁ ⊢₂ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls , ft
  plug-ana (def e₁ ⊢₂ C) (↤def d₁ d₂) with plug-ana C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , adef₂ d₁ cls , ft

PositionTyping : ℕ → Assms → Exp → Position → Set
PositionTyping n Γ e synPos     = ∃ λ τ → n ； Γ ⊢ e ↦ τ
PositionTyping n Γ e (anaPos τ) = n ； Γ ⊢ e ↤ τ

-- Generalised plug decomposition: for well-typed plug C e in any mode,
plug-decompose : ∀ {n Γ e} (C : Ctx) (p : Position) →
  PositionTyping n Γ (plug C e) p → PlugResult n Γ C e p
plug-decompose C synPos     (_ , d) = plug-syn C d
plug-decompose C (anaPos _) d       = plug-ana C d
