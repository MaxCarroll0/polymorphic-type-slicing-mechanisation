open import Data.Nat hiding (_+_; _⊔_)
open import Data.List using (_∷_)
open import Data.Product using (Σ; _,_; ∃) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core
open import Semantics.Statics.Typing

-- Context classification Γ₀ ⊢ C at p ▷ Γ [ mode ] and the plug-decomposition / plug-composition
-- theorems that connect classified contexts to expression typing.
-- Dissertation: §4.4 Context Classification, Appendix A
module Semantics.Statics.CtxTyping where

-- The mode a context expects its focus to be in, carrying the focus type
data CtxMode : Set where
  ⇒mode  : Typ → CtxMode    -- focus synthesizes this type
  ⇐mode  : Typ → CtxMode    -- focus is analyzed against this type

-- The position of a context in the derivation, carrying the outer type
data Position : Set where
  synPos  : Typ → Position   -- outer expression synthesizes this type
  anaPos  : Typ → Position   -- outer expression is analyzed against this type

FocusTyping : ℕ → Assms → Exp → CtxMode → Set
FocusTyping n Γ' e (⇒mode τ')  = n , Γ' ⊢ e ⇑ τ'
FocusTyping n Γ' e (⇐mode τ')  = n , Γ' ⊢ e ⇓ τ'

-- Context classification judgement
-- n , Γ ⊢ C at p ▷ n' , Γ' [ m ] is in words:
--   Under type depth n and outer assumptions Γ, context C in position p
--   has its focus at type depth n' under assumptions Γ' in mode m
--
-- For synPos τ: plugging a well-typed focus produces a synthesis derivation at type τ
-- For anaPos τ: plugging a well-typed focus produces an analysis derivation at type τ
data _,_⊢_at_▷_,_[_] : ℕ → Assms → Ctx → Position → ℕ → Assms → CtxMode → Set where

  -- outer type = focus syn type
  s○      : ∀ {n Γ τ}                                                                                →
            n , Γ ⊢ ○ at synPos τ ▷ n , Γ [ ⇒mode τ ]

  -- outer type = focus ana type
  a○      : ∀ {n Γ τ}                                                                                →
            n , Γ ⊢ ○ at anaPos τ ▷ n , Γ [ ⇐mode τ ]

  -- Subsumption: synthesis classification is consistent with analysis type
  aSub    : ∀ {n Γ n' Γ' C τ τ' m}  → n , Γ ⊢ C at synPos τ' ▷ n' , Γ' [ m ]
                                     → τ ~ τ'                                                          →
            n , Γ ⊢ C at anaPos τ ▷ n' , Γ' [ m ]

  sλ:     : ∀ {n Γ n' Γ' τ₁ τ₂ C m} → n ⊢wf τ₁
                                     → n , (τ₁ ∷ Γ) ⊢ C at synPos τ₂ ▷ n' , Γ' [ m ]               →
            n , Γ ⊢ λ: τ₁ ⇒ C at synPos (τ₁ ⇒ τ₂) ▷ n' , Γ' [ m ]

  aλ:     : ∀ {n Γ n' Γ' C τ τ₁ τ₁' τ₂ m}
            → τ ~ τ₁ ⇒ □
            → τ ⊔ τ₁ ⇒ □ ≡ τ₁' ⇒ τ₂
            → n ⊢wf τ₁
            → n , (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ n' , Γ' [ m ]                                        →
            n , Γ ⊢ λ: τ₁ ⇒ C at anaPos τ ▷ n' , Γ' [ m ]

  aλ⇒     : ∀ {n Γ n' Γ' C τ τ₁ τ₂ m}
            → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂
            → n , (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ n' , Γ' [ m ]                                        →
            n , Γ ⊢ λ⇒ C at anaPos τ ▷ n' , Γ' [ m ]

  s∘₁     : ∀ {n Γ n' Γ' C e τ τ₁ τ₂ m}
            → n , Γ ⊢ C at synPos τ ▷ n' , Γ' [ m ]
            → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂
            → n , Γ ⊢ e ⇓ τ₁                                                                         →
            n , Γ ⊢ C ∘₁ e at synPos τ₂ ▷ n' , Γ' [ m ]

  s∘₂     : ∀ {n Γ n' Γ' e C τ τ₁ τ₂ m}
            → n , Γ ⊢ e ⇑ τ   → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂
            → n , Γ ⊢ C at anaPos τ₁ ▷ n' , Γ' [ m ]                                               →
            n , Γ ⊢ e ∘₂ C at synPos τ₂ ▷ n' , Γ' [ m ]

  s<>₁    : ∀ {n Γ n' Γ' C τ τ' σ m}
            → n , Γ ⊢ C at synPos τ ▷ n' , Γ' [ m ]
            → τ ⊔ ∀· □ ≡ ∀· τ'
            → n ⊢wf σ                                                                                 →
            n , Γ ⊢ C < σ >₁ at synPos ([ zero ↦ σ ] τ') ▷ n' , Γ' [ m ]

  s&₁     : ∀ {n Γ n' Γ' C e τ₁ τ₂ m}
            → n , Γ ⊢ C at synPos τ₁ ▷ n' , Γ' [ m ]
            → n , Γ ⊢ e ⇑ τ₂                                                                         →
            n , Γ ⊢ C &₁ e at synPos (τ₁ × τ₂) ▷ n' , Γ' [ m ]

  s&₂     : ∀ {n Γ n' Γ' C e τ₁ τ₂ m}
            → n , Γ ⊢ e ⇑ τ₁
            → n , Γ ⊢ C at synPos τ₂ ▷ n' , Γ' [ m ]                                               →
            n , Γ ⊢ e &₂ C at synPos (τ₁ × τ₂) ▷ n' , Γ' [ m ]

  a&₁     : ∀ {n Γ n' Γ' C e τ τ₁ τ₂ m}
            → τ ⊔ □ × □ ≡ τ₁ × τ₂
            → n , Γ ⊢ C at anaPos τ₁ ▷ n' , Γ' [ m ]
            → n , Γ ⊢ e ⇓ τ₂                                                                         →
            n , Γ ⊢ C &₁ e at anaPos τ ▷ n' , Γ' [ m ]

  a&₂     : ∀ {n Γ n' Γ' C e τ τ₁ τ₂ m}
            → τ ⊔ □ × □ ≡ τ₁ × τ₂
            → n , Γ ⊢ e ⇓ τ₁
            → n , Γ ⊢ C at anaPos τ₂ ▷ n' , Γ' [ m ]                                               →
            n , Γ ⊢ e &₂ C at anaPos τ ▷ n' , Γ' [ m ]

  sι₁     : ∀ {n Γ n' Γ' C τ m}
            → n , Γ ⊢ C at synPos τ ▷ n' , Γ' [ m ]                                                →
            n , Γ ⊢ ι₁ C at synPos (τ + □) ▷ n' , Γ' [ m ]

  sι₂     : ∀ {n Γ n' Γ' C τ m}
            → n , Γ ⊢ C at synPos τ ▷ n' , Γ' [ m ]                                                →
            n , Γ ⊢ ι₂ C at synPos (□ + τ) ▷ n' , Γ' [ m ]

  aι₁     : ∀ {n Γ n' Γ' C τ τ₁ τ₂ m}
            → τ ⊔ □ + □ ≡ τ₁ + τ₂
            → n , Γ ⊢ C at anaPos τ₁ ▷ n' , Γ' [ m ]                                               →
            n , Γ ⊢ ι₁ C at anaPos τ ▷ n' , Γ' [ m ]

  aι₂     : ∀ {n Γ n' Γ' C τ τ₁ τ₂ m}
            → τ ⊔ □ + □ ≡ τ₁ + τ₂
            → n , Γ ⊢ C at anaPos τ₂ ▷ n' , Γ' [ m ]                                               →
            n , Γ ⊢ ι₂ C at anaPos τ ▷ n' , Γ' [ m ]

  scase₁  : ∀ {n Γ n' Γ' e C e' τ τ₁ τ₂ τ₁' τ₂' m}
            → n , Γ ⊢ e ⇑ τ   → τ ⊔ □ + □ ≡ τ₁ + τ₂
            → n , (τ₁ ∷ Γ) ⊢ C at synPos τ₁' ▷ n' , Γ' [ m ]
            → n , (τ₂ ∷ Γ) ⊢ e' ⇑ τ₂'
            → τ₁' ~ τ₂'                                                                               →
            n , Γ ⊢ case e of C ·₁ e' at synPos (τ₁' ⊔ τ₂') ▷ n' , Γ' [ m ]

  scase₂  : ∀ {n Γ n' Γ' e e' C τ τ₁ τ₂ τ₁' τ₂' m}
            → n , Γ ⊢ e ⇑ τ   → τ ⊔ □ + □ ≡ τ₁ + τ₂
            → n , (τ₁ ∷ Γ) ⊢ e' ⇑ τ₁'
            → n , (τ₂ ∷ Γ) ⊢ C at synPos τ₂' ▷ n' , Γ' [ m ]
            → τ₁' ~ τ₂'                                                                               →
            n , Γ ⊢ case e of₂ e' · C at synPos (τ₁' ⊔ τ₂') ▷ n' , Γ' [ m ]

  acase₁  : ∀ {n Γ n' Γ' e C e' τ τ₀ τ₁ τ₂ m}
            → n , Γ ⊢ e ⇑ τ₀  → τ₀ ⊔ □ + □ ≡ τ₁ + τ₂
            → n , (τ₁ ∷ Γ) ⊢ C at anaPos τ ▷ n' , Γ' [ m ]
            → n , (τ₂ ∷ Γ) ⊢ e' ⇓ τ                                                                 →
            n , Γ ⊢ case e of C ·₁ e' at anaPos τ ▷ n' , Γ' [ m ]

  acase₂  : ∀ {n Γ n' Γ' e e' C τ τ₀ τ₁ τ₂ m}
            → n , Γ ⊢ e ⇑ τ₀  → τ₀ ⊔ □ + □ ≡ τ₁ + τ₂
            → n , (τ₁ ∷ Γ) ⊢ e' ⇓ τ
            → n , (τ₂ ∷ Γ) ⊢ C at anaPos τ ▷ n' , Γ' [ m ]                                         →
            n , Γ ⊢ case e of₂ e' · C at anaPos τ ▷ n' , Γ' [ m ]

  sπ₁     : ∀ {n Γ n' Γ' C τ τ₁ τ₂ m}
            → n , Γ ⊢ C at synPos τ ▷ n' , Γ' [ m ]
            → τ ⊔ □ × □ ≡ τ₁ × τ₂                                                                    →
            n , Γ ⊢ π₁ C at synPos τ₁ ▷ n' , Γ' [ m ]

  sπ₂     : ∀ {n Γ n' Γ' C τ τ₁ τ₂ m}
            → n , Γ ⊢ C at synPos τ ▷ n' , Γ' [ m ]
            → τ ⊔ □ × □ ≡ τ₁ × τ₂                                                                    →
            n , Γ ⊢ π₂ C at synPos τ₂ ▷ n' , Γ' [ m ]

  sΛ      : ∀ {n Γ n' Γ' C τ m}
            → suc n , shiftΓ (suc zero) Γ ⊢ C at synPos τ ▷ n' , Γ' [ m ]                           →
            n , Γ ⊢ Λ C at synPos (∀· τ) ▷ n' , Γ' [ m ]

  sdef₁   : ∀ {n Γ n' Γ' C e τ' τ m}
            → n , Γ ⊢ C at synPos τ' ▷ n' , Γ' [ m ]
            → n , (τ' ∷ Γ) ⊢ e ⇑ τ                                                                   →
            n , Γ ⊢ def C ⊢₁ e at synPos τ ▷ n' , Γ' [ m ]

  sdef₂   : ∀ {n Γ n' Γ' e C τ' τ m}
            → n , Γ ⊢ e ⇑ τ'  → n , (τ' ∷ Γ) ⊢ C at synPos τ ▷ n' , Γ' [ m ]                      →
            n , Γ ⊢ def e ⊢₂ C at synPos τ ▷ n' , Γ' [ m ]

  adef₁   : ∀ {n Γ n' Γ' C e τ τ' m}
            → n , Γ ⊢ C at synPos τ' ▷ n' , Γ' [ m ]
            → n , (τ' ∷ Γ) ⊢ e ⇓ τ                                                                   →
            n , Γ ⊢ def C ⊢₁ e at anaPos τ ▷ n' , Γ' [ m ]

  adef₂   : ∀ {n Γ n' Γ' e C τ τ' m}
            → n , Γ ⊢ e ⇑ τ'  → n , (τ' ∷ Γ) ⊢ C at anaPos τ ▷ n' , Γ' [ m ]                      →
            n , Γ ⊢ def e ⊢₂ C at anaPos τ ▷ n' , Γ' [ m ]

PlugResult : ℕ → Assms → Ctx → Exp → Position → Set
PlugResult n Γ C e p = Σ ℕ λ n' → Σ Assms λ Γ' → Σ CtxMode λ m →
  n , Γ ⊢ C at p ▷ n' , Γ' [ m ] ∧ FocusTyping n' Γ' e m

-- Plug decomposition theorem (totality)
mutual
  plug-syn : ∀ {n Γ e τ} (C : Ctx) → n , Γ ⊢ plug C e ⇑ τ → PlugResult n Γ C e (synPos τ)

  plug-syn ○ d =
    _ , _ , ⇒mode _ , s○ , d
  plug-syn (λ: τ ⇒ C) (⇑λ: wf d) with plug-syn C d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sλ: wf cls , ft
  plug-syn (λ⇒ C) ()
  plug-syn (C ∘₁ e₂) (⇑∘ d₁ eq d₂) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , s∘₁ cls eq d₂ , ft
  plug-syn (e₁ ∘₂ C) (⇑∘ d₁ eq d₂) with plug-ana C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , s∘₂ d₁ eq cls , ft
  plug-syn (C < σ >₁) (⇑<> d₁ eq wf) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , s<>₁ cls eq wf , ft
  plug-syn (C &₁ e₂) (⇑& d₁ d₂) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , s&₁ cls d₂ , ft
  plug-syn (e₁ &₂ C) (⇑& d₁ d₂) with plug-syn C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , s&₂ d₁ cls , ft
  plug-syn (ι₁ C) (⇑ι₁ d) with plug-syn C d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sι₁ cls , ft
  plug-syn (ι₂ C) (⇑ι₂ d) with plug-syn C d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sι₂ cls , ft
  plug-syn (case e₀ of C ·₁ e₂) (⇑case d₀ eq d₁ d₂ con) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , scase₁ d₀ eq cls d₂ con , ft
  plug-syn (case e₀ of₂ e₁ · C) (⇑case d₀ eq d₁ d₂ con) with plug-syn C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , scase₂ d₀ eq d₁ cls con , ft
  plug-syn (π₁ C) (⇑π₁ d₁ eq) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sπ₁ cls eq , ft
  plug-syn (π₂ C) (⇑π₂ d₁ eq) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sπ₂ cls eq , ft
  plug-syn (Λ C) (⇑Λ d₁) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sΛ cls , ft
  plug-syn (def C ⊢₁ e₂) (⇑def d₁ d₂) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sdef₁ cls d₂ , ft
  plug-syn (def e₁ ⊢₂ C) (⇑def d₁ d₂) with plug-syn C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , sdef₂ d₁ cls , ft

  plug-ana : ∀ {n Γ e τ} (C : Ctx) → n , Γ ⊢ plug C e ⇓ τ → PlugResult n Γ C e (anaPos τ)

  plug-ana ○ (⇓Sub d con) =
    _ , _ , ⇒mode _ , aSub s○ con , d
  plug-ana ○ d =
    _ , _ , ⇐mode _ , a○ , d
  plug-ana (λ: τ ⇒ C) (⇓Sub d con) with plug-syn (λ: τ ⇒ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (λ: τ₁ ⇒ C) (⇓λ: c eq wf d) with plug-ana C d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aλ: c eq wf cls , ft
  plug-ana (λ⇒ C) (⇓Sub () _)
  plug-ana (λ⇒ C) (⇓λ eq d) with plug-ana C d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aλ⇒ eq cls , ft
  plug-ana (C ∘₁ e₂) (⇓Sub d con) with plug-syn (C ∘₁ e₂) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (e₁ ∘₂ C) (⇓Sub d con) with plug-syn (e₁ ∘₂ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (C < τ >₁) (⇓Sub d con) with plug-syn (C < τ >₁) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (C &₁ e₂) (⇓Sub d con) with plug-syn (C &₁ e₂) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (C &₁ e₂) (⇓& eq d₁ d₂) with plug-ana C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , a&₁ eq cls d₂ , ft
  plug-ana (e₁ &₂ C) (⇓Sub d con) with plug-syn (e₁ &₂ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (e₁ &₂ C) (⇓& eq d₁ d₂) with plug-ana C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , a&₂ eq d₁ cls , ft
  plug-ana (ι₁ C) (⇓Sub d con) with plug-syn (ι₁ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (ι₁ C) (⇓ι₁ eq d) with plug-ana C d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aι₁ eq cls , ft
  plug-ana (ι₂ C) (⇓Sub d con) with plug-syn (ι₂ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (ι₂ C) (⇓ι₂ eq d) with plug-ana C d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aι₂ eq cls , ft
  plug-ana (case e₀ of C ·₁ e₂) (⇓Sub d con) with plug-syn (case e₀ of C ·₁ e₂) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (case e₀ of C ·₁ e₂) (⇓case d₀ eq d₁ d₂) with plug-ana C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , acase₁ d₀ eq cls d₂ , ft
  plug-ana (case e₀ of₂ e₁ · C) (⇓Sub d con) with plug-syn (case e₀ of₂ e₁ · C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (case e₀ of₂ e₁ · C) (⇓case d₀ eq d₁ d₂) with plug-ana C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , acase₂ d₀ eq d₁ cls , ft
  plug-ana (π₁ C) (⇓Sub d con) with plug-syn (π₁ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (π₂ C) (⇓Sub d con) with plug-syn (π₂ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (Λ C) (⇓Sub d con) with plug-syn (Λ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (def C ⊢₁ e₂) (⇓Sub d con) with plug-syn (def C ⊢₁ e₂) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (def C ⊢₁ e₂) (⇓def d₁ d₂) with plug-syn C d₁
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , adef₁ cls d₂ , ft
  plug-ana (def e₁ ⊢₂ C) (⇓Sub d con) with plug-syn (def e₁ ⊢₂ C) d
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , aSub cls con , ft
  plug-ana (def e₁ ⊢₂ C) (⇓def d₁ d₂) with plug-ana C d₂
  ... | n' , Γ' , m , cls , ft = n' , Γ' , m , adef₂ d₁ cls , ft

PositionTyping : ℕ → Assms → Exp → Position → Set
PositionTyping n Γ e (synPos τ) = n , Γ ⊢ e ⇑ τ
PositionTyping n Γ e (anaPos τ) = n , Γ ⊢ e ⇓ τ

-- Dissertation: Theorem 4.11 thm:plug-decomposition (Plug Decomposition - Totality), §4.4.
-- Generalised plug decomposition: for well-typed plug C e in any mode
plug-decompose : ∀ {n Γ e} (C : Ctx) (p : Position) →
  PositionTyping n Γ (plug C e) p → PlugResult n Γ C e p
plug-decompose C (synPos _) d = plug-syn C d
plug-decompose C (anaPos _) d = plug-ana C d

-- Soundness: classification + focus typing → full typing derivation (plug-compose)
mutual
  plug-compose-syn : ∀ {n Γ n' Γ' C e τ m}
    → n , Γ ⊢ C at synPos τ ▷ n' , Γ' [ m ]
    → FocusTyping n' Γ' e m
    → n , Γ ⊢ plug C e ⇑ τ

  plug-compose-syn s○ ft = ft
  plug-compose-syn (sλ: wf cls) ft = ⇑λ: wf (plug-compose-syn cls ft)
  plug-compose-syn (s∘₁ cls eq d₂) ft = ⇑∘ (plug-compose-syn cls ft) eq d₂
  plug-compose-syn (s∘₂ d₁ eq cls) ft = ⇑∘ d₁ eq (plug-compose-ana cls ft)
  plug-compose-syn (s<>₁ cls eq wf) ft = ⇑<> (plug-compose-syn cls ft) eq wf
  plug-compose-syn (s&₁ cls d₂) ft = ⇑& (plug-compose-syn cls ft) d₂
  plug-compose-syn (s&₂ d₁ cls) ft = ⇑& d₁ (plug-compose-syn cls ft)
  plug-compose-syn (scase₁ d₀ eq cls d₂ con) ft = ⇑case d₀ eq (plug-compose-syn cls ft) d₂ con
  plug-compose-syn (scase₂ d₀ eq d₁ cls con) ft = ⇑case d₀ eq d₁ (plug-compose-syn cls ft) con
  plug-compose-syn (sπ₁ cls eq) ft = ⇑π₁ (plug-compose-syn cls ft) eq
  plug-compose-syn (sπ₂ cls eq) ft = ⇑π₂ (plug-compose-syn cls ft) eq
  plug-compose-syn (sι₁ cls) ft = ⇑ι₁ (plug-compose-syn cls ft)
  plug-compose-syn (sι₂ cls) ft = ⇑ι₂ (plug-compose-syn cls ft)
  plug-compose-syn (sΛ cls) ft = ⇑Λ (plug-compose-syn cls ft)
  plug-compose-syn (sdef₁ cls d₂) ft = ⇑def (plug-compose-syn cls ft) d₂
  plug-compose-syn (sdef₂ d₁ cls) ft = ⇑def d₁ (plug-compose-syn cls ft)

  plug-compose-ana : ∀ {n Γ n' Γ' C e τ m}
    → n , Γ ⊢ C at anaPos τ ▷ n' , Γ' [ m ]
    → FocusTyping n' Γ' e m
    → n , Γ ⊢ plug C e ⇓ τ

  plug-compose-ana a○ ft = ft
  plug-compose-ana (aSub cls con) ft = ⇓Sub (plug-compose-syn cls ft) con
  plug-compose-ana (aλ: c eq wf cls) ft = ⇓λ: c eq wf (plug-compose-ana cls ft)
  plug-compose-ana (aλ⇒ eq cls) ft = ⇓λ eq (plug-compose-ana cls ft)
  plug-compose-ana (a&₁ eq cls d₂) ft = ⇓& eq (plug-compose-ana cls ft) d₂
  plug-compose-ana (a&₂ eq d₁ cls) ft = ⇓& eq d₁ (plug-compose-ana cls ft)
  plug-compose-ana (aι₁ eq cls) ft = ⇓ι₁ eq (plug-compose-ana cls ft)
  plug-compose-ana (aι₂ eq cls) ft = ⇓ι₂ eq (plug-compose-ana cls ft)
  plug-compose-ana (acase₁ d₀ eq cls d₂) ft = ⇓case d₀ eq (plug-compose-ana cls ft) d₂
  plug-compose-ana (acase₂ d₀ eq d₁ cls) ft = ⇓case d₀ eq d₁ (plug-compose-ana cls ft)
  plug-compose-ana (adef₁ cls d₂) ft = ⇓def (plug-compose-syn cls ft) d₂
  plug-compose-ana (adef₂ d₁ cls) ft = ⇓def d₁ (plug-compose-ana cls ft)

-- Dissertation: Theorem 4.12 thm:plug-composition (Plug Composition - Soundness), §4.4.
-- Generalised plug composition
plug-compose : ∀ {n Γ n' Γ' C e p m}
  → n , Γ ⊢ C at p ▷ n' , Γ' [ m ]
  → FocusTyping n' Γ' e m
  → PositionTyping n Γ (plug C e) p
plug-compose {p = synPos _} cls ft = plug-compose-syn cls ft
plug-compose {p = anaPos _} cls ft = plug-compose-ana cls ft
