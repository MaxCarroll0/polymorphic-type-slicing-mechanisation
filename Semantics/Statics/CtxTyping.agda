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

FocusTyping : Assms → Exp → CtxMode → Set
FocusTyping Γ' e ⇒mode       = ∃ λ τ' → Γ' ⊢ e ↦ τ'
FocusTyping Γ' e (⇐mode τ')  = Γ' ⊢ e ↤ τ'

-- Context classification judgement
-- Γ ⊢ C at p ▷ Γ' [ m ] means:
--   Under outer assumptions Γ, context C in position p
--   has its focus under assumptions Γ' in mode m
data _⊢_at_▷_[_] : Assms → Ctx → Position → Assms → CtxMode → Set where
  s○      : ∀ {Γ}                                                                                →
            Γ ⊢ ○ at synPos ▷ Γ [ ⇒mode ]

  a○      : ∀ {Γ τ}                                                                              →
            Γ ⊢ ○ at anaPos τ ▷ Γ [ ⇐mode τ ]

  -- Subsumption: any synthesis classification works for analysis too
  aSub    : ∀ {Γ Γ' C τ m}     → Γ ⊢ C at synPos ▷ Γ' [ m ]                                     →
            Γ ⊢ C at anaPos τ ▷ Γ' [ m ]

  sλ:     : ∀ {Γ Γ' τ C m}     → (τ ∷ Γ) ⊢ C at synPos ▷ Γ' [ m ]                              →
            Γ ⊢ λ: τ ⇒ C at synPos ▷ Γ' [ m ]

  aλ:     : ∀ {Γ Γ' C τ τ₁ τ₂ m}
            → τ ~ τ₁ ⇒ □       → τ ⊔ τ₁ ⇒ □ ≡ τ₁ ⇒ τ₂
            → (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ Γ' [ m ]                                              →
            Γ ⊢ λ: τ₁ ⇒ C at anaPos τ ▷ Γ' [ m ]

  aλ⇒     : ∀ {Γ Γ' C τ τ₁ τ₂ m}
            → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂
            → (τ₁ ∷ Γ) ⊢ C at anaPos τ₂ ▷ Γ' [ m ]                                              →
            Γ ⊢ λ⇒ C at anaPos τ ▷ Γ' [ m ]

  s∘₁     : ∀ {Γ Γ' C e m}     → Γ ⊢ C at synPos ▷ Γ' [ m ]                                    →
            Γ ⊢ C ∘₁ e at synPos ▷ Γ' [ m ]

  s∘₂     : ∀ {Γ Γ' e C τ τ₁ τ₂ m}
            → Γ ⊢ e ↦ τ        → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂
            → Γ ⊢ C at anaPos τ₁ ▷ Γ' [ m ]                                                     →
            Γ ⊢ e ∘₂ C at synPos ▷ Γ' [ m ]

  s<>₁    : ∀ {Γ Γ' C τ m}     → Γ ⊢ C at synPos ▷ Γ' [ m ]                                    →
            Γ ⊢ C < τ >₁ at synPos ▷ Γ' [ m ]
            
  s&₁     : ∀ {Γ Γ' C e m}     → Γ ⊢ C at synPos ▷ Γ' [ m ]                                    →
            Γ ⊢ C &₁ e at synPos ▷ Γ' [ m ]

  s&₂     : ∀ {Γ Γ' C e m}     → Γ ⊢ C at synPos ▷ Γ' [ m ]                                    →
            Γ ⊢ e &₂ C at synPos ▷ Γ' [ m ]

  a&₁     : ∀ {Γ Γ' C e τ τ₁ τ₂ m}
            → τ ⊔ □ × □ ≡ τ₁ × τ₂
            → Γ ⊢ C at anaPos τ₁ ▷ Γ' [ m ]                                                     →
            Γ ⊢ C &₁ e at anaPos τ ▷ Γ' [ m ]

  a&₂     : ∀ {Γ Γ' C e τ τ₁ τ₂ m}
            → τ ⊔ □ × □ ≡ τ₁ × τ₂
            → Γ ⊢ C at anaPos τ₂ ▷ Γ' [ m ]                                                     →
            Γ ⊢ e &₂ C at anaPos τ ▷ Γ' [ m ]

  aι₁     : ∀ {Γ Γ' C τ τ₁ τ₂ m}
            → τ ⊔ □ + □ ≡ τ₁ + τ₂
            → Γ ⊢ C at anaPos τ₁ ▷ Γ' [ m ]                                                     →
            Γ ⊢ ι₁ C at anaPos τ ▷ Γ' [ m ]

  aι₂     : ∀ {Γ Γ' C τ τ₁ τ₂ m}
            → τ ⊔ □ + □ ≡ τ₁ + τ₂
            → Γ ⊢ C at anaPos τ₂ ▷ Γ' [ m ]                                                     →
            Γ ⊢ ι₂ C at anaPos τ ▷ Γ' [ m ]

  scase₁  : ∀ {Γ Γ' e C e' τ τ₁ τ₂ m}
            → Γ ⊢ e ↦ τ        → τ ⊔ □ + □ ≡ τ₁ + τ₂
            → (τ₁ ∷ Γ) ⊢ C at synPos ▷ Γ' [ m ]                                                →
            Γ ⊢ case e of C ·₁ e' at synPos ▷ Γ' [ m ]

  scase₂  : ∀ {Γ Γ' e e' C τ τ₁ τ₂ m}
            → Γ ⊢ e ↦ τ        → τ ⊔ □ + □ ≡ τ₁ + τ₂
            → (τ₂ ∷ Γ) ⊢ C at synPos ▷ Γ' [ m ]                                                →
            Γ ⊢ case e of₂ e' · C at synPos ▷ Γ' [ m ]

  acase₁  : ∀ {Γ Γ' e C e' τ τ₀ τ₁ τ₂ m}
            → Γ ⊢ e ↦ τ₀       → τ₀ ⊔ □ + □ ≡ τ₁ + τ₂
            → (τ₁ ∷ Γ) ⊢ C at anaPos τ ▷ Γ' [ m ]                                              →
            Γ ⊢ case e of C ·₁ e' at anaPos τ ▷ Γ' [ m ]

  acase₂  : ∀ {Γ Γ' e e' C τ τ₀ τ₁ τ₂ m}
            → Γ ⊢ e ↦ τ₀       → τ₀ ⊔ □ + □ ≡ τ₁ + τ₂
            → (τ₂ ∷ Γ) ⊢ C at anaPos τ ▷ Γ' [ m ]                                              →
            Γ ⊢ case e of₂ e' · C at anaPos τ ▷ Γ' [ m ]

  sπ₁     : ∀ {Γ Γ' C m}       → Γ ⊢ C at synPos ▷ Γ' [ m ]                                    →
            Γ ⊢ π₁ C at synPos ▷ Γ' [ m ]

  sπ₂     : ∀ {Γ Γ' C m}       → Γ ⊢ C at synPos ▷ Γ' [ m ]                                    →
            Γ ⊢ π₂ C at synPos ▷ Γ' [ m ]

  sΛ      : ∀ {Γ Γ' C m}       → Γ ⊢ C at synPos ▷ Γ' [ m ]                                    →
            Γ ⊢ Λ C at synPos ▷ Γ' [ m ]

  sdef₁   : ∀ {Γ Γ' C e m}     → Γ ⊢ C at synPos ▷ Γ' [ m ]                                    →
            Γ ⊢ def C ⊢₁ e at synPos ▷ Γ' [ m ]

  sdef₂   : ∀ {Γ Γ' e C τ' m}
            → Γ ⊢ e ↦ τ'       → (τ' ∷ Γ) ⊢ C at synPos ▷ Γ' [ m ]                             →
            Γ ⊢ def e ⊢₂ C at synPos ▷ Γ' [ m ]

  adef₁   : ∀ {Γ Γ' C e τ m}   → Γ ⊢ C at synPos ▷ Γ' [ m ]                                    →
            Γ ⊢ def C ⊢₁ e at anaPos τ ▷ Γ' [ m ]

  adef₂   : ∀ {Γ Γ' e C τ τ' m}
            → Γ ⊢ e ↦ τ'       → (τ' ∷ Γ) ⊢ C at anaPos τ ▷ Γ' [ m ]                           →
            Γ ⊢ def e ⊢₂ C at anaPos τ ▷ Γ' [ m ]

-- Result type for plug decomposition
PlugResult : Assms → Ctx → Exp → Position → Set
PlugResult Γ C e p = Σ Assms λ Γ' → Σ CtxMode λ m → Γ ⊢ C at p ▷ Γ' [ m ] ×' FocusTyping Γ' e m

-- Plug decomposition theorem
-- For any plugged context Γ ⊢ plug C e ↦ τ, we can classify C and extract
-- the corresponding typing of the focus e
mutual
  plug-syn : ∀ {Γ e τ} (C : Ctx) → Γ ⊢ plug C e ↦ τ → PlugResult Γ C e synPos

  plug-syn ○ d =
    _ , ⇒mode , s○ , _ , d
  plug-syn (λ: τ ⇒ C) (↦λ: d) with plug-syn C d
  ... | Γ' , m , cls , ft = Γ' , m , sλ: cls , ft
  plug-syn (λ⇒ C) ()
  plug-syn (C ∘₁ e₂) (↦∘ d₁ _ _) with plug-syn C d₁
  ... | Γ' , m , cls , ft = Γ' , m , s∘₁ cls , ft
  plug-syn (e₁ ∘₂ C) (↦∘ d₁ eq d₂) with plug-ana C d₂
  ... | Γ' , m , cls , ft = Γ' , m , s∘₂ d₁ eq cls , ft
  plug-syn (C < τ >₁) (↦<> d₁ _) with plug-syn C d₁
  ... | Γ' , m , cls , ft = Γ' , m , s<>₁ cls , ft
  plug-syn (C &₁ e₂) (↦& d₁ _) with plug-syn C d₁
  ... | Γ' , m , cls , ft = Γ' , m , s&₁ cls , ft
  plug-syn (e₁ &₂ C) (↦& _ d₂) with plug-syn C d₂
  ... | Γ' , m , cls , ft = Γ' , m , s&₂ cls , ft
  plug-syn (ι₁ C) ()
  plug-syn (ι₂ C) ()
  plug-syn (case e₀ of C ·₁ e₂) (↦case d₀ eq d₁ _ _) with plug-syn C d₁
  ... | Γ' , m , cls , ft = Γ' , m , scase₁ d₀ eq cls , ft
  plug-syn (case e₀ of₂ e₁ · C) (↦case d₀ eq _ d₂ _) with plug-syn C d₂
  ... | Γ' , m , cls , ft = Γ' , m , scase₂ d₀ eq cls , ft
  plug-syn (π₁ C) (↦π₁ d₁ _) with plug-syn C d₁
  ... | Γ' , m , cls , ft = Γ' , m , sπ₁ cls , ft
  plug-syn (π₂ C) (↦π₂ d₁ _) with plug-syn C d₁
  ... | Γ' , m , cls , ft = Γ' , m , sπ₂ cls , ft
  plug-syn (Λ C) (↦Λ d₁) with plug-syn C d₁
  ... | Γ' , m , cls , ft = Γ' , m , sΛ cls , ft
  plug-syn (def C ⊢₁ e₂) (↦def d₁ _) with plug-syn C d₁
  ... | Γ' , m , cls , ft = Γ' , m , sdef₁ cls , ft
  plug-syn (def e₁ ⊢₂ C) (↦def d₁ d₂) with plug-syn C d₂
  ... | Γ' , m , cls , ft = Γ' , m , sdef₂ d₁ cls , ft

  plug-ana : ∀ {Γ e τ} (C : Ctx) → Γ ⊢ plug C e ↤ τ → PlugResult Γ C e (anaPos τ)

  plug-ana ○ (↤Sub d _) =
    _ , ⇒mode , aSub s○ , _ , d
  plug-ana ○ d =
    _ , ⇐mode _ , a○ , d
  plug-ana (λ: τ ⇒ C) (↤Sub d _) with plug-syn (λ: τ ⇒ C) d
  ... | Γ' , m , cls , ft = Γ' , m , aSub cls , ft
  plug-ana (λ: τ₁ ⇒ C) (↤λ: c eq d) with plug-ana C d
  ... | Γ' , m , cls , ft = Γ' , m , aλ: c eq cls , ft
  plug-ana (λ⇒ C) (↤Sub () _)
  plug-ana (λ⇒ C) (↤λ eq d) with plug-ana C d
  ... | Γ' , m , cls , ft = Γ' , m , aλ⇒ eq cls , ft
  plug-ana (C ∘₁ e₂) (↤Sub d _) with plug-syn (C ∘₁ e₂) d
  ... | Γ' , m , cls , ft = Γ' , m , aSub cls , ft
  plug-ana (e₁ ∘₂ C) (↤Sub d _) with plug-syn (e₁ ∘₂ C) d
  ... | Γ' , m , cls , ft = Γ' , m , aSub cls , ft
  plug-ana (C < τ >₁) (↤Sub d _) with plug-syn (C < τ >₁) d
  ... | Γ' , m , cls , ft = Γ' , m , aSub cls , ft
  plug-ana (C &₁ e₂) (↤Sub d _) with plug-syn (C &₁ e₂) d
  ... | Γ' , m , cls , ft = Γ' , m , aSub cls , ft
  plug-ana (C &₁ e₂) (↤& eq d₁ _) with plug-ana C d₁
  ... | Γ' , m , cls , ft = Γ' , m , a&₁ eq cls , ft
  plug-ana (e₁ &₂ C) (↤Sub d _) with plug-syn (e₁ &₂ C) d
  ... | Γ' , m , cls , ft = Γ' , m , aSub cls , ft
  plug-ana (e₁ &₂ C) (↤& eq _ d₂) with plug-ana C d₂
  ... | Γ' , m , cls , ft = Γ' , m , a&₂ eq cls , ft
  plug-ana (ι₁ C) (↤Sub () _)
  plug-ana (ι₁ C) (↤ι₁ eq d) with plug-ana C d
  ... | Γ' , m , cls , ft = Γ' , m , aι₁ eq cls , ft
  plug-ana (ι₂ C) (↤Sub () _)
  plug-ana (ι₂ C) (↤ι₂ eq d) with plug-ana C d
  ... | Γ' , m , cls , ft = Γ' , m , aι₂ eq cls , ft
  plug-ana (case e₀ of C ·₁ e₂) (↤Sub d _) with plug-syn (case e₀ of C ·₁ e₂) d
  ... | Γ' , m , cls , ft = Γ' , m , aSub cls , ft
  plug-ana (case e₀ of C ·₁ e₂) (↤case d₀ eq d₁ _) with plug-ana C d₁
  ... | Γ' , m , cls , ft = Γ' , m , acase₁ d₀ eq cls , ft
  plug-ana (case e₀ of₂ e₁ · C) (↤Sub d _) with plug-syn (case e₀ of₂ e₁ · C) d
  ... | Γ' , m , cls , ft = Γ' , m , aSub cls , ft
  plug-ana (case e₀ of₂ e₁ · C) (↤case d₀ eq _ d₂) with plug-ana C d₂
  ... | Γ' , m , cls , ft = Γ' , m , acase₂ d₀ eq cls , ft
  plug-ana (π₁ C) (↤Sub d _) with plug-syn (π₁ C) d
  ... | Γ' , m , cls , ft = Γ' , m , aSub cls , ft
  plug-ana (π₂ C) (↤Sub d _) with plug-syn (π₂ C) d
  ... | Γ' , m , cls , ft = Γ' , m , aSub cls , ft
  plug-ana (Λ C) (↤Sub d _) with plug-syn (Λ C) d
  ... | Γ' , m , cls , ft = Γ' , m , aSub cls , ft
  plug-ana (def C ⊢₁ e₂) (↤Sub d _) with plug-syn (def C ⊢₁ e₂) d
  ... | Γ' , m , cls , ft = Γ' , m , aSub cls , ft
  plug-ana (def C ⊢₁ e₂) (↤def d₁ _) with plug-syn C d₁
  ... | Γ' , m , cls , ft = Γ' , m , adef₁ cls , ft
  plug-ana (def e₁ ⊢₂ C) (↤Sub d _) with plug-syn (def e₁ ⊢₂ C) d
  ... | Γ' , m , cls , ft = Γ' , m , aSub cls , ft
  plug-ana (def e₁ ⊢₂ C) (↤def d₁ d₂) with plug-ana C d₂
  ... | Γ' , m , cls , ft = Γ' , m , adef₂ d₁ cls , ft

PositionTyping : Assms → Exp → Position → Set
PositionTyping Γ e synPos     = ∃ λ τ → Γ ⊢ e ↦ τ
PositionTyping Γ e (anaPos τ) = Γ ⊢ e ↤ τ

-- Generalised plug decomposition: for well-typed plug C e in any mode,
plug-decompose : ∀ {Γ e} (C : Ctx) (p : Position) →
  PositionTyping Γ (plug C e) p → PlugResult Γ C e p
plug-decompose C synPos     (_ , d) = plug-syn C d
plug-decompose C (anaPos _) d       = plug-ana C d
