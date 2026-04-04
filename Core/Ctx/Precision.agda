module Core.Ctx.Precision where

open import Relation.Binary using (IsPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)

open import Core.Typ using (Typ; _⊑t_; ⊑t-refl; ⊑t-trans; ⊑t-antisym; ⊑?)
open import Core.Exp using (Exp; _⊑e_; ⊑e-refl; ⊑e-trans; ⊑e-antisym; ⊑□; ⊑λ; ⊑∘; ⊑&; ⊑ιₗ; ⊑ιᵣ; ⊑Λ; ⊑def)
open import Core.Ctx.Base

-- Syntactic precision for contexts
-- Note: only matching constructors are related (no global bottom)
data _⊑Ctx_ : Ctx → Ctx → Set where
  ⊑○    :                                               ○           ⊑Ctx ○
  ⊑λ    : ∀ {τ τ' C C'} → τ ⊑t τ' → C ⊑Ctx C'         → λ· τ ⇒ C   ⊑Ctx λ· τ' ⇒ C'
  ⊑∘ₗ   : ∀ {C C' e e'} → C ⊑Ctx C' → e ⊑e e'         → C ∘ₗ e     ⊑Ctx C' ∘ₗ e'
  ⊑∘ᵣ   : ∀ {e e' C C'} → e ⊑e e' → C ⊑Ctx C'         → e ∘ᵣ C     ⊑Ctx e' ∘ᵣ C'
  ⊑&ₗ   : ∀ {C C' e e'} → C ⊑Ctx C' → e ⊑e e'         → C &ₗ e     ⊑Ctx C' &ₗ e'
  ⊑&ᵣ   : ∀ {e e' C C'} → e ⊑e e' → C ⊑Ctx C'         → e &ᵣ C     ⊑Ctx e' &ᵣ C'
  ⊑ιₗ   : ∀ {C C'}      → C ⊑Ctx C'                   → ιₗ C       ⊑Ctx ιₗ C'
  ⊑ιᵣ   : ∀ {C C'}      → C ⊑Ctx C'                   → ιᵣ C       ⊑Ctx ιᵣ C'
  ⊑Λ    : ∀ {C C'}      → C ⊑Ctx C'                   → Λ C        ⊑Ctx Λ C'
  ⊑defₗ : ∀ {C C' e e'} → C ⊑Ctx C' → e ⊑e e'         → def C ⊢ₗ e ⊑Ctx def C' ⊢ₗ e'
  ⊑defᵣ : ∀ {e e' C C'} → e ⊑e e' → C ⊑Ctx C'         → def e ⊢ᵣ C ⊑Ctx def e' ⊢ᵣ C'

infix 4 _⊑Ctx_

-- Precision is reflexive
⊑Ctx-refl : Reflexive _⊑Ctx_
⊑Ctx-refl {○}           = ⊑○
⊑Ctx-refl {λ· _ ⇒ _}    = ⊑λ ⊑t-refl ⊑Ctx-refl
⊑Ctx-refl {_ ∘ₗ _}      = ⊑∘ₗ ⊑Ctx-refl ⊑e-refl
⊑Ctx-refl {_ ∘ᵣ _}      = ⊑∘ᵣ ⊑e-refl ⊑Ctx-refl
⊑Ctx-refl {_ &ₗ _}      = ⊑&ₗ ⊑Ctx-refl ⊑e-refl
⊑Ctx-refl {_ &ᵣ _}      = ⊑&ᵣ ⊑e-refl ⊑Ctx-refl
⊑Ctx-refl {ιₗ _}        = ⊑ιₗ ⊑Ctx-refl
⊑Ctx-refl {ιᵣ _}        = ⊑ιᵣ ⊑Ctx-refl
⊑Ctx-refl {Λ _}         = ⊑Λ ⊑Ctx-refl
⊑Ctx-refl {def _ ⊢ₗ _}  = ⊑defₗ ⊑Ctx-refl ⊑e-refl
⊑Ctx-refl {def _ ⊢ᵣ _}  = ⊑defᵣ ⊑e-refl ⊑Ctx-refl

-- Precision is transitive
⊑Ctx-trans : Transitive _⊑Ctx_
⊑Ctx-trans ⊑○ ⊑○                     = ⊑○
⊑Ctx-trans (⊑λ p q) (⊑λ r s)         = ⊑λ (⊑t-trans p r) (⊑Ctx-trans q s)
⊑Ctx-trans (⊑∘ₗ p q) (⊑∘ₗ r s)       = ⊑∘ₗ (⊑Ctx-trans p r) (⊑e-trans q s)
⊑Ctx-trans (⊑∘ᵣ p q) (⊑∘ᵣ r s)       = ⊑∘ᵣ (⊑e-trans p r) (⊑Ctx-trans q s)
⊑Ctx-trans (⊑&ₗ p q) (⊑&ₗ r s)       = ⊑&ₗ (⊑Ctx-trans p r) (⊑e-trans q s)
⊑Ctx-trans (⊑&ᵣ p q) (⊑&ᵣ r s)       = ⊑&ᵣ (⊑e-trans p r) (⊑Ctx-trans q s)
⊑Ctx-trans (⊑ιₗ p) (⊑ιₗ q)           = ⊑ιₗ (⊑Ctx-trans p q)
⊑Ctx-trans (⊑ιᵣ p) (⊑ιᵣ q)           = ⊑ιᵣ (⊑Ctx-trans p q)
⊑Ctx-trans (⊑Λ p) (⊑Λ q)             = ⊑Λ (⊑Ctx-trans p q)
⊑Ctx-trans (⊑defₗ p q) (⊑defₗ r s)   = ⊑defₗ (⊑Ctx-trans p r) (⊑e-trans q s)
⊑Ctx-trans (⊑defᵣ p q) (⊑defᵣ r s)   = ⊑defᵣ (⊑e-trans p r) (⊑Ctx-trans q s)

-- Precision is antisymmetric
⊑Ctx-antisym : Antisymmetric _≡_ _⊑Ctx_
⊑Ctx-antisym ⊑○ ⊑○                   = refl
⊑Ctx-antisym (⊑λ p q) (⊑λ r s)       = cong₂ λ·_⇒_ (⊑t-antisym p r) (⊑Ctx-antisym q s)
⊑Ctx-antisym (⊑∘ₗ p q) (⊑∘ₗ r s)     = cong₂ _∘ₗ_ (⊑Ctx-antisym p r) (⊑e-antisym q s)
⊑Ctx-antisym (⊑∘ᵣ p q) (⊑∘ᵣ r s)     = cong₂ _∘ᵣ_ (⊑e-antisym p r) (⊑Ctx-antisym q s)
⊑Ctx-antisym (⊑&ₗ p q) (⊑&ₗ r s)     = cong₂ _&ₗ_ (⊑Ctx-antisym p r) (⊑e-antisym q s)
⊑Ctx-antisym (⊑&ᵣ p q) (⊑&ᵣ r s)     = cong₂ _&ᵣ_ (⊑e-antisym p r) (⊑Ctx-antisym q s)
⊑Ctx-antisym (⊑ιₗ p) (⊑ιₗ q)         = cong ιₗ (⊑Ctx-antisym p q)
⊑Ctx-antisym (⊑ιᵣ p) (⊑ιᵣ q)         = cong ιᵣ (⊑Ctx-antisym p q)
⊑Ctx-antisym (⊑Λ p) (⊑Λ q)           = cong Λ (⊑Ctx-antisym p q)
⊑Ctx-antisym (⊑defₗ p q) (⊑defₗ r s) = cong₂ def_⊢ₗ_ (⊑Ctx-antisym p r) (⊑e-antisym q s)
⊑Ctx-antisym (⊑defᵣ p q) (⊑defᵣ r s) = cong₂ def_⊢ᵣ_ (⊑e-antisym p r) (⊑Ctx-antisym q s)

-- Partial order structure
⊑Ctx-isPartialOrder : IsPartialOrder _≡_ _⊑Ctx_
⊑Ctx-isPartialOrder = record
  { isPreorder = record
    { isEquivalence = Eq.isEquivalence
    ; reflexive = λ where refl → ⊑Ctx-refl
    ; trans = ⊑Ctx-trans
    }
  ; antisym = ⊑Ctx-antisym
  }

-- □Ctx is minimum for slices of a specific context
□Ctx-min : ∀ C → □Ctx C ⊑Ctx C
□Ctx-min ○             = ⊑○
□Ctx-min (λ· τ ⇒ C)    = ⊑λ ⊑? (□Ctx-min C)
□Ctx-min (C ∘ₗ e)      = ⊑∘ₗ (□Ctx-min C) ⊑□
□Ctx-min (e ∘ᵣ C)      = ⊑∘ᵣ ⊑□ (□Ctx-min C)
□Ctx-min (C &ₗ e)      = ⊑&ₗ (□Ctx-min C) ⊑□
□Ctx-min (e &ᵣ C)      = ⊑&ᵣ ⊑□ (□Ctx-min C)
□Ctx-min (ιₗ C)        = ⊑ιₗ (□Ctx-min C)
□Ctx-min (ιᵣ C)        = ⊑ιᵣ (□Ctx-min C)
□Ctx-min (Λ C)         = ⊑Λ (□Ctx-min C)
□Ctx-min (def C ⊢ₗ e)  = ⊑defₗ (□Ctx-min C) ⊑□
□Ctx-min (def e ⊢ᵣ C)  = ⊑defᵣ ⊑□ (□Ctx-min C)

-- □Ctx is below any slice of C
□Ctx-min-slice : ∀ {C' C} → C' ⊑Ctx C → □Ctx C ⊑Ctx C'
□Ctx-min-slice ⊑○                   = ⊑○
□Ctx-min-slice (⊑λ _ p)             = ⊑λ ⊑? (□Ctx-min-slice p)
□Ctx-min-slice (⊑∘ₗ p _)            = ⊑∘ₗ (□Ctx-min-slice p) ⊑□
□Ctx-min-slice (⊑∘ᵣ _ p)            = ⊑∘ᵣ ⊑□ (□Ctx-min-slice p)
□Ctx-min-slice (⊑&ₗ p _)            = ⊑&ₗ (□Ctx-min-slice p) ⊑□
□Ctx-min-slice (⊑&ᵣ _ p)            = ⊑&ᵣ ⊑□ (□Ctx-min-slice p)
□Ctx-min-slice (⊑ιₗ p)              = ⊑ιₗ (□Ctx-min-slice p)
□Ctx-min-slice (⊑ιᵣ p)              = ⊑ιᵣ (□Ctx-min-slice p)
□Ctx-min-slice (⊑Λ p)               = ⊑Λ (□Ctx-min-slice p)
□Ctx-min-slice (⊑defₗ p _)          = ⊑defₗ (□Ctx-min-slice p) ⊑□
□Ctx-min-slice (⊑defᵣ _ p)          = ⊑defᵣ ⊑□ (□Ctx-min-slice p)

-- Plug preserves precision
plug-preserves-⊑ : ∀ {C C' e e'} → C ⊑Ctx C' → e ⊑e e' → plug C e ⊑e plug C' e'
plug-preserves-⊑ ⊑○ p                   = p
plug-preserves-⊑ (⊑λ q r) p             = ⊑λ q (plug-preserves-⊑ r p)
plug-preserves-⊑ (⊑∘ₗ q r) p            = ⊑∘ (plug-preserves-⊑ q p) r
plug-preserves-⊑ (⊑∘ᵣ q r) p            = ⊑∘ q (plug-preserves-⊑ r p)
plug-preserves-⊑ (⊑&ₗ q r) p            = ⊑& (plug-preserves-⊑ q p) r
plug-preserves-⊑ (⊑&ᵣ q r) p            = ⊑& q (plug-preserves-⊑ r p)
plug-preserves-⊑ (⊑ιₗ q) p              = ⊑ιₗ (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑ιᵣ q) p              = ⊑ιᵣ (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑Λ q) p               = ⊑Λ (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑defₗ q r) p          = ⊑def (plug-preserves-⊑ q p) r
plug-preserves-⊑ (⊑defᵣ q r) p          = ⊑def q (plug-preserves-⊑ r p)
