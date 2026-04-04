module Core.Exp.Precision where

open import Relation.Binary using (IsPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)

open import Core.Typ using (Typ; _⊑t_; ⊑t-refl; ⊑t-trans; ⊑t-antisym)
open import Core.Exp.Base

-- Slices (Precision) for expressions
data _⊑e_ : Exp → Exp → Set where
  ⊑□   : ∀ {e}               →                                   □e           ⊑e e
  ⊑*   :                                                         *e           ⊑e *e
  ⊑Var : ∀ {n}               →                                   < n >        ⊑e < n >
  ⊑λ   : ∀ {τ τ' e e'}       → τ ⊑t τ' → e ⊑e e'               → λ· τ ⇒ e    ⊑e λ· τ' ⇒ e'
  ⊑∘   : ∀ {e₁ e₂ e₁' e₂'}   → e₁ ⊑e e₁' → e₂ ⊑e e₂'           → e₁ ∘ e₂     ⊑e e₁' ∘ e₂'
  ⊑&   : ∀ {e₁ e₂ e₁' e₂'}   → e₁ ⊑e e₁' → e₂ ⊑e e₂'           → e₁ & e₂     ⊑e e₁' & e₂'
  ⊑ιₗ  : ∀ {e e'}            → e ⊑e e'                         → ιₗ e        ⊑e ιₗ e'
  ⊑ιᵣ  : ∀ {e e'}            → e ⊑e e'                         → ιᵣ e        ⊑e ιᵣ e'
  ⊑Λ   : ∀ {e e'}            → e ⊑e e'                         → Λ e         ⊑e Λ e'
  ⊑def : ∀ {e₁ e₂ e₁' e₂'}   → e₁ ⊑e e₁' → e₂ ⊑e e₂'           → def e₁ ⊢ e₂ ⊑e def e₁' ⊢ e₂'

infix 4 _⊑e_

-- Slices form a partial order
⊑e-refl : Reflexive _⊑e_
⊑e-refl {□e}         = ⊑□
⊑e-refl {*e}         = ⊑*
⊑e-refl {< _ >}      = ⊑Var
⊑e-refl {λ· _ ⇒ _}   = ⊑λ ⊑t-refl ⊑e-refl
⊑e-refl {_ ∘ _}      = ⊑∘ ⊑e-refl ⊑e-refl
⊑e-refl {_ & _}      = ⊑& ⊑e-refl ⊑e-refl
⊑e-refl {ιₗ _}       = ⊑ιₗ ⊑e-refl
⊑e-refl {ιᵣ _}       = ⊑ιᵣ ⊑e-refl
⊑e-refl {Λ _}        = ⊑Λ ⊑e-refl
⊑e-refl {def _ ⊢ _}  = ⊑def ⊑e-refl ⊑e-refl

⊑e-trans : Transitive _⊑e_
⊑e-trans ⊑□ _                 = ⊑□
⊑e-trans ⊑* ⊑*                = ⊑*
⊑e-trans ⊑Var ⊑Var            = ⊑Var
⊑e-trans (⊑λ p q) (⊑λ r s)    = ⊑λ (⊑t-trans p r) (⊑e-trans q s)
⊑e-trans (⊑∘ p q) (⊑∘ r s)    = ⊑∘ (⊑e-trans p r) (⊑e-trans q s)
⊑e-trans (⊑& p q) (⊑& r s)    = ⊑& (⊑e-trans p r) (⊑e-trans q s)
⊑e-trans (⊑ιₗ p) (⊑ιₗ q)      = ⊑ιₗ (⊑e-trans p q)
⊑e-trans (⊑ιᵣ p) (⊑ιᵣ q)      = ⊑ιᵣ (⊑e-trans p q)
⊑e-trans (⊑Λ p) (⊑Λ q)        = ⊑Λ (⊑e-trans p q)
⊑e-trans (⊑def p q) (⊑def r s) = ⊑def (⊑e-trans p r) (⊑e-trans q s)

⊑e-antisym : Antisymmetric _≡_ _⊑e_
⊑e-antisym ⊑□ ⊑□                = refl
⊑e-antisym ⊑* ⊑*                = refl
⊑e-antisym ⊑Var ⊑Var            = refl
⊑e-antisym (⊑λ p q) (⊑λ r s)    = cong₂ λ·_⇒_ (⊑t-antisym p r) (⊑e-antisym q s)
⊑e-antisym (⊑∘ p q) (⊑∘ r s)    = cong₂ _∘_ (⊑e-antisym p r) (⊑e-antisym q s)
⊑e-antisym (⊑& p q) (⊑& r s)    = cong₂ _&_ (⊑e-antisym p r) (⊑e-antisym q s)
⊑e-antisym (⊑ιₗ p) (⊑ιₗ q)      = cong ιₗ (⊑e-antisym p q)
⊑e-antisym (⊑ιᵣ p) (⊑ιᵣ q)      = cong ιᵣ (⊑e-antisym p q)
⊑e-antisym (⊑Λ p) (⊑Λ q)        = cong Λ (⊑e-antisym p q)
⊑e-antisym (⊑def p q) (⊑def r s) = cong₂ def_⊢_ (⊑e-antisym p r) (⊑e-antisym q s)

⊑e-isPartialOrder : IsPartialOrder _≡_ _⊑e_
⊑e-isPartialOrder = record
  { isPreorder = record
    { isEquivalence = Eq.isEquivalence
    ; reflexive = λ where refl → ⊑e-refl
    ; trans = ⊑e-trans
    }
  ; antisym = ⊑e-antisym
  }
