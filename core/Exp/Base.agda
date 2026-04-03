module core.Exp.Base where

open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import core.Typ using (Typ)

-- Expressions
data Exp : Set where
  □e     : Exp                    -- Expression hole (bottom for slicing)
  *e     : Exp                    -- Unit value
  <_>    : ℕ → Exp                -- Variables (de Bruijn indices)
  λ·_⇒_  : Typ → Exp → Exp        -- Lambda abstraction
  _∘_    : Exp → Exp → Exp        -- Application
  _&_    : Exp → Exp → Exp        -- Pair
  ιₗ     : Exp → Exp              -- Left injection
  ιᵣ     : Exp → Exp              -- Right injection
  Λ      : Exp → Exp              -- Type abstraction
  def_⊢_ : Exp → Exp → Exp        -- Let binding

infixl 22 _∘_
infixl 23 _&_

-- Type cast (derived form)
_▸_ : Exp → Typ → Exp
e ▸ τ = (λ· τ ⇒ < 0 >) ∘ e

-- Classify expressions by their 'kinds' i.e. the kind of their top-most constructor
data _kind?_ : Exp → Exp → Set where
  kind□   :                               □e             kind? □e
  kind*   :                               *e             kind? *e
  kindVar : ∀ {m n}                     → < m >          kind? < n >
  kindλ   : ∀ {τ τ' e e'}               → (λ· τ ⇒ e)    kind? (λ· τ' ⇒ e')
  kind∘   : ∀ {e₁ e₂ e₁' e₂'}           → (e₁ ∘ e₂)     kind? (e₁' ∘ e₂')
  kind&   : ∀ {e₁ e₂ e₁' e₂'}           → (e₁ & e₂)     kind? (e₁' & e₂')
  kindιₗ  : ∀ {e e'}                    → ιₗ e          kind? ιₗ e'
  kindιᵣ  : ∀ {e e'}                    → ιᵣ e          kind? ιᵣ e'
  kindΛ   : ∀ {e e'}                    → Λ e           kind? Λ e'
  kinddef : ∀ {e₁ e₂ e₁' e₂'}           → (def e₁ ⊢ e₂) kind? (def e₁' ⊢ e₂')
  diff    : ∀ {e e'}                    → e             kind? e'

diag : (e e' : Exp) → e kind? e'
diag □e           □e             = kind□
diag *e           *e             = kind*
diag < m >        < n >          = kindVar
diag (λ· τ ⇒ e)   (λ· τ' ⇒ e')   = kindλ
diag (e₁ ∘ e₂)    (e₁' ∘ e₂')    = kind∘
diag (e₁ & e₂)    (e₁' & e₂')    = kind&
diag (ιₗ e)       (ιₗ e')        = kindιₗ
diag (ιᵣ e)       (ιᵣ e')        = kindιᵣ
diag (Λ e)        (Λ e')         = kindΛ
diag (def e₁ ⊢ e₂) (def e₁' ⊢ e₂') = kinddef
diag _            _              = diff

shallow-disequality : {e : Exp} → ¬(diag e e ≡ diff)
shallow-disequality {□e}         = λ ()
shallow-disequality {*e}         = λ ()
shallow-disequality {< _ >}      = λ ()
shallow-disequality {λ· _ ⇒ _}   = λ ()
shallow-disequality {_ ∘ _}      = λ ()
shallow-disequality {_ & _}      = λ ()
shallow-disequality {ιₗ _}       = λ ()
shallow-disequality {ιᵣ _}       = λ ()
shallow-disequality {Λ _}        = λ ()
shallow-disequality {def _ ⊢ _}  = λ ()
