module Core.Exp.Base where

open import Data.Nat using (ℕ; _≟_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Agda.Builtin.FromNat using (Number; fromNat)

open import Core.Typ using (Typ)

-- Expressions
data Exp : Set where
  □      : Exp                    -- Expression hole (bottom for slicing)
  *      : Exp                    -- Unit value
  ⟨_⟩    : ℕ → Exp                -- Variables (de Bruijn indices)
  λ·_⇒_  : Typ → Exp → Exp        -- Lambda abstraction
  _∘_    : Exp → Exp → Exp        -- Application
  _&_    : Exp → Exp → Exp        -- Pair
  ι₁     : Exp → Exp              -- Left injection
  ι₂     : Exp → Exp              -- Right injection
  Λ      : Exp → Exp              -- Type abstraction
  def_⊢_ : Exp → Exp → Exp        -- Let binding

infixr 5  λ·_⇒_
infixr 5  def_⊢_
infixl 22 _∘_
infixl 23 _&_
infix  4  _kind?_

-- Literal overloading: allow writing 0, 1 instead of < 0 >, < 1 >
instance
  NumExp : Number Exp
  NumExp = record
    { Constraint = λ _ → ⊤
    ; fromNat = λ n → ⟨ n ⟩
    }

-- Type cast (derived form)
_▸_ : Exp → Typ → Exp
e ▸ τ = (λ· τ ⇒ 0) ∘ e

-- Classify expressions by their 'kinds' i.e. the kind of their top-most constructor
data _kind?_ : Exp → Exp → Set where
  kind□   :                               □            kind? □
  kind*   :                               *            kind? *
  kindVar : ∀ {m n}                     → ⟨ m ⟩        kind? ⟨ n ⟩
  kindλ   : ∀ {τ τ' e e'}               → λ· τ ⇒ e     kind? λ· τ' ⇒ e'
  kind∘   : ∀ {e₁ e₂ e₁' e₂'}           → e₁ ∘ e₂      kind? e₁' ∘ e₂'
  kind&   : ∀ {e₁ e₂ e₁' e₂'}           → e₁ & e₂      kind? e₁' & e₂'
  kindι₁  : ∀ {e e'}                    → ι₁ e         kind? ι₁ e'
  kindι₂  : ∀ {e e'}                    → ι₂ e         kind? ι₂ e'
  kindΛ   : ∀ {e e'}                    → Λ e          kind? Λ e'
  kinddef : ∀ {e₁ e₂ e₁' e₂'}           → def e₁ ⊢ e₂  kind? def e₁' ⊢ e₂'
  diff    : ∀ {e e'}                    → e            kind? e'

diag : (e e' : Exp) → e kind? e'
diag □             □               = kind□
diag *             *               = kind*
diag ⟨ m ⟩         ⟨ n ⟩           = kindVar
diag (λ· τ ⇒ e)    (λ· τ' ⇒ e')    = kindλ
diag (e₁ ∘ e₂)     (e₁' ∘ e₂')     = kind∘
diag (e₁ & e₂)     (e₁' & e₂')     = kind&
diag (ι₁ e)        (ι₁ e')         = kindι₁
diag (ι₂ e)        (ι₂ e')         = kindι₂
diag (Λ e)         (Λ e')          = kindΛ
diag (def e₁ ⊢ e₂) (def e₁' ⊢ e₂') = kinddef
diag _             _               = diff

shallow-disequality : {e : Exp} → ¬(diag e e ≡ diff)
shallow-disequality {□}         = λ ()
shallow-disequality {*}         = λ ()
shallow-disequality {⟨ _ ⟩}     = λ ()
shallow-disequality {λ· _ ⇒ _}  = λ ()
shallow-disequality {_ ∘ _}     = λ ()
shallow-disequality {_ & _}     = λ ()
shallow-disequality {ι₁ _}      = λ ()
shallow-disequality {ι₂ _}      = λ ()
shallow-disequality {Λ _}       = λ ()
shallow-disequality {def _ ⊢ _} = λ ()

