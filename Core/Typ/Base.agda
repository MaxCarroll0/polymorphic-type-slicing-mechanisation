module Core.Typ.Base where

open import Data.Nat using (ℕ; _≟_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Agda.Builtin.FromNat using (Number; fromNat)

-- Types
data Typ : Set where
  ⟨_⟩ : ℕ → Typ  -- Type variables (nats: de Bruijn)
  *   : Typ
  □   : Typ
  _+_ : Typ → Typ → Typ
  _×_ : Typ → Typ → Typ
  _⇒_ : Typ → Typ → Typ
  ∀·  : Typ → Typ

infixl 23 _+_
infixl 24 _×_
infixr 25 _⇒_
infix 4 _kind?_

-- Classify types by their 'kinds' i.e. the kind of their top-most constructor
data _kind?_ : Typ → Typ → Set where
  kindVar : ∀ {m n}           → ⟨ m ⟩   kind? ⟨ n ⟩
  kind*   :                     *       kind? *
  kind□   :                     □       kind? □
  kind+   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ + τ₂ kind? τ₁' + τ₂'
  kind×   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ × τ₂ kind? τ₁' × τ₂'
  kind⇒   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⇒ τ₂ kind? τ₁' ⇒ τ₂'
  kind∀   : ∀ {τ τ'}          → ∀· τ    kind? ∀· τ'
  diff    : ∀ {τ τ'}          → τ       kind? τ'

diag : (τ τ' : Typ) → τ kind? τ'
diag *          *          = kind*
diag □         □           = kind□
diag ⟨ m ⟩     ⟨ n ⟩       = kindVar
diag (τ₁ + τ₂) (τ₁' + τ₂') = kind+
diag (τ₁ × τ₂) (τ₁' × τ₂') = kind×
diag (τ₁ ⇒ τ₂) (τ₁' ⇒ τ₂') = kind⇒
diag (∀· τ)    (∀· τ')     = kind∀
diag τ         τ'          = diff

shallow-disequality : {τ : Typ} → ¬(diag τ τ ≡ diff)
shallow-disequality {⟨ x ⟩}    = λ ()
shallow-disequality {*}        = λ ()
shallow-disequality {□}        = λ ()
shallow-disequality {(τ + τ₁)} = λ ()
shallow-disequality {(τ × τ₁)} = λ ()
shallow-disequality {(τ ⇒ τ₁)} = λ ()
shallow-disequality {(∀· τ)}   = λ ()

-- Literal overloading: allow writing 0, 1 instead of ⟨ 0 ⟩, ⟨ 1 ⟩
instance
  NumTyp : Number Typ
  NumTyp = record
    { Constraint = λ _ → ⊤
    ; fromNat = λ n → ⟨ n ⟩
    }

private
  -- Test: literals work as type variables
  _ : Typ
  _ = 0 ⇒ 1
