open import core.Typ
open import Data.Nat

module core.exp where

  -- Note: (unannotated) let bindings whose binding type is synthesised rules cannot be simulated by functions without adding a new typing rule for type application
  -- (inferring function type from argument). It is difficult to make this work without overlapping typing rules.
  data Exp : Set where
    □e : Exp
    *e : Exp
    <_> : ℕ → Exp
    λ·_⇒_ : Typ → Exp → Exp
    _∘_ : Exp → Exp → Exp
    _&_ : Exp → Exp → Exp
    ιₗ : Exp → Exp
    ιᵣ : Exp → Exp
    Λ : Exp → Exp
    def_⊢_ : Exp → Exp → Exp -- 'let' binding

  -- Type cast
  _▸_ : Exp → Typ → Exp
  e ▸ τ = (λ· τ ⇒ < 0 >) ∘ e 
