module Core.IntExp where

open import Data.Nat using (ℕ)
open import Core.Typ using (Typ)

-- Internal expressions: the target of elaboration (no unannotated lambdas, plus cast terms)
data IntExp : Set where
  □              : IntExp
  *              : IntExp
  ⟨_⟩            : ℕ → IntExp
  λ:_⇒_         : Typ → IntExp → IntExp
  _∘_            : IntExp → IntExp → IntExp
  _<_>           : IntExp → Typ → IntExp
  _&_            : IntExp → IntExp → IntExp
  ι₁             : IntExp → IntExp
  ι₂             : IntExp → IntExp
  case_of_·_     : IntExp → IntExp → IntExp → IntExp
  π₁             : IntExp → IntExp
  π₂             : IntExp → IntExp
  Λ              : IntExp → IntExp
  def_⊢_         : IntExp → IntExp → IntExp
  _⟪_⇛_⟫        : IntExp → Typ → Typ → IntExp    -- Cast
  _⟪_⇛⊥_⟫       : IntExp → Typ → Typ → IntExp    -- Failed cast

infixr 5  λ:_⇒_
infixr 5  def_⊢_
infixl 22 _∘_
infixl 22 _<_>
infixl 23 _&_

-- TODO: make instances?
-- term substitution
postulate
  [_↦e_]_ : IntExp → ℕ → IntExp → IntExp

-- type-in-term substitution
postulate
  [_↦t_]_ : Typ → ℕ → IntExp → IntExp
