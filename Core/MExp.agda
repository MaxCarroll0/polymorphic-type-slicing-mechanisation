module Core.MExp where

open import Data.Nat using (ℕ)
open import Core.Typ using (Typ)

-- Marked expressions
data MExp : Set where
  □              : MExp
  *              : MExp
  ⟨_⟩            : ℕ → MExp
  λ:_⇒_         : Typ → MExp → MExp
  λ⇒_           : MExp → MExp
  _∘_            : MExp → MExp → MExp
  _<_>           : MExp → Typ → MExp
  _&_            : MExp → MExp → MExp
  ι₁             : MExp → MExp
  ι₂             : MExp → MExp
  case_of_·_     : MExp → MExp → MExp → MExp
  π₁             : MExp → MExp
  π₂             : MExp → MExp
  Λ              : MExp → MExp
  def_⊢_         : MExp → MExp → MExp

  -- Error marks
  ⟨_⟩⇑           : ℕ → MExp                    -- Free variable (unbound)
  _⦅≁_⦆          : MExp → Typ → MExp            -- Type inconsistency
  _⦅▸⇒⦆          : MExp → MExp                  -- Expected arrow type
  _⦅▸+⦆          : MExp → MExp                  -- Expected sum type
  _⦅▸×⦆          : MExp → MExp                  -- Expected product type
  _⦅▸∀⦆          : MExp → MExp                  -- Expected forall type
  _⦅~⇒⦆          : MExp → MExp                  -- Lambda against non-arrow
  _⦅~+⦆          : MExp → MExp                  -- Injection against non-sum
  _⦅~×⦆          : MExp → MExp                  -- Pair against non-product

infixr 5  λ:_⇒_
infixr 5  λ⇒_
infixr 5  def_⊢_
infixl 22 _∘_
infixl 22 _<_>
infixl 23 _&_
