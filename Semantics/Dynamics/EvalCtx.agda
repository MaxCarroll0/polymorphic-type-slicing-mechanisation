module Semantics.Dynamics.EvalCtx where

open import Core.Typ using (Typ)
open import Core.IntExp

-- Evaluation contexts (non-deterministic)
data EvalCtx : Set where
  ○              : EvalCtx
  _∘₁_           : EvalCtx → IntExp → EvalCtx
  _∘₂_           : IntExp → EvalCtx → EvalCtx
  _<_>₁          : EvalCtx → Typ → EvalCtx
  _⟪_⇛_⟫₁       : EvalCtx → Typ → Typ → EvalCtx
  _&₁_           : EvalCtx → IntExp → EvalCtx
  _&₂_           : IntExp → EvalCtx → EvalCtx
  ι₁             : EvalCtx → EvalCtx
  ι₂             : EvalCtx → EvalCtx
  case_of_·_     : EvalCtx → IntExp → IntExp → EvalCtx
  π₁             : EvalCtx → EvalCtx
  π₂             : EvalCtx → EvalCtx
  def_⊢_         : EvalCtx → IntExp → EvalCtx

infixr 5  def_⊢_
infixl 22 _∘₁_ _∘₂_
infixl 22 _<_>₁
infixl 23 _&₁_ _&₂_

plug : EvalCtx → IntExp → IntExp
plug ○                    d = d
plug (ε ∘₁ d₂)            d = plug ε d ∘ d₂
plug (d₁ ∘₂ ε)            d = d₁ ∘ plug ε d
plug (ε < τ >₁)           d = plug ε d < τ >
plug (ε ⟪ τ₁ ⇛ τ₂ ⟫₁)    d = plug ε d ⟪ τ₁ ⇛ τ₂ ⟫
plug (ε &₁ d₂)            d = plug ε d & d₂
plug (d₁ &₂ ε)            d = d₁ & plug ε d
plug (ι₁ ε)               d = ι₁ (plug ε d)
plug (ι₂ ε)               d = ι₂ (plug ε d)
plug (case ε of d₁ · d₂)  d = case plug ε d of d₁ · d₂
plug (π₁ ε)               d = π₁ (plug ε d)
plug (π₂ ε)               d = π₂ (plug ε d)
plug (def ε ⊢ d₂)         d = def plug ε d ⊢ d₂
