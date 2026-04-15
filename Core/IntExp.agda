module Core.IntExp where

open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _∸_) renaming (_+_ to _ℕ+_; _≟_ to _≟ℕ_)
open import Data.Bool using (true; false)
open import Relation.Nullary using (yes; no)
open import Core.Typ using (Typ)
open import Core.Typ.Substitution as TS using ([_↦_]_)

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

-- Shift free term variables: cutoff c, amount a
private
  shift-e : ℕ → ℕ → IntExp → IntExp
  shift-e c a □                = □
  shift-e c a *                = *
  shift-e c a ⟨ k ⟩            with k <ᵇ c
  ...                          | true  = ⟨ k ⟩
  ...                          | false = ⟨ k ℕ+ a ⟩
  shift-e c a (λ: τ ⇒ d)      = λ: τ ⇒ shift-e (suc c) a d
  shift-e c a (d₁ ∘ d₂)       = shift-e c a d₁ ∘ shift-e c a d₂
  shift-e c a (d < τ >)        = shift-e c a d < τ >
  shift-e c a (d₁ & d₂)       = shift-e c a d₁ & shift-e c a d₂
  shift-e c a (ι₁ d)           = ι₁ (shift-e c a d)
  shift-e c a (ι₂ d)           = ι₂ (shift-e c a d)
  shift-e c a (case d of d₁ · d₂) =
    case shift-e c a d of shift-e (suc c) a d₁ · shift-e (suc c) a d₂
  shift-e c a (π₁ d)           = π₁ (shift-e c a d)
  shift-e c a (π₂ d)           = π₂ (shift-e c a d)
  shift-e c a (Λ d)            = Λ (shift-e c a d)
  shift-e c a (def d₁ ⊢ d₂)   = def shift-e c a d₁ ⊢ shift-e (suc c) a d₂
  shift-e c a (d ⟪ τ₁ ⇛ τ₂ ⟫)  = shift-e c a d ⟪ τ₁ ⇛ τ₂ ⟫
  shift-e c a (d ⟪ τ₁ ⇛⊥ τ₂ ⟫) = shift-e c a d ⟪ τ₁ ⇛⊥ τ₂ ⟫

  -- Term substitution
  sub-e : ℕ → IntExp → IntExp → IntExp
  sub-e n v □                = □
  sub-e n v *                = *
  sub-e n v ⟨ m ⟩            with m ≟ℕ n
  ...                        | yes _ = v
  ...                        | no  _ with m <ᵇ n
  ...                                   | true  = ⟨ m ⟩
  ...                                   | false = ⟨ m ∸ 1 ⟩
  sub-e n v (λ: τ ⇒ d)      = λ: τ ⇒ sub-e (suc n) (shift-e 0 1 v) d
  sub-e n v (d₁ ∘ d₂)       = sub-e n v d₁ ∘ sub-e n v d₂
  sub-e n v (d < τ >)        = sub-e n v d < τ >
  sub-e n v (d₁ & d₂)       = sub-e n v d₁ & sub-e n v d₂
  sub-e n v (ι₁ d)           = ι₁ (sub-e n v d)
  sub-e n v (ι₂ d)           = ι₂ (sub-e n v d)
  sub-e n v (case d of d₁ · d₂) =
    case sub-e n v d of sub-e (suc n) (shift-e 0 1 v) d₁ · sub-e (suc n) (shift-e 0 1 v) d₂
  sub-e n v (π₁ d)           = π₁ (sub-e n v d)
  sub-e n v (π₂ d)           = π₂ (sub-e n v d)
  sub-e n v (Λ d)            = Λ (sub-e n v d)
  sub-e n v (def d₁ ⊢ d₂)   = def sub-e n v d₁ ⊢ sub-e (suc n) (shift-e 0 1 v) d₂
  sub-e n v (d ⟪ τ₁ ⇛ τ₂ ⟫)  = sub-e n v d ⟪ τ₁ ⇛ τ₂ ⟫
  sub-e n v (d ⟪ τ₁ ⇛⊥ τ₂ ⟫) = sub-e n v d ⟪ τ₁ ⇛⊥ τ₂ ⟫

  -- Substitute types into terms
  sub-t : ℕ → Typ → IntExp → IntExp
  sub-t n σ □                = □
  sub-t n σ *                = *
  sub-t n σ ⟨ m ⟩            = ⟨ m ⟩
  sub-t n σ (λ: τ ⇒ d)      = λ: [ n ↦ σ ] τ ⇒ sub-t n σ d
  sub-t n σ (d₁ ∘ d₂)       = sub-t n σ d₁ ∘ sub-t n σ d₂
  sub-t n σ (d < τ >)        = sub-t n σ d < [ n ↦ σ ] τ >
  sub-t n σ (d₁ & d₂)       = sub-t n σ d₁ & sub-t n σ d₂
  sub-t n σ (ι₁ d)           = ι₁ (sub-t n σ d)
  sub-t n σ (ι₂ d)           = ι₂ (sub-t n σ d)
  sub-t n σ (case d of d₁ · d₂) =
    case sub-t n σ d of sub-t n σ d₁ · sub-t n σ d₂
  sub-t n σ (π₁ d)           = π₁ (sub-t n σ d)
  sub-t n σ (π₂ d)           = π₂ (sub-t n σ d)
  sub-t n σ (Λ d)            = Λ (sub-t (suc n) σ d)
  sub-t n σ (def d₁ ⊢ d₂)   = def sub-t n σ d₁ ⊢ sub-t n σ d₂
  sub-t n σ (d ⟪ τ₁ ⇛ τ₂ ⟫)  = sub-t n σ d ⟪ [ n ↦ σ ] τ₁ ⇛ [ n ↦ σ ] τ₂ ⟫
  sub-t n σ (d ⟪ τ₁ ⇛⊥ τ₂ ⟫) = sub-t n σ d ⟪ [ n ↦ σ ] τ₁ ⇛⊥ [ n ↦ σ ] τ₂ ⟫

-- Syntax
[_↦e_]_ : IntExp → ℕ → IntExp → IntExp
[ v ↦e n ] d = sub-e n v d

[_↦t_]_ : Typ → ℕ → IntExp → IntExp
[ σ ↦t n ] d = sub-t n σ d
