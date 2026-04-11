module Semantics.Dynamics.Values where

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Core.Typ using (Typ; □; _⇒_; _+_; _×_; ∀·)
open import Core.IntExp
open import Semantics.Dynamics.Ground

data Value : IntExp → Set where
  val*    :                                          Value *
  valλ    : ∀ {τ d}                                → Value (λ: τ ⇒ d)
  valΛ    : ∀ {d}                                  → Value (Λ d)
  val&    : ∀ {d₁ d₂}  → Value d₁ → Value d₂       → Value (d₁ & d₂)
  valι₁   : ∀ {d}      → Value d                   → Value (ι₁ d)
  valι₂   : ∀ {d}      → Value d                   → Value (ι₂ d)

mutual
  data BoxedVal : IntExp → Set where
    bval      : ∀ {d}
              → Value d                              → BoxedVal d
    bvCast⇒   : ∀ {d τ₁ τ₂ τ₃ τ₄}
              → (τ₁ ⇒ τ₂) ≢ (τ₃ ⇒ τ₄)
              → BoxedVal d                           → BoxedVal (d ⟪ τ₁ ⇒ τ₂ ⇛ τ₃ ⇒ τ₄ ⟫)
    bvCastG□  : ∀ {d τ}
              → Ground τ
              → BoxedVal d                           → BoxedVal (d ⟪ τ ⇛ □ ⟫)
    bvCast∀   : ∀ {d τ₁ τ₂}
              → (∀· τ₁) ≢ (∀· τ₂)
              → BoxedVal d                           → BoxedVal (d ⟪ ∀· τ₁ ⇛ ∀· τ₂ ⟫)

  data Indet : IntExp → Set where
    ind□     :                                       Indet □
    ind∘     : ∀ {d₁ d₂}    → Indet d₁ → Final d₂ → Indet (d₁ ∘ d₂)
    indCastG : ∀ {d τ}      → Ground τ → Indet d   → Indet (d ⟪ τ ⇛ □ ⟫)
    indCast  : ∀ {d τ₁ τ₂}  → Indet d              → Indet (d ⟪ τ₁ ⇛ τ₂ ⟫)
    indFail  : ∀ {d τ₁ τ₂}  → Final d
              → Ground τ₁ → Ground τ₂              → Indet (d ⟪ τ₁ ⇛⊥ τ₂ ⟫)

  data Final : IntExp → Set where
    fboxed : ∀ {d}  → BoxedVal d  → Final d
    findet : ∀ {d}  → Indet d     → Final d
