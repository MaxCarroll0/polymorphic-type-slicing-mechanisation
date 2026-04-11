module Semantics.Dynamics.Step where

open import Data.Nat using (ℕ; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Core.Typ using (Typ; □; _⇒_; _+_; _×_; ∀·)
open import Core.Typ.Substitution using ([_↦_]_)
open import Core.IntExp
open import Semantics.Dynamics.Ground
open import Semantics.Dynamics.Values

infix 3 _⟶_

-- TODO: Switch to contextual dynamics
data _⟶_ : IntExp → IntExp → Set where
  ITFun      : ∀ {τ d₁ d₂} →
                 Value d₂ →
                 (λ: τ ⇒ d₁) ∘ d₂ ⟶ [ d₂ ↦e zero ] d₁

  ITTLam     : ∀ {d σ} →
                 (Λ d) < σ > ⟶ [ σ ↦t zero ] d

  ITCastId   : ∀ {d τ} →
                 d ⟪ τ ⇛ τ ⟫ ⟶ d

  ITAppCast  : ∀ {d₁ d₂ τ₁ τ₂ τ₃ τ₄} →
                 (τ₁ ⇒ τ₂) ≢ (τ₃ ⇒ τ₄) →
                 Value d₂ →
                 (d₁ ⟪ τ₁ ⇒ τ₂ ⇛ τ₃ ⇒ τ₄ ⟫) ∘ d₂
                   ⟶ (d₁ ∘ (d₂ ⟪ τ₃ ⇛ τ₁ ⟫)) ⟪ τ₂ ⇛ τ₄ ⟫

  ITTApCast  : ∀ {d τ₁ τ₂ σ} →
                 (∀· τ₁) ≢ (∀· τ₂) →
                 (d ⟪ ∀· τ₁ ⇛ ∀· τ₂ ⟫) < σ >
                   ⟶ (d < σ >) ⟪ [ zero ↦ σ ] τ₁ ⇛ [ zero ↦ σ ] τ₂ ⟫

  ITGround   : ∀ {d τ g} →
                 BoxedVal d →
                 τ ▸g g →
                 d ⟪ τ ⇛ □ ⟫ ⟶ (d ⟪ τ ⇛ g ⟫) ⟪ g ⇛ □ ⟫

  ITExpand   : ∀ {d τ g} →
                 BoxedVal d →
                 τ ▸g g →
                 d ⟪ □ ⇛ τ ⟫ ⟶ (d ⟪ □ ⇛ g ⟫) ⟪ g ⇛ τ ⟫

  ITCastOK   : ∀ {d τ} →
                 Ground τ →
                 BoxedVal d →
                 (d ⟪ τ ⇛ □ ⟫) ⟪ □ ⇛ τ ⟫ ⟶ d

  ITCastFail : ∀ {d τ₁ τ₂} →
                 Ground τ₁ → Ground τ₂ →
                 τ₁ ≢ τ₂ →
                 BoxedVal d →
                 (d ⟪ τ₁ ⇛ □ ⟫) ⟪ □ ⇛ τ₂ ⟫ ⟶ d ⟪ τ₁ ⇛⊥ τ₂ ⟫

  cong∘₁     : ∀ {d₁ d₁' d₂} →
                 d₁ ⟶ d₁' →
                 d₁ ∘ d₂ ⟶ d₁' ∘ d₂

  cong∘₂     : ∀ {d₁ d₂ d₂'} →
                 Final d₁ →
                 d₂ ⟶ d₂' →
                 d₁ ∘ d₂ ⟶ d₁ ∘ d₂'

  congCast   : ∀ {d d' τ₁ τ₂} →
                 d ⟶ d' →
                 d ⟪ τ₁ ⇛ τ₂ ⟫ ⟶ d' ⟪ τ₁ ⇛ τ₂ ⟫

  cong<>     : ∀ {d d' σ} →
                 d ⟶ d' →
                 d < σ > ⟶ d' < σ >

  cong&₁     : ∀ {d₁ d₁' d₂} →
                 d₁ ⟶ d₁' →
                 d₁ & d₂ ⟶ d₁' & d₂

  cong&₂     : ∀ {d₁ d₂ d₂'} →
                 Final d₁ →
                 d₂ ⟶ d₂' →
                 d₁ & d₂ ⟶ d₁ & d₂'

  congπ₁     : ∀ {d d'} →
                 d ⟶ d' →
                 π₁ d ⟶ π₁ d'

  congπ₂     : ∀ {d d'} →
                 d ⟶ d' →
                 π₂ d ⟶ π₂ d'

  congι₁     : ∀ {d d'} →
                 d ⟶ d' →
                 ι₁ d ⟶ ι₁ d'

  congι₂     : ∀ {d d'} →
                 d ⟶ d' →
                 ι₂ d ⟶ ι₂ d'

  congCase   : ∀ {d d' d₁ d₂} →
                 d ⟶ d' →
                 case d of d₁ · d₂ ⟶ case d' of d₁ · d₂

  congDef    : ∀ {d₁ d₁' d₂} →
                 d₁ ⟶ d₁' →
                 def d₁ ⊢ d₂ ⟶ def d₁' ⊢ d₂

  ITπ₁       : ∀ {d₁ d₂} →
                 Value d₁ → Value d₂ →
                 π₁ (d₁ & d₂) ⟶ d₁

  ITπ₂       : ∀ {d₁ d₂} →
                 Value d₁ → Value d₂ →
                 π₂ (d₁ & d₂) ⟶ d₂

  ITCase₁    : ∀ {d d₁ d₂} →
                 Value d →
                 case (ι₁ d) of d₁ · d₂ ⟶ [ d ↦e zero ] d₁

  ITCase₂    : ∀ {d d₁ d₂} →
                 Value d →
                 case (ι₂ d) of d₁ · d₂ ⟶ [ d ↦e zero ] d₂

  ITDef      : ∀ {d₁ d₂} →
                 Value d₁ →
                 def d₁ ⊢ d₂ ⟶ [ d₁ ↦e zero ] d₂
