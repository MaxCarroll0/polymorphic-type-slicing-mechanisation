open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsEquivalence; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe using (just)
open import Data.List using (_∷_; [])
open import Core
open import Semantics.Statics

module Slicing.Synthesis where

-- Synthesis slice: sliced assumptions and expression that still synthesize
-- a given type slice υ. Indexed by the original derivation D.
record SynSlice {n : ℕ} {Γ : Assms} {e : Exp} {τ : Typ}
                (D : n ； Γ ⊢ e ↦ τ) (υ : ⌊ τ ⌋) : Set where
  field
    γ     : ⌊ Γ ⌋
    σ     : ⌊ e ⌋
    valid : n ； γ .↓ ⊢ σ .↓ ↦ υ .↓
open SynSlice public

private
-- Precision polymorphic in υ
  _⊑syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂} →
             SynSlice D υ₁ → SynSlice D υ₂ → Set
  _⊑syn_ s₁ s₂ =
      s₁ .σ ⊑ₛ s₂ .σ
    ∧ s₁ .γ ⊑ₛ s₂ .γ

  _≈syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂} →
              SynSlice D υ₁ → SynSlice D υ₂ → Set
  _≈syn_ s₁ s₂ =
      s₁ .σ ≈ₛ s₂ .σ
    ∧ s₁ .γ ≈ₛ s₂ .γ

  _≈syn?_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → (s₁ s₂ : SynSlice D υ) → Relation.Nullary.Dec (s₁ ≈syn s₂)
  s₁ ≈syn? s₂ with s₁ .σ ≈ₛ? s₂ .σ | s₁ .γ ≈ₛ? s₂ .γ
  ...            | yes p          | yes q = yes (p , q)
  ...            | no ¬p          | _     = no λ where (p , _) → ¬p p
  ...            | _              | no ¬q = no λ where (_ , q) → ¬q q

  _⊑syn?_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → (s₁ s₂ : SynSlice D υ) → Relation.Nullary.Dec (s₁ ⊑syn s₂)
  s₁ ⊑syn? s₂ with s₁ .σ ⊑ₛ? s₂ .σ | s₁ .γ ⊑ₛ? s₂ .γ
  ...            | yes p          | yes q = yes (p , q)
  ...            | no ¬p          | _     = no λ where (p , _) → ¬p p
  ...            | _              | no ¬q = no λ where (_ , q) → ¬q q

  ⊑syn-isDecPartialOrder : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
                              IsDecPartialOrder (_≈syn_ {D = D} {υ₁ = υ} {υ₂ = υ}) _⊑syn_
  ⊑syn-isDecPartialOrder {Γ = Γ} {e = e} = record
                           { isPartialOrder = record
                                              { isPreorder = isPreorder
                                              ; antisym = λ (p₁ , q₁) (p₂ , q₂) → ⊑.antisym {Exp} p₁ p₂ , ⊑.antisym {Assms} q₁ q₂
                                              }
                           ; _≟_  = _≈syn?_
                           ; _≤?_ = _⊑syn?_ 
                           }
    where isPreorder = record
                       { isEquivalence = record
                           { refl  = λ {_} → refl , refl
                           ; sym   = λ where (refl , refl) → refl , refl
                           ; trans = λ where (refl , refl) (refl , refl) → refl , refl
                           }
                       ; reflexive  = λ where (refl , refl) → ⊑.refl {Exp} , ⊑.refl {Assms}
                       ; trans = λ (p₁ , q₁) (p₂ , q₂) → ⊑.trans {Exp} p₁ p₂ , ⊑.trans {Assms} q₁ q₂
                       }

instance
  synSlice-precision : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
                         HasPrecision (SynSlice D υ)
  synSlice-precision = record
    { _≈_               = _≈syn_
    ; _⊑_               = _⊑syn_
    ; isDecPartialOrder = ⊑syn-isDecPartialOrder
    }

⊥-syn : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} → SynSlice D ⊥ₛ
⊥-syn = record { γ = ⊥ₛ ; σ = ⊥ₛ ; valid = ↦□ }

⊤-syn : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) → SynSlice D ⊤ₛ
⊤-syn D = record { γ = ⊤ₛ ; σ = ⊤ₛ ; valid = D }

-- Minimality
IsMinimal : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} → SynSlice D υ → Set
IsMinimal {D = D} {υ = υ} s = ∀ (s' : SynSlice D υ) → s' ⊑syn s → s ⊑syn s'

MinSynSlice : ∀ {n Γ e τ} → (D : n ； Γ ⊢ e ↦ τ) → ⌊ τ ⌋ → Set
MinSynSlice D υ = Σ[ s ∈ SynSlice D υ ] IsMinimal s

-- Join closure (of minimal syn slices)
-- Without IsMinimal, ⊔syn-valid is false: ↦□ allows arbitrary assumptions γ,
-- so joining pollutes the assumptions, i.e.
module ⊔-closure-counterexample where
  D' : 0 ； * ∷ [] ⊢ ⟨ 0 ⟩ ↦ *
  D' = ↦Var refl

  υ' : ⌊ Typ.* ⌋
  υ' = ⊥ₛ

  s₁' : SynSlice D' υ'
  s₁' = record { γ = ⊤ₛ ; σ = ⊥ₛ ; valid = ↦□ }

  s₂' : SynSlice D' υ'
  s₂' = record { γ = ⊥ₛ ; σ = ⊤ₛ ; valid = ↦Var refl }

  ¬⊔-valid : ¬ (0 ； (s₁' .γ ⊔ₛ s₂' .γ) .↓ ⊢ (s₁' .σ ⊔ₛ s₂' .σ) .↓ ↦ υ' .↓)
  ¬⊔-valid (↦Var ())

private
  postulate
    ⊔syn-valid : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
                 → (s₁ s₂ : SynSlice D υ)
                 → IsMinimal s₁ → IsMinimal s₂
                 → n ； (SynSlice.γ s₁ ⊔ₛ SynSlice.γ s₂) .↓
                     ⊢ (SynSlice.σ s₁ ⊔ₛ SynSlice.σ s₂) .↓ ↦ υ .↓

  _⊔syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
             (s₁ s₂ : SynSlice D υ) → IsMinimal s₁ → IsMinimal s₂ → SynSlice D υ
  (s₁ ⊔syn s₂) m₁ m₂ = record
    { γ = SynSlice.γ s₁ ⊔ₛ SynSlice.γ s₂
    ; σ = SynSlice.σ s₁ ⊔ₛ SynSlice.σ s₂
    ; valid = ⊔syn-valid s₁ s₂ m₁ m₂
    }

⊔syn-ub₁ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → (s₁ s₂ : SynSlice D υ) → (m₁ : IsMinimal s₁) → (m₂ : IsMinimal s₂)
            → s₁ ⊑syn ((s₁ ⊔syn s₂) m₁ m₂)
⊔syn-ub₁ s₁ s₂ _ _ = ⊑ₛLat.x⊑ₛx⊔ₛy (SynSlice.σ s₁) (SynSlice.σ s₂)
                     , ⊑ₛLat.x⊑ₛx⊔ₛy (SynSlice.γ s₁) (SynSlice.γ s₂)

⊔syn-ub₂ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → (s₁ s₂ : SynSlice D υ) → (m₁ : IsMinimal s₁) → (m₂ : IsMinimal s₂)
            → s₂ ⊑syn ((s₁ ⊔syn s₂) m₁ m₂)
⊔syn-ub₂ s₁ s₂ _ _ = ⊑ₛLat.y⊑ₛx⊔ₛy (SynSlice.σ s₁) (SynSlice.σ s₂)
                     , ⊑ₛLat.y⊑ₛx⊔ₛy (SynSlice.γ s₁) (SynSlice.γ s₂)

⊔syn-lub : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → {s : SynSlice D υ} (s₁ s₂ : SynSlice D υ)
            → (m₁ : IsMinimal s₁) → (m₂ : IsMinimal s₂)
            → s₁ ⊑syn s → s₂ ⊑syn s
            → ((s₁ ⊔syn s₂) m₁ m₂) ⊑syn s
⊔syn-lub {Γ = Γ} {e = e} {s = s} s₁ s₂ _ _ (p₁ , q₁) (p₂ , q₂) =
    ⊑ₛLat.⊔ₛ-least {A = Exp} {a = e}
      {x = SynSlice.σ s₁} {y = SynSlice.σ s₂} {z = SynSlice.σ s}
      p₁ p₂
  , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ}
      {x = SynSlice.γ s₁} {y = SynSlice.γ s₂} {z = SynSlice.γ s}
      q₁ q₂

-- Every derivation and type slice has a minimal SynSlice
-- TODO: Prove via classical methods using the fact that a bottom element exists
postulate
  minExists : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) υ
             → ∃[ m ] IsMinimal {D = D} {υ = υ} m

-- Monotonicity: more precise type slice → more precise minimal slice
postulate
  mono : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂ : ⌊ τ ⌋}
         → υ₁ ⊑ₛ υ₂
         → (m₂ : SynSlice D υ₂) → IsMinimal m₂
         → Σ[ m₁ ∈ SynSlice D υ₁ ] IsMinimal m₁ ∧ m₁ ⊑syn m₂
