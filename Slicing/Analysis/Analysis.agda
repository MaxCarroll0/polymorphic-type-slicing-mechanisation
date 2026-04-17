open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsEquivalence; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core
open import Semantics.Statics

module Slicing.Analysis.Analysis where

-- Analysis slice: sliced context and assumptions that still enforce
-- analysis against a type slice υ. Indexed by a context classification
record AnaSlice {n : ℕ} {Γ₀ : Assms} {C : Ctx} {Γ : Assms} {τ : Typ} {p : Position}
                (_ : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]) (υ : ⌊ τ ⌋) : Set where
  field
    κ     : ⌊ C ⌋
    γ     : ⌊ Γ₀ ⌋
    valid : ∃[ Γ' ] n ； γ .↓ ⊢ κ .↓ at p ▷ Γ' [ ⇐mode (υ .↓) ]
open AnaSlice public

private
-- Precision polymorphic in υ
  _⊑ana_ : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ₁ υ₂} →
             AnaSlice Cls υ₁ → AnaSlice Cls υ₂ → Set
  _⊑ana_ s₁ s₂ =
      s₁ .κ ⊑ₛ s₂ .κ
    ∧ s₁ .γ ⊑ₛ s₂ .γ

  _≈ana_ : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ₁ υ₂} →
              AnaSlice Cls υ₁ → AnaSlice Cls υ₂ → Set
  _≈ana_ s₁ s₂ =
      s₁ .κ ≈ₛ s₂ .κ
    ∧ s₁ .γ ≈ₛ s₂ .γ

  _≈ana?_ : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ}
            → (s₁ s₂ : AnaSlice Cls υ) → Relation.Nullary.Dec (s₁ ≈ana s₂)
  s₁ ≈ana? s₂ with s₁ .κ ≈ₛ? s₂ .κ | s₁ .γ ≈ₛ? s₂ .γ
  ...            | yes p          | yes q = yes (p , q)
  ...            | no ¬p          | _     = no λ where (p , _) → ¬p p
  ...            | _              | no ¬q = no λ where (_ , q) → ¬q q

  _⊑ana?_ : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ}
            → (s₁ s₂ : AnaSlice Cls υ) → Relation.Nullary.Dec (s₁ ⊑ana s₂)
  s₁ ⊑ana? s₂ with s₁ .κ ⊑ₛ? s₂ .κ | s₁ .γ ⊑ₛ? s₂ .γ
  ...            | yes p          | yes q = yes (p , q)
  ...            | no ¬p          | _     = no λ where (p , _) → ¬p p
  ...            | _              | no ¬q = no λ where (_ , q) → ¬q q

  ⊑ana-isDecPartialOrder : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ} →
                              IsDecPartialOrder (_≈ana_ {Cls = Cls} {υ₁ = υ} {υ₂ = υ}) _⊑ana_
  ⊑ana-isDecPartialOrder = record
                           { isPartialOrder = record
                                              { isPreorder = isPreorder
                                              ; antisym = λ (p₁ , q₁) (p₂ , q₂) → ⊑.antisym {Ctx} p₁ p₂ , ⊑.antisym {Assms} q₁ q₂
                                              }
                           ; _≟_  = _≈ana?_
                           ; _≤?_ = _⊑ana?_
                           }
    where isPreorder = record
                       { isEquivalence = record
                           { refl  = λ {_} → refl , refl
                           ; sym   = λ where (refl , refl) → refl , refl
                           ; trans = λ where (refl , refl) (refl , refl) → refl , refl
                           }
                       ; reflexive  = λ where (refl , refl) → ⊑.refl {Ctx} , ⊑.refl {Assms}
                       ; trans = λ (p₁ , q₁) (p₂ , q₂) → ⊑.trans {Ctx} p₁ p₂ , ⊑.trans {Assms} q₁ q₂
                       }

instance
  anaSlice-precision : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ} →
                         HasPrecision (AnaSlice Cls υ)
  anaSlice-precision = record
    { _≈_               = _≈ana_
    ; _⊑_               = _⊑ana_
    ; isDecPartialOrder = ⊑ana-isDecPartialOrder
    }

postulate
  ⊥-ana-valid : ∀ {n Γ₀ C Γ τ p} (Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ])
              → ∃[ Γ' ] n ； (⊥ₛ {a = Γ₀}) .↓ ⊢ (⊥ₛ {a = C}) .↓ at p ▷ Γ' [ ⇐mode ((⊥ₛ {a = τ}) .↓) ]

⊥-ana : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} → AnaSlice Cls ⊥ₛ
⊥-ana {Cls = Cls} = record { κ = ⊥ₛ ; γ = ⊥ₛ ; valid = ⊥-ana-valid Cls }

⊤-ana : ∀ {n Γ₀ C Γ τ p} (Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]) → AnaSlice Cls ⊤ₛ
⊤-ana Cls = record { κ = ⊤ₛ ; γ = ⊤ₛ ; valid = _ , Cls }

-- Minimality
IsMinimal : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ} → AnaSlice Cls υ → Set
IsMinimal {Cls = Cls} {υ = υ} s = ∀ (s' : AnaSlice Cls υ) → s' ⊑ana s → s ⊑ana s'

MinAnaSlice : ∀ {n Γ₀ C Γ τ p} → (Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]) → ⌊ τ ⌋ → Set
MinAnaSlice Cls υ = Σ[ s ∈ AnaSlice Cls υ ] IsMinimal s

-- Join closure (of minimal analysis slices)
private
  postulate
    ⊔ana-valid : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ}
                 → (s₁ s₂ : AnaSlice Cls υ)
                 → IsMinimal s₁ → IsMinimal s₂
                 → ∃[ Γ' ] n ； (AnaSlice.γ s₁ ⊔ₛ AnaSlice.γ s₂) .↓
                              ⊢ (AnaSlice.κ s₁ ⊔ₛ AnaSlice.κ s₂) .↓ at p ▷ Γ' [ ⇐mode (υ .↓) ]

  _⊔ana_ : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ} →
             (s₁ s₂ : AnaSlice Cls υ) → IsMinimal s₁ → IsMinimal s₂ → AnaSlice Cls υ
  (s₁ ⊔ana s₂) m₁ m₂ = record
    { κ = AnaSlice.κ s₁ ⊔ₛ AnaSlice.κ s₂
    ; γ = AnaSlice.γ s₁ ⊔ₛ AnaSlice.γ s₂
    ; valid = ⊔ana-valid s₁ s₂ m₁ m₂
    }

⊔ana-ub₁ : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ}
            → (s₁ s₂ : AnaSlice Cls υ) → (m₁ : IsMinimal s₁) → (m₂ : IsMinimal s₂)
            → s₁ ⊑ana ((s₁ ⊔ana s₂) m₁ m₂)
⊔ana-ub₁ s₁ s₂ _ _ = ⊑ₛLat.x⊑ₛx⊔ₛy (AnaSlice.κ s₁) (AnaSlice.κ s₂)
                     , ⊑ₛLat.x⊑ₛx⊔ₛy (AnaSlice.γ s₁) (AnaSlice.γ s₂)

⊔ana-ub₂ : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ}
            → (s₁ s₂ : AnaSlice Cls υ) → (m₁ : IsMinimal s₁) → (m₂ : IsMinimal s₂)
            → s₂ ⊑ana ((s₁ ⊔ana s₂) m₁ m₂)
⊔ana-ub₂ s₁ s₂ _ _ = ⊑ₛLat.y⊑ₛx⊔ₛy (AnaSlice.κ s₁) (AnaSlice.κ s₂)
                     , ⊑ₛLat.y⊑ₛx⊔ₛy (AnaSlice.γ s₁) (AnaSlice.γ s₂)

⊔ana-lub : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ}
            → {s : AnaSlice Cls υ} (s₁ s₂ : AnaSlice Cls υ)
            → (m₁ : IsMinimal s₁) → (m₂ : IsMinimal s₂)
            → s₁ ⊑ana s → s₂ ⊑ana s
            → ((s₁ ⊔ana s₂) m₁ m₂) ⊑ana s
⊔ana-lub {Γ₀ = Γ₀} {C = C} {s = s} s₁ s₂ _ _ (p₁ , q₁) (p₂ , q₂) =
    ⊑ₛLat.⊔ₛ-least {A = Ctx} {a = C}
      {x = AnaSlice.κ s₁} {y = AnaSlice.κ s₂} {z = AnaSlice.κ s}
      p₁ p₂
  , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀}
      {x = AnaSlice.γ s₁} {y = AnaSlice.γ s₂} {z = AnaSlice.γ s}
      q₁ q₂

-- Every checking context has a minimal AnaSlice
postulate
  minExists : ∀ {n Γ₀ C Γ τ p} (Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]) υ
             → ∃[ m ] IsMinimal {Cls = Cls} {υ = υ} m

-- Monotonicity: more precise type slice → more precise minimal slice
postulate
  mono : ∀ {n Γ₀ C Γ τ p} {Cls : n ； Γ₀ ⊢ C at p ▷ Γ [ ⇐mode τ ]} {υ₁ υ₂ : ⌊ τ ⌋}
         → υ₁ ⊑ₛ υ₂
         → (m₂ : AnaSlice Cls υ₂) → IsMinimal m₂
         → Σ[ m₁ ∈ AnaSlice Cls υ₁ ] IsMinimal m₁ ∧ m₁ ⊑ana m₂
