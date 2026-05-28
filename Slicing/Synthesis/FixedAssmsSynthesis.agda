open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; subst)
import Relation.Binary.Construct.On as On
open import Induction.WellFounded using (WellFounded; Acc; acc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_on_)
open import Core
open import Semantics.Statics
open import Semantics.Graduality using (static-gradual-syn; syn-precision)
open import Slicing.Synthesis.Synthesis using (IsMinimal)

-- Term-minimal slices: the SynSlice specialisation that holds the assumption context fixed.
-- Definitions 8.1, 8.2. Theorem 8.4 (existence)
-- Dissertation: §8.2 Term Slices, §8.3 Term-Minimality.
module Slicing.Synthesis.FixedAssmsSynthesis where

-- Fixed-context synthesis slice: full context, minimal expression
record FixedAssmsSynSlice {n : ℕ} {Γ : Assms} {e : Exp} {τ : Typ}
                    (D : n , Γ ⊢ e ⇑ τ) (υ : ⌊ τ ⌋) : Set where
  constructor _⇑_∈_⊒_
  field
    expₛ  : ⌊ e ⌋
    type  : ⌊ τ ⌋
    syn   : n , Γ ⊢ expₛ .↓ ⇑ type .↓
    valid : υ ⊑ₛ type

  ↓σ = expₛ .↓
  ↓σₛ = expₛ
  ↓σ⊑ = expₛ .proof

  ↓ϕ = type .↓
  ↓ϕₛ = type
  ↓ϕ⊑ = type .proof

  reindex : ∀ {υ'} → υ' ⊑ₛ type → FixedAssmsSynSlice D υ'
  reindex p = record { expₛ = expₛ; type = type; syn = syn; valid = p }

open FixedAssmsSynSlice public
  renaming ( ↓σ to _↓σ; ↓σₛ to _↓σₛ; ↓σ⊑ to _↓σ⊑
           ; ↓ϕ to _↓ϕ; ↓ϕₛ to _↓ϕₛ; ↓ϕ⊑ to _↓ϕ⊑)
infix 10 FixedAssmsSynSlice
infix 10 _⇑_∈_⊒_

instance
  fixedassms-syn-slice-precision : ∀ {n Γ e τ υ} {D : n , Γ ⊢ e ⇑ τ}
    → HasPrecision (FixedAssmsSynSlice D υ)
  fixedassms-syn-slice-precision = record
    { _≈_               = _≈_ on _↓σ
    ; _⊑_               = _⊑_ on _↓σ
    ; isDecPartialOrder = On.isDecPartialOrder _↓σ
        (HasPrecision.isDecPartialOrder exp-precision)
    }

⊥-fixedassms-syn : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ} → FixedAssmsSynSlice D ⊥ₛ
⊥-fixedassms-syn = ⊥ₛ ⇑ ⊥ₛ ∈ ⇑□ ⊒ ⊑□

⊤-fixedassms-syn : ∀ {n Γ e τ} (D : n , Γ ⊢ e ⇑ τ) → FixedAssmsSynSlice D ⊤ₛ
⊤-fixedassms-syn {τ = τ} D = (⊤ₛ ⇑ ⊤ₛ ∈ D ⊒ ⊑ₛ.refl {A = Typ} {x = ⊤ₛ {a = τ}})

MinFixedAssmsSynSlice : ∀ {n Γ e τ} → (D : n , Γ ⊢ e ⇑ τ) → ⌊ τ ⌋ → Set
MinFixedAssmsSynSlice D υ = Σ[ s ∈ FixedAssmsSynSlice D υ ] IsMinimal s

ExactFixedAssmsSynSlice : ∀ {n Γ e τ} (D : n , Γ ⊢ e ⇑ τ) (υ : ⌊ τ ⌋) → Set
ExactFixedAssmsSynSlice D υ = Σ[ s ∈ FixedAssmsSynSlice D υ ] s .type ⊑ₛ υ

open ⊑ {A = Assms} using () renaming (refl to ⊑a-refl)

static-gradual-syn-exp
  : ∀ {n Γ e τ} → (D : n , Γ ⊢ e ⇑ τ)
    → (σₛ : ⌊ e ⌋)
    → Σ[ ϕ ∈ ⌊ τ ⌋ ] n , Γ ⊢ σₛ .↓ ⇑ ϕ .↓
static-gradual-syn-exp {Γ = Γ} D σₛ
  with static-gradual-syn (⊑a-refl {x = Γ}) (σₛ .proof) D
...  | ϕt , (d , ϕt⊑τ) = ↑ ϕt⊑τ , d

syn-precision-exp
  : ∀ {n Γ e τ} (D : n , Γ ⊢ e ⇑ τ)
    → (σₛ : ⌊ e ⌋) → ∀ {υ}
    → _
    → υ ⊑ τ
syn-precision-exp {Γ = Γ} D σₛ
  = syn-precision (⊑a-refl {x = Γ}) (σₛ .proof) D

infixl 6 _⊔fixsyn_
_⊔fixsyn_ : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ} {υ₁ υ₂}
           → FixedAssmsSynSlice D υ₁ → FixedAssmsSynSlice D υ₂
           → FixedAssmsSynSlice D (υ₁ ⊔ₛ υ₂)
_⊔fixsyn_ {τ = τ} {D = D} {υ₁} {υ₂}
  (σₛ₁ ⇑ ϕ₁ ∈ d₁ ⊒ υ₁⊑ϕ₁) (σₛ₂ ⇑ ϕ₂ ∈ d₂ ⊒ υ₂⊑ϕ₂)
  with static-gradual-syn-exp D (σₛ₁ ⊔ₛ σₛ₂) in eq
...  | ϕ⊔ , d⊔ = σₛ₁ ⊔ₛ σₛ₂ ⇑ ϕ⊔ ∈ d⊔ ⊒ υ⊔⊑ϕ⊔
                 where open ⊑ₛ {a = τ}
                       open ⊑ₛLat {a = τ}
                       υ₁⊑ϕ⊔ = begin υ₁ ⊑⟨ υ₁⊑ϕ₁ ⟩
                                     ϕ₁ ⊑⟨ syn-precision-exp d⊔
                                           (↑ (⊑ₛLat.x⊑ₛx⊔ₛy σₛ₁ σₛ₂)) d₁ ⟩
                                     ϕ⊔ ∎
                       υ₂⊑ϕ⊔ = begin υ₂ ⊑⟨ υ₂⊑ϕ₂ ⟩
                                     ϕ₂ ⊑⟨ syn-precision-exp d⊔
                                           (↑ (⊑ₛLat.y⊑ₛx⊔ₛy σₛ₁ σₛ₂)) d₂ ⟩
                                     ϕ⊔ ∎
                       υ⊔⊑ϕ⊔ = ⊔ₛ-least {υ₁} {υ₂} {ϕ⊔}
                                        υ₁⊑ϕ⊔ υ₂⊑ϕ⊔


-- Well-foundedness of strict precision on FixedAssmsSynSlices (finite lattice)
private
  _⊏ᶠ_ : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ} {υ : ⌊ τ ⌋}
        → FixedAssmsSynSlice D υ → FixedAssmsSynSlice D υ → Set
  _⊏ᶠ_ = ⊑._⊏_ ⦃ fixedassms-syn-slice-precision ⦄

postulate
  ⊏-wf-fixedassms : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ} {υ : ⌊ τ ⌋}
    → WellFounded (_⊏ᶠ_ {D = D} {υ = υ})
  minimal?-fixedassms : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ} {υ : ⌊ τ ⌋}
    → (s : FixedAssmsSynSlice D υ)
    → IsMinimal s ⊎ (Σ[ s' ∈ FixedAssmsSynSlice D υ ] s' ⊏ᶠ s)

-- Every FixedAssmsSynSlice has a minimal element below it.
-- By well-founded recursion on strict expression precision.
minFixedAssmsExists
  : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ} {υ : ⌊ τ ⌋}
    (s : FixedAssmsSynSlice D υ)
    → Σ[ (m , _) ∈ MinFixedAssmsSynSlice D υ ]
         m ⊑ s
minFixedAssmsExists {D = D} {υ = υ} s = go s (⊏-wf-fixedassms s)
  where
  go : (s : FixedAssmsSynSlice D υ) → Acc _⊏ᶠ_ s
     → Σ[ (m , _) ∈ MinFixedAssmsSynSlice D υ ] m ⊑ s
  go s a with minimal?-fixedassms s
  go s _        | inj₁ min-s       = (s , min-s) , ⊑.refl {Exp}
  go s (acc rs) | inj₂ (s' , s'⊏s) =
    let ((m , min-m) , m⊑s') = go s' (rs s'⊏s)
    in (m , min-m) , ⊑.trans {Exp} m⊑s' (proj₁ s'⊏s)
