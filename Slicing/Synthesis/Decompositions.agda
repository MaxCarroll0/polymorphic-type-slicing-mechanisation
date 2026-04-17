open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; subst; cong; cong₂)
open import Core
open import Core.Typ.Properties using (⊔t-zeroₗ; ⊔t-zeroᵣ; ⊔-×-⊑; ⊔□×□)
open import Data.Empty using (⊥-elim)
open import Semantics.Statics
open import Semantics.Graduality using (static-gradual-syn; syn-precision)
open import Slicing.Synthesis.Synthesis

module Slicing.Synthesis.Decompositions where

-- MIN SLICE DECOMPOSITIONS
_×ₛ_ : ∀ {τ₁ τ₂ : Typ} → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ₁ × τ₂ ⌋
s₁ ×ₛ s₂ = (s₁ .↓ × s₂ .↓) isSlice ⊑× (s₁ .proof) (s₂ .proof)

_&ₛ_ : ∀ {e₁ e₂ : Exp} → ⌊ e₁ ⌋ → ⌊ e₂ ⌋ → ⌊ e₁ & e₂ ⌋
s₁ &ₛ s₂ = (s₁ .↓ & s₂ .↓) isSlice ⊑& (s₁ .proof) (s₂ .proof)

-- Pair construction: given m₁ : D₁ ◂ υ₁ and m₂ : D₂ ◂ υ₂, form
-- a slice of ↦& D₁ D₂ ◂ (υ₁ ×ₛ υ₂) by joining assumptions (γ₁ ⊔ γ₂)
-- and re-deriving both components under the shared context.
--   γₛ⊔ = γₛ₁ ⊔ₛ γₛ₂ ⊑ Γ   (join closure)
--   dᵢ' : γ⊔ ⊢ σᵢ ↦ ϕᵢ'    (static gradual guarantee)
--   υᵢ ⊑ ϕᵢ ⊑ ϕᵢ'          (valid of dᵢ + syn-precision)
_&syn_   : ∀ {n Γ e₁ e₂ τ₁ τ₂} {D₁ : n ； Γ ⊢ e₁ ↦ τ₁}
             {D₂ : n ； Γ ⊢ e₂ ↦ τ₂} {υ₁ υ₂}
           → SynSlice D₁ ◂ υ₁ → SynSlice D₂ ◂ υ₂
           → SynSlice (↦& D₁ D₂) ◂ (υ₁ ×ₛ υ₂)
_&syn_ {D₁ = D₁} {D₂ = D₂}
       (ρₛ₁ ⇑ ϕ₁ ∈ d₁ ⊒ υ₁⊑ϕ₁) (ρₛ₂ ⇑ ϕ₂ ∈ d₂ ⊒ υ₂⊑ϕ₂)
  with static-gradual-syn (γₛ⊔ .proof) (sndₛ ρₛ₁ .proof) D₁
     | static-gradual-syn (γₛ⊔ .proof) (sndₛ ρₛ₂ .proof) D₂
  where γₛ⊔ = fstₛ ρₛ₁ ⊔ₛ fstₛ ρₛ₂
... | ϕ₁' , d₁' , ϕ₁'⊑τ₁ | ϕ₂' , d₂' , ϕ₂'⊑τ₂
  = (γₛ⊔ ,ₛ (σₛ₁ &ₛ σₛ₂)) ⇑ (↑ ϕ₁'⊑τ₁) ×ₛ (↑ ϕ₂'⊑τ₂)
    ∈ ↦& d₁' d₂' ⊒ ⊑× υ₁⊑ϕ₁' υ₂⊑ϕ₂'
  where
    γₛ⊔ = fstₛ ρₛ₁ ⊔ₛ fstₛ ρₛ₂
    σₛ₁ = sndₛ ρₛ₁
    σₛ₂ = sndₛ ρₛ₂
    open ⊑ {A = Typ} using () renaming (trans to ⊑t-trans)
    open ⊑ {A = Exp} using () renaming (refl to ⊑e-refl)
    υ₁⊑ϕ₁' = ⊑t-trans υ₁⊑ϕ₁
              (syn-precision (⊑ₛLat.x⊑ₛx⊔ₛy (fstₛ ρₛ₁) (fstₛ ρₛ₂))
                             ⊑e-refl d₁' d₁)
    υ₂⊑ϕ₂' = ⊑t-trans υ₂⊑ϕ₂
              (syn-precision (⊑ₛLat.y⊑ₛx⊔ₛy (fstₛ ρₛ₁) (fstₛ ρₛ₂))
                             ⊑e-refl d₂' d₂)

-- Minimal product slices decompose into minimal component slices.
min-prod-decomposability
  : ∀ {n Γ e₁ e₂ τ₁ τ₂}
      {D₁ : n ； Γ ⊢ e₁ ↦ τ₁} {D₂ : n ； Γ ⊢ e₂ ↦ τ₂}
      {υ₁ : ⌊ τ₁ ⌋} {υ₂ : ⌊ τ₂ ⌋}
      ((m× , _) : MinSynSlice (↦& D₁ D₂) ◂ (υ₁ ×ₛ υ₂))
    → Σ[ (m₁ , _) ∈ MinSynSlice D₁ ◂ υ₁ ]
      Σ[ (m₂ , _) ∈ MinSynSlice D₂ ◂ υ₂ ]
         m× ≈ m₁ &syn m₂
min-prod-decomposability (m× , min)
  with m× .valid | m× ↓σ | m× ↓σ⊑ | m× ↓ϕ⊑ | m× .syn
...  | ⊑× υ₁⊑ϕ₁ υ₂⊑ϕ₂ | σ₁ & σ₂ | ⊑& σ₁⊑e₁ σ₂⊑e₂ | ⊑× ϕ₁⊑τ₁ ϕ₂⊑τ₂ | ↦& d₁ d₂
  = let s₁ = ((m× ↓γₛ) ,ₛ (σ₁ isSlice σ₁⊑e₁)) ⇑ ↑ ϕ₁⊑τ₁ ∈ d₁ ⊒ υ₁⊑ϕ₁
        s₂ = ((m× ↓γₛ) ,ₛ (σ₂ isSlice σ₂⊑e₂)) ⇑ ↑ ϕ₂⊑τ₂ ∈ d₂ ⊒ υ₂⊑ϕ₂
        m₁ , (γ₁⊑γ , σ₁'⊑σ₁) = minExists s₁
        m₂ , (γ₂⊑γ , σ₂'⊑σ₂) = minExists s₂
    in m₁ , m₂
     , min ((m₁ ↓s) &syn (m₂ ↓s))
           (HasJoin.closure assms-join γ₁⊑γ γ₂⊑γ , ⊑& σ₁'⊑σ₁ σ₂'⊑σ₂)

π₁ₛ : ∀ {e : Exp} → ⌊ e ⌋ → ⌊ π₁ e ⌋
π₁ₛ (σ isSlice σ⊑e) = (π₁ σ) isSlice (⊑π₁ σ⊑e)

π₁syn : ∀ {n Γ e τ₁ τ₂} {D : n ； Γ ⊢ e ↦ τ₁ × τ₂}
          {υ₁ : ⌊ τ₁ ⌋} {υ₂ : ⌊ τ₂ ⌋}
        → SynSlice D ◂ (υ₁ ×ₛ υ₂)
        → SynSlice (↦π₁ {τ₂ = τ₂} D ⊔□×□) ◂ υ₁
π₁syn {τ₁ = τ₁} {τ₂ = τ₂} {D = D} s
  with s .valid | s ↓ϕ⊑ | s .syn
... | ⊑× υ₁⊑ϕ₁ _ | ⊑× {τ₁ = ϕ₁} {τ₂ = ϕ₂} ϕ₁⊑τ₁ ϕ₂⊑τ₂ | d
  = (fstₛ (s ↓ρₛ) ,ₛ π₁ₛ (sndₛ (s ↓ρₛ))) ⇑ ↑ ϕ₁⊑τ₁ ∈ ↦π₁ d (⊔□×□ {ϕ₁} {ϕ₂}) ⊒ υ₁⊑ϕ₁

π₁syn-↓ρ : ∀ {n Γ e τ₁ τ₂} {D : n ； Γ ⊢ e ↦ τ₁ × τ₂}
              {υ₁ : ⌊ τ₁ ⌋} {υ₂ : ⌊ τ₂ ⌋}
              (s : SynSlice D ◂ (υ₁ ×ₛ υ₂))
            → (π₁syn s) ↓ρ ≡ (s ↓γ , π₁ (s ↓σ))
π₁syn-↓ρ {τ₁ = τ₁} {τ₂ = τ₂} s
  with s .valid | s ↓ϕ⊑ | s .syn
... | ⊑× _ _ | ⊑× {τ₁ = ϕ₁} {τ₂ = ϕ₂} _ _ | d = refl

-- Projection decomposability: a minimal slice of ↦π₁ D ◂ υ (for υ ≢ □)
-- decomposes into a minimal slice of D ◂ (υ ×ₛ ⊥ₛ).
-- Case □: impossible with υ ≢ □.
-- Case ↦π₁ s x: invert to get sub-derivation s on e, build
-- s× : SynSlice D ◂ (υ ×ₛ ⊥ₛ) from s, then show use minimality on π₁
min-π₁-decomposability
  : ∀ {n Γ e τ₁ τ₂} {D : n ； Γ ⊢ e ↦ τ₁ × τ₂}
      {υ : ⌊ τ₁ ⌋}
    → υ .↓ ≢ □
    → ((mπ₁ , _) : MinSynSlice (↦π₁ D ⊔□×□) ◂ υ)
    → Σ[ (m× , _) ∈ MinSynSlice D ◂ (υ ×ₛ ⊥ₛ) ]
        mπ₁ ≈ π₁syn m×
min-π₁-decomposability {τ₁ = τ₁} {τ₂ = τ₂} {D = D} υ≢□ (mπ₁ , min)
  with mπ₁ .syn  | mπ₁ .valid | mπ₁ .type | mπ₁ ↓σ⊑
... | ↦□ | ⊑□ | _ | _ = ⊥-elim (υ≢□ refl)
... | ↦π₁ {τ = ϕ'} s x | υ⊑ϕ₁ | ϕ₁ isSlice ϕ₁⊑τ₁ | ⊑π₁ σ'⊑e
  with syn-precision (mπ₁ ↓γ⊑) σ'⊑e D s
... | ⊑× {τ₁ = ϕ₁'} {τ₂ = ϕ₂'} ϕ₁'⊑τ₁ ϕ₂'⊑τ₂
  rewrite ⊔t-zeroᵣ {ϕ₁'} | ⊔t-zeroᵣ {ϕ₂'} with refl ← x
  = (m× , min×) , min (π₁syn m×) π₁m×⊑mπ₁
  where
    s× = ((mπ₁ ↓γₛ) ,ₛ (↑ σ'⊑e))
           ⇑ (↑ ϕ₁'⊑τ₁) ×ₛ (↑ ϕ₂'⊑τ₂) ∈ s ⊒ ⊑× υ⊑ϕ₁ ⊑□
    m× = minExists s× .proj₁ .proj₁
    min× = minExists s× .proj₁ .proj₂
    π₁m×⊑mπ₁ : (π₁syn m×) ↓ρ ⊑ mπ₁ ↓ρ
    π₁m×⊑mπ₁ rewrite π₁syn-↓ρ m×
      = minExists s× .proj₂ .proj₁ , ⊑π₁ (minExists s× .proj₂ .proj₂)
... | ⊑□ rewrite ⊔t-zeroₗ {□ × □} with refl ← x with ⊑□ ← υ⊑ϕ₁ = ⊥-elim (υ≢□ refl)

π₂ₛ : ∀ {e : Exp} → ⌊ e ⌋ → ⌊ π₂ e ⌋
π₂ₛ (σ isSlice σ⊑e) = (π₂ σ) isSlice (⊑π₂ σ⊑e)

π₂syn : ∀ {n Γ e τ₁ τ₂} {D : n ； Γ ⊢ e ↦ τ₁ × τ₂}
          {υ₁ : ⌊ τ₁ ⌋} {υ₂ : ⌊ τ₂ ⌋}
        → SynSlice D ◂ (υ₁ ×ₛ υ₂)
        → SynSlice (↦π₂ {τ₁ = τ₁} D ⊔□×□) ◂ υ₂
π₂syn {τ₁ = τ₁} {τ₂ = τ₂} {D = D} s
  with s .valid | s ↓ϕ⊑ | s .syn
... | ⊑× _ υ₂⊑ϕ₂ | ⊑× {τ₁ = ϕ₁} {τ₂ = ϕ₂} ϕ₁⊑τ₁ ϕ₂⊑τ₂ | d
  = (fstₛ (s ↓ρₛ) ,ₛ π₂ₛ (sndₛ (s ↓ρₛ))) ⇑ ↑ ϕ₂⊑τ₂ ∈ ↦π₂ d (⊔□×□ {ϕ₁} {ϕ₂}) ⊒ υ₂⊑ϕ₂

π₂syn-↓ρ : ∀ {n Γ e τ₁ τ₂} {D : n ； Γ ⊢ e ↦ τ₁ × τ₂}
              {υ₁ : ⌊ τ₁ ⌋} {υ₂ : ⌊ τ₂ ⌋}
              (s : SynSlice D ◂ (υ₁ ×ₛ υ₂))
            → (π₂syn s) ↓ρ ≡ (s ↓γ , π₂ (s ↓σ))
π₂syn-↓ρ {τ₁ = τ₁} {τ₂ = τ₂} s
  with s .valid | s ↓ϕ⊑ | s .syn
... | ⊑× _ _ | ⊑× {τ₁ = ϕ₁} {τ₂ = ϕ₂} _ _ | d = refl

min-π₂-decomposability
  : ∀ {n Γ e τ₁ τ₂} {D : n ； Γ ⊢ e ↦ τ₁ × τ₂}
      {υ : ⌊ τ₂ ⌋}
    → υ .↓ ≢ □
    → ((mπ₂ , _) : MinSynSlice (↦π₂ D ⊔□×□) ◂ υ)
    → Σ[ (m× , _) ∈ MinSynSlice D ◂ (⊥ₛ ×ₛ υ) ]
        mπ₂ ≈ π₂syn m×
min-π₂-decomposability {τ₁ = τ₁} {τ₂ = τ₂} {D = D} υ≢□ (mπ₂ , min)
  with mπ₂ .syn  | mπ₂ .valid | mπ₂ .type | mπ₂ ↓σ⊑
... | ↦□ | ⊑□ | _ | _ = ⊥-elim (υ≢□ refl)
... | ↦π₂ {τ = ϕ'} s x | υ⊑ϕ₂ | ϕ₂ isSlice ϕ₂⊑τ₂ | ⊑π₂ σ'⊑e
  with syn-precision (mπ₂ ↓γ⊑) σ'⊑e D s
... | ⊑× {τ₁ = ϕ₁'} {τ₂ = ϕ₂'} ϕ₁'⊑τ₁ ϕ₂'⊑τ₂
  rewrite ⊔t-zeroᵣ {ϕ₁'} | ⊔t-zeroᵣ {ϕ₂'} with refl ← x
  = (m× , min×) , min (π₂syn m×) π₂m×⊑mπ₂
  where
    s× = ((mπ₂ ↓γₛ) ,ₛ (↑ σ'⊑e))
           ⇑ (↑ ϕ₁'⊑τ₁) ×ₛ (↑ ϕ₂'⊑τ₂) ∈ s ⊒ ⊑× ⊑□ υ⊑ϕ₂
    m× = minExists s× .proj₁ ↓s
    min× = minimality (minExists s× .proj₁)
    π₂m×⊑mπ₂ : (π₂syn m×) ↓ρ ⊑ mπ₂ ↓ρ
    π₂m×⊑mπ₂ rewrite π₂syn-↓ρ m×
      = minExists s× .proj₂ .proj₁ , ⊑π₂ (minExists s× .proj₂ .proj₂)
... | ⊑□ rewrite ⊔t-zeroₗ {□ × □} with refl ← x with ⊑□ ← υ⊑ϕ₂ = ⊥-elim (υ≢□ refl)
