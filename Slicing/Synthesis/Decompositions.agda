open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; subst; cong; cong₂)
open import Core
open import Core.Typ.Base using (diag; kind□; kind⇒; kind×; kind+; kind∀; diff)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.Unit using (⊤; tt)
open import Semantics.Statics
open import Semantics.Graduality using (static-gradual-syn; syn-precision; static-gradual-ana)
open import Slicing.Synthesis.Synthesis

module Slicing.Synthesis.Decompositions where

open ⊑ {A = Typ} using () renaming (refl to ⊑t-refl; trans to ⊑t-trans)
open ⊑ {A = Exp} using () renaming (refl to ⊑e-refl)
open ⊑ {A = Assms} using () renaming (refl to ⊑a-refl)
private _≟t_ = HasDecEq._≟_ typ-decEq


⊑⇒-fst : ∀ {τ₁ τ₂ τ} → τ₁ ⇒ τ₂ ⊑t τ → ∃[ τ₁' ] ∃[ τ₂' ] (τ ≡ τ₁' ⇒ τ₂' ∧ τ₁ ⊑t τ₁' ∧ τ₂ ⊑t τ₂')
⊑⇒-fst (⊑⇒ p q) = _ , _ , refl , p , q

-- MIN SLICE DECOMPOSITIONS
_⇒ₛ_ : ∀ {τ₁ τ₂ : Typ} → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ₁ ⇒ τ₂ ⌋
s₁ ⇒ₛ s₂ = (s₁ .↓ ⇒ s₂ .↓) isSlice ⊑⇒ (s₁ .proof) (s₂ .proof)

_×ₛ_ : ∀ {τ₁ τ₂ : Typ} → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ₁ × τ₂ ⌋
s₁ ×ₛ s₂ = (s₁ .↓ × s₂ .↓) isSlice ⊑× (s₁ .proof) (s₂ .proof)

∀·ₛ : ∀ {τ : Typ} → ⌊ τ ⌋ → ⌊ ∀· τ ⌋
∀·ₛ s = (∀· (s .↓)) isSlice ⊑∀ (s .proof)

_&ₛ_ : ∀ {e₁ e₂ : Exp} → ⌊ e₁ ⌋ → ⌊ e₂ ⌋ → ⌊ e₁ & e₂ ⌋
s₁ &ₛ s₂ = (s₁ .↓ & s₂ .↓) isSlice ⊑& (s₁ .proof) (s₂ .proof)

-- Unmatch/unsub helpers (duplicated from SynSliceCalc which has parse errors)
unmatch⇒ : ∀ {τ τ₁ τ₂} → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂ → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ ⌋
unmatch⇒ {τ} eq s₁ s₂ with diag τ (□ ⇒ □)
unmatch⇒      refl s₁ s₂ | kind⇒ =
  subst ⌊_⌋ ⊔t-zeroᵣ s₁ ⇒ₛ subst ⌊_⌋ ⊔t-zeroᵣ s₂
unmatch⇒ {τ} eq   s₁ s₂ | diff with τ ≟t □
...                                | yes refl = ⊥ₛ
unmatch⇒      ()   _  _  | diff    | no _

unmatch∀ : ∀ {τ τ'} → τ ⊔ ∀· □ ≡ ∀· τ' → ⌊ τ' ⌋ → ⌊ τ ⌋
unmatch∀ {τ} eq s with diag τ (∀· □)
unmatch∀      refl s | kind∀ = ∀·ₛ (subst ⌊_⌋ ⊔t-zeroᵣ s)
unmatch∀ {τ} eq    s | diff with τ ≟t □
...                           | yes refl = ⊥ₛ
unmatch∀      ()   _ | diff    | no _

unsub : ∀ {τ' σ} → ⌊ [ zero ↦ σ ] τ' ⌋ → ⌊ τ' ⌋
unsub {τ'} s = ↑ (⊑Lat.x⊓y⊑y (s .↓) τ')

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

Λₛ : ∀ {e : Exp} → ⌊ e ⌋ → ⌊ Λ e ⌋
Λₛ (σ isSlice σ⊑e) = (Λ σ) isSlice (⊑Λ σ⊑e)

unshiftΓₛ : ∀ {Γ a} → ⌊ shiftΓ a Γ ⌋ → ⌊ Γ ⌋
unshiftΓₛ {a = a} (γ isSlice γ⊑) = unshiftΓ a γ isSlice unshiftΓ-shiftΓ-⊑ γ⊑

shiftΓₛ : ∀ {Γ a} → ⌊ Γ ⌋ → ⌊ shiftΓ a Γ ⌋
shiftΓₛ {a = a} (γ isSlice γ⊑) = shiftΓ a γ isSlice shiftΓ-⊑ γ⊑

unshift-shiftΓₛ : ∀ {Γ a} (γₛ : ⌊ Γ ⌋) → unshiftΓₛ {a = a} (shiftΓₛ γₛ) ≈ₛ γₛ
unshift-shiftΓₛ (γ isSlice _) = unshiftΓ-shiftΓ γ

-- TODO: Prove
postulate
  shift-unshiftΓ : ∀ {a Γ} (γ : Assms) → γ ⊑a shiftΓ a Γ → shiftΓ a (unshiftΓ a γ) ≡ γ

shift-unshiftΓₛ : ∀ {Γ a} (γₛ : ⌊ shiftΓ a Γ ⌋) → shiftΓₛ (unshiftΓₛ γₛ) ≈ₛ γₛ
shift-unshiftΓₛ {a = a} (γ isSlice γ⊑) = shift-unshiftΓ γ γ⊑

-- Lift a SynSlice of D to a SynSlice of (↦Λ D) by wrapping with ↦Λ.

Λsyn : ∀ {n Γ e τ} {D : suc n ； shiftΓ 1 Γ ⊢ e ↦ τ}
         {υ : ⌊ τ ⌋}
       → SynSlice D ◂ υ
       → SynSlice (↦Λ D) ◂ (∀·ₛ υ)
Λsyn {Γ = Γ} {D = D} {υ = υ} s
  = unshiftΓₛ (s ↓γₛ) ,ₛ Λₛ (s ↓σₛ) ⇑ ∀·ₛ (s .type)
    ∈ ↦Λ (subst (λ γ → _ ； γ ⊢ _ ↦ _) (Eq.sym (shift-unshiftΓₛ (s ↓γₛ))) (s .syn))
    ⊒ ⊑∀ (s .valid)

-- A minimal slice of ↦Λ D ◂ ∀·ₛ υ yields a minimal slice of D ◂ υ.
min-Λ-decomposability
  : ∀ {n Γ e τ}
      {D : suc n ； shiftΓ 1 Γ ⊢ e ↦ τ}
      {υ : ⌊ τ ⌋}
      ((mΛ , _) : MinSynSlice (↦Λ D) ◂ (∀·ₛ υ))
    → Σ[ (m , _) ∈ MinSynSlice D ◂ υ ]
        mΛ ≈ Λsyn m
min-Λ-decomposability {D = D} (mΛ , min)
  with mΛ .syn | mΛ .valid | mΛ ↓σ⊑ | mΛ ↓ϕ⊑
... | ↦Λ d | ⊑∀ υ⊑ϕ | ⊑Λ σ'⊑e | ⊑∀ ϕ⊑τ
  = (m , min-m) , min (Λsyn m) Λm⊑mΛ
  where
    s = ((↑ (shiftΓ-⊑ (mΛ ↓γ⊑))) ,ₛ (↑ σ'⊑e)) ⇑ ↑ ϕ⊑τ ∈ d ⊒ υ⊑ϕ
    m = minExists s .proj₁ ↓s
    min-m = minimality (minExists s .proj₁)
    Λm⊑mΛ : (Λsyn m) ↓ρ ⊑ mΛ ↓ρ
    Λm⊑mΛ = unshiftΓ-shiftΓ-⊑ (minExists s .proj₂ .proj₁)
            , ⊑Λ (minExists s .proj₂ .proj₂)

-- Annotated lambdas
λ:ₛ : ∀ {τ₁ : Typ} {e : Exp} → ⌊ τ₁ ⌋ → ⌊ e ⌋ → ⌊ λ: τ₁ ⇒ e ⌋
λ:ₛ (τ isSlice τ⊑τ₁) (σ isSlice σ⊑e) = (λ: τ ⇒ σ) isSlice (⊑λ τ⊑τ₁ σ⊑e)

hdₛ : ∀ {τ : Typ} {Γ : Assms} → ⌊ τ ∷ Γ ⌋ → ⌊ τ ⌋
hdₛ (_ isSlice (⊑∷ h _)) = _ isSlice h

tlₛ : ∀ {τ : Typ} {Γ : Assms} → ⌊ τ ∷ Γ ⌋ → ⌊ Γ ⌋
tlₛ (_ isSlice (⊑∷ _ t)) = _ isSlice t

hdₛ-⊑ : ∀ {τ Γ τ' Γ'} (γₛ : ⌊ τ ∷ Γ ⌋) → γₛ .↓ ⊑a (τ' ∷ Γ') → hdₛ γₛ .↓ ⊑t τ'
hdₛ-⊑ (_ isSlice (⊑∷ _ _)) (⊑∷ h _) = h

tlₛ-⊑ : ∀ {τ Γ τ' Γ'} (γₛ : ⌊ τ ∷ Γ ⌋) → γₛ .↓ ⊑a (τ' ∷ Γ') → tlₛ γₛ .↓ ⊑a Γ'
tlₛ-⊑ (_ isSlice (⊑∷ _ _)) (⊑∷ _ t) = t

-- Lift a SynSlice of D to a SynSlice of (↦λ: wf D) by wrapping with ↦λ:.
-- Given a slice of a function body, we can construct a slice of
-- a function which some annotation ϕ₁, so long as the annotation
-- assumes at least as much as the slice of the body used
λ:syn : ∀ {n Γ e τ₁ τ₂} {wf : n ⊢wf τ₁} {D : n ； (τ₁ ∷ Γ) ⊢ e ↦ τ₂}
          {υ₂ : ⌊ τ₂ ⌋} {ϕ₁ : ⌊ τ₁ ⌋}
        → (υ₁ : ⌊ τ₁ ⌋)
        → υ₁ ⊑ₛ ϕ₁
        → (s : SynSlice D ◂ υ₂)
        → hdₛ (s ↓γₛ) ⊑ₛ ϕ₁
        → SynSlice (↦λ: wf D) ◂ (υ₁ ⇒ₛ υ₂)
λ:syn {wf = wf} {D = D} {ϕ₁ = ϕ₁} υ₁ υ₁⊑ϕ₁
      (((_ ∷ γ' , σ') isSlice (⊑∷ _ γ'⊑Γ , σ'⊑e)) ⇑ ϕ ∈ d ⊒ υ⊑ϕ) sγ₀⊑ϕ₁
  with static-gradual-syn (⊑∷ (ϕ₁ .proof) γ'⊑Γ) σ'⊑e D
... | ϕ₂ , d₂ , ϕ₂⊑τ₂
  = (↑ γ'⊑Γ) ,ₛ λ:ₛ ϕ₁ (σ' isSlice σ'⊑e)
    ⇑ ϕ₁ ⇒ₛ (↑ ϕ₂⊑τ₂)
    ∈ ↦λ: (wf-⊑ wf (ϕ₁ .proof)) d₂
    ⊒ ⊑⇒ υ₁⊑ϕ₁ (⊑t-trans υ⊑ϕ (syn-precision (⊑∷ sγ₀⊑ϕ₁ ⊑a-refl) ⊑e-refl d₂ d))

-- Minimal λ: slices decompose: a minimal slice of ↦λ: wf D ◂ (υ₁ ⇒ₛ υ₂)
-- contains a minimal slice of D ◂ υ₂ with υ₁ (or weaker) in the context
-- Again, the converse is not valid:
-- Take a naive slice reconstruction of the body:
-- x : * × * ⊢ case ? of a ↦ x | b ↦ * & *
-- with min slice x : □ × * ⊢ case ? of a ↦ x | b ↦ * & □
-- Yet when placed in a function is not min:
-- λ x : (* × *). case ? of a ↦ x | b ↦ * & □
-- The arg forces a more precise context TODO: add to counterexamples

-- However, decomposing a min lambda is possible as we know the minimal arg type (the sliced annotation)
-- If this mechanisation is to be extended with patterns, the υ₁ argument to
-- λ:syn would instead be a SynSlice (⊒ υ₁) this proof allows ϕ₁ ⊒ υ₁
-- in preparation for this, but currently ϕ₁ ≈ υ₁ in reality
min-λ:-decomposability
  : ∀ {n Γ e τ₁ τ₂}
      {wf : n ⊢wf τ₁} {D : n ； (τ₁ ∷ Γ) ⊢ e ↦ τ₂}
      {υ₁ : ⌊ τ₁ ⌋} {υ₂ : ⌊ τ₂ ⌋}
      ((mλ: , _) : MinSynSlice (↦λ: wf D) ◂ (υ₁ ⇒ₛ υ₂))
    → Σ[ (m₂ , _) ∈ MinSynSlice D ◂ υ₂ ]
      Σ[ ϕ₁ ∈ ⌊ τ₁ ⌋ ]
      Σ[ υ₁⊑ϕ₁ ∈ υ₁ ⊑ₛ ϕ₁ ]
      Σ[ m₂γ₀⊑ϕ₁ ∈ hdₛ (m₂ ↓γₛ) ⊑ₛ ϕ₁ ]
         mλ: ≈ (λ:syn {wf = wf} {ϕ₁ = ϕ₁} υ₁ υ₁⊑ϕ₁ m₂ m₂γ₀⊑ϕ₁)
min-λ:-decomposability {wf = wf} {D = D} {υ₁ = υ₁} (mλ: , min)
  with mλ: .syn | mλ: .valid | mλ: ↓σ⊑ | mλ: ↓ϕ⊑
... | ↦λ: wf' d | ⊑⇒ υ₁⊑ϕ₁ υ₂⊑ϕ₂ | ⊑λ α⊑τ₁ σ⊑e | ⊑⇒ ϕ₁⊑τ₁ ϕ₂⊑τ₂
  = (m₂ , min-m₂) , ↑ ϕ₁⊑τ₁ , υ₁⊑ϕ₁ , m₂γ₀⊑ϕ₁
    , min (λ:syn {wf = wf} υ₁ υ₁⊑ϕ₁ m₂ m₂γ₀⊑ϕ₁) λ:m⊑mλ:
  where
    s₂ = (↑ (⊑∷ ϕ₁⊑τ₁ (mλ: ↓γ⊑))) ,ₛ (↑ σ⊑e) ⇑ ↑ ϕ₂⊑τ₂ ∈ d ⊒ υ₂⊑ϕ₂
    m₂ = minExists s₂ .proj₁ ↓s
    min-m₂ = minimality (minExists s₂ .proj₁)
    m₂⊑s₂ = minExists s₂ .proj₂
    m₂γ₀⊑ϕ₁ : hdₛ (m₂ ↓γₛ) ⊑ₛ (↑ ϕ₁⊑τ₁)
    m₂γ₀⊑ϕ₁ = hdₛ-⊑ (m₂ ↓γₛ) (m₂⊑s₂ .proj₁)
    λ:m⊑mλ: : (λ:syn {wf = wf} υ₁ υ₁⊑ϕ₁ m₂ m₂γ₀⊑ϕ₁) ↓ρ ⊑ mλ: ↓ρ
    λ:m⊑mλ: with m₂ | m₂⊑s₂ | m₂γ₀⊑ϕ₁
    ... | ((_ ∷ _ , _) isSlice (⊑∷ _ _ , _)) ⇑ _ ∈ _ ⊒ _
        | ⊑∷ _ γ₂⊑ , σ₂⊑ | _ = γ₂⊑ , ⊑λ ⊑t-refl σ₂⊑

-- Let bindings
defₛ : ∀ {e' e : Exp} → ⌊ e' ⌋ → ⌊ e ⌋ → ⌊ def e' ⊢ e ⌋
defₛ (σ₁ isSlice σ₁⊑e') (σ₂ isSlice σ₂⊑e) = (def σ₁ ⊢ σ₂) isSlice (⊑def σ₁⊑e' σ₂⊑e)

-- Lift two SynSlices to a SynSlice of (↦def D₁ D₂).
-- The outer assumption comes from s₁
defsyn : ∀ {n Γ e' e τ' τ} {D₁ : n ； Γ ⊢ e' ↦ τ'}
           {D₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ} {υ' υ}
         → (s₁ : SynSlice D₁ ◂ υ') → (s₂ : SynSlice D₂ ◂ υ)
         → s₂ ↓γ ⊑a (s₁ .type .↓ ∷ s₁ ↓γ)
         → SynSlice (↦def D₁ D₂) ◂ υ
defsyn {D₁ = D₁} {D₂ = D₂}
       (ρₛ₁ ⇑ ϕ₁ ∈ d₁ ⊒ υ'⊑ϕ₁) (ρₛ₂ ⇑ ϕ₂ ∈ d₂ ⊒ υ⊑ϕ₂) ctx⊑
  with static-gradual-syn (⊑∷ ϕ₁⊑τ' (fstₛ ρₛ₁ .proof)) (sndₛ ρₛ₂ .proof) D₂
  where ϕ₁⊑τ' = syn-precision (fstₛ ρₛ₁ .proof) (sndₛ ρₛ₁ .proof) D₁ d₁
... | ϕ , d₂' , ϕ⊑τ
  = (fstₛ ρₛ₁ ,ₛ defₛ (sndₛ ρₛ₁) (sndₛ ρₛ₂))
    ⇑ ↑ ϕ⊑τ ∈ ↦def d₁ d₂'
    ⊒ ⊑t-trans υ⊑ϕ₂ (syn-precision ctx⊑ ⊑e-refl d₂' d₂)

min-def-decomposability
  : ∀ {n Γ e' e τ' τ}
      {D₁ : n ； Γ ⊢ e' ↦ τ'} {D₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ}
      {υ : ⌊ τ ⌋}
    → υ .↓ ≢ □
    → ((mdef , _) : MinSynSlice (↦def D₁ D₂) ◂ υ)
    → ∃[ υ' ]
      Σ[ (m₁ , _) ∈ MinSynSlice D₁ ◂ υ' ]
      Σ[ (m₂ , _) ∈ MinSynSlice D₂ ◂ υ ]
      Σ[ ctx⊑ ∈ m₂ ↓γ ⊑a (m₁ .type .↓ ∷ m₁ ↓γ) ]
        mdef ≈ (defsyn m₁ m₂ ctx⊑)
min-def-decomposability {D₁ = D₁} {D₂ = D₂} υ≢□ (mdef , min)
  with mdef .syn | mdef .valid | mdef ↓σ⊑ | mdef ↓ϕ⊑
... | ↦□ | ⊑□ | _ | _ = ⊥-elim (υ≢□ refl)
... | ↦def d₁ d₂ | υ⊑ϕ | ⊑def σ₁⊑e' σ₂⊑e | ϕ⊑τ
  = ↑ ϕ₁⊑τ' , (m₁ , min-m₁) , (m₂ , min-m₂) , ctx⊑
    , min (defsyn m₁ m₂ ctx⊑) defm⊑mdef
  where
    ϕ₁⊑τ' = syn-precision (mdef ↓γ⊑) σ₁⊑e' D₁ d₁
    s₁ = ((mdef ↓γₛ) ,ₛ (_ isSlice σ₁⊑e')) ⇑ ↑ ϕ₁⊑τ' ∈ d₁ ⊒ ⊑t-refl
    s₂ = (↑ (⊑∷ ϕ₁⊑τ' (mdef ↓γ⊑))) ,ₛ (↑ σ₂⊑e) ⇑ ↑ ϕ⊑τ ∈ d₂ ⊒ υ⊑ϕ
    m₁ = minExists s₁ .proj₁ ↓s
    min-m₁ = minimality (minExists s₁ .proj₁)
    m₁⊑s₁ = minExists s₁ .proj₂
    m₂ = minExists s₂ .proj₁ ↓s
    min-m₂ = minimality (minExists s₂ .proj₁)
    m₂⊑s₂ = minExists s₂ .proj₂
    postulate ctx⊑ : m₂ ↓γ ⊑a (m₁ .type .↓ ∷ m₁ ↓γ)
    defm⊑mdef : (defsyn m₁ m₂ ctx⊑) ↓ρ ⊑ mdef ↓ρ
    defm⊑mdef with m₁ | m₂ | m₁⊑s₁ | m₂⊑s₂
    ... | ρₛ₁ ⇑ _ ∈ _ ⊒ _ | ρₛ₂ ⇑ _ ∈ _ ⊒ _
        | γ₁⊑ , σ₁'⊑ | γ₂⊑ , σ₂'⊑ = γ₁⊑ , ⊑def σ₁'⊑ σ₂'⊑

