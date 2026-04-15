open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.List using (_∷_)
open import Core
open import Core.Typ.Base using (diag; kind□; kind⇒; kind×; kind+; kind∀; kindVar; kind*; diff)
open import Semantics.Statics
open import Slicing.Synthesis

module Slicing.SynSliceCalc where

_⇒ₛ_ : ∀ {τ₁ τ₂} → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ₁ ⇒ τ₂ ⌋
s₁ ⇒ₛ s₂ = (s₁ .↓ ⇒ s₂ .↓) isSlice ⊑⇒ (s₁ .proof) (s₂ .proof)

_×ₛ_ : ∀ {τ₁ τ₂} → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ₁ × τ₂ ⌋
s₁ ×ₛ s₂ = (s₁ .↓ × s₂ .↓) isSlice ⊑× (s₁ .proof) (s₂ .proof)

∀·ₛ : ∀ {τ} → ⌊ τ ⌋ → ⌊ ∀· τ ⌋
∀·ₛ s = (∀· (s .↓)) isSlice ⊑∀ (s .proof)

-- Lift component slices back through a match
-- TODO: Switch uses of subst to rewrites or equational reasoning
unmatch⇒ : ∀ {τ τ₁ τ₂} → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂ → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ ⌋
unmatch⇒ {τ} eq s₁ s₂ with diag τ (□ ⇒ □)
unmatch⇒      refl s₁ s₂ | kind⇒ =
  subst ⌊_⌋ ⊔t-zeroᵣ s₁ ⇒ₛ subst ⌊_⌋ ⊔t-zeroᵣ s₂
unmatch⇒ {τ} eq   s₁ s₂ | diff with τ ≟ □
...                                | yes refl = ⊥ₛ
unmatch⇒      ()   _  _  | diff    | no _

unmatch× : ∀ {τ τ₁ τ₂} → τ ⊔ □ × □ ≡ τ₁ × τ₂ → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ ⌋
unmatch× {τ} eq s₁ s₂ with diag τ (□ × □)
unmatch×      refl s₁ s₂ | kind× =
  subst ⌊_⌋ ⊔t-zeroᵣ s₁ ×ₛ subst ⌊_⌋ ⊔t-zeroᵣ s₂
unmatch× {τ} eq   s₁ s₂ | diff with τ ≟ □
...                                | yes refl = ⊥ₛ
unmatch×      ()   _  _  | diff    | no _

unmatch+ : ∀ {τ τ₁ τ₂} → τ ⊔ □ + □ ≡ τ₁ + τ₂ → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ ⌋
unmatch+ {τ} eq s₁ s₂ with diag τ (□ + □)
unmatch+      refl s₁ s₂ | kind+ =
  ↑ (⊑+ (subst ⌊_⌋ ⊔t-zeroᵣ s₁ .proof) (subst ⌊_⌋ ⊔t-zeroᵣ s₂ .proof))
unmatch+ {τ} eq   s₁ s₂ | diff with τ ≟ □
...                                | yes refl = ⊥ₛ
unmatch+      ()   _  _  | diff    | no _

unmatch∀ : ∀ {τ τ'} → τ ⊔ ∀· □ ≡ ∀· τ' → ⌊ τ' ⌋ → ⌊ τ ⌋
unmatch∀ {τ} eq s with diag τ (∀· □)
unmatch∀      refl s | kind∀ = ∀·ₛ (subst ⌊_⌋ ⊔t-zeroᵣ s)
unmatch∀ {τ} eq   s | diff with τ ≟ □
...                           | yes refl = ⊥ₛ
unmatch∀      ()   _ | diff    | no _

-- Embed slices into join
⊔ₛ-inj₁ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ⌊ τ₁ ⌋ → ⌊ τ₁ ⊔ τ₂ ⌋
⊔ₛ-inj₁ con s = weaken (~.⊔-ub₁ con) s

⊔ₛ-inj₂ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ⌊ τ₂ ⌋ → ⌊ τ₁ ⊔ τ₂ ⌋
⊔ₛ-inj₂ con s = weaken (~.⊔-ub₂ con) s

unsub : ∀ {τ' σ} → ⌊ [ zero ↦ σ ] τ' ⌋ → ⌊ τ' ⌋
unsub {τ'} s = ↑ (⊑Lat.x⊓y⊑y (s .↓) τ')

⊔ₛ-proj₁ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ⌊ τ₁ ⊔ τ₂ ⌋ → ⌊ τ₁ ⌋
⊔ₛ-proj₁ {τ₁} _ s = ↑ (⊑Lat.x⊓y⊑y (s .↓) τ₁)

⊔ₛ-proj₂ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ⌊ τ₁ ⊔ τ₂ ⌋ → ⌊ τ₂ ⌋
⊔ₛ-proj₂ {τ₂ = τ₂} _ s = ↑ (⊑Lat.x⊓y⊑y (s .↓) τ₂)

-- Minimal synthesis slice derivation.
data MinSyn : ∀ {n Γ e τ} → (D : n ； Γ ⊢ e ↦ τ) → ⌊ τ ⌋ → Set where
  min□     : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ}
           → MinSyn D ⊥ₛ

  min*     : ∀ {n Γ}
           → MinSyn (↦* {n} {Γ}) ⊤ₛ

  minVar   : ∀ {n Γ k τ} {p : Γ at k ≡ just τ}
           → (υ : ⌊ τ ⌋)
           → MinSyn (↦Var {n = n} {Γ = Γ} {k = k} {τ = τ} p) υ

  minλ:    : ∀ {n Γ e τ₁ τ₂} {wf : n ⊢wf τ₁} {D : n ； (τ₁ ∷ Γ) ⊢ e ↦ τ₂}
           → (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
           → MinSyn D υ₂
           → MinSyn (↦λ: wf D) (υ₁ ⇒ₛ υ₂)

  mindef   : ∀ {n Γ e' e τ' τ} {D₁ : n ； Γ ⊢ e' ↦ τ'} {D₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ}
           → (υ' : ⌊ τ' ⌋) (υ : ⌊ τ ⌋)
           → MinSyn D₁ υ'
           → MinSyn D₂ υ
           → MinSyn (↦def D₁ D₂) υ

  minΛ     : ∀ {n Γ e τ} {D : suc n ； shiftΓ (suc zero) Γ ⊢ e ↦ τ}
           → (υ : ⌊ τ ⌋)
           → MinSyn D υ
           → MinSyn (↦Λ D) (∀·ₛ υ)

  min∘     : ∀ {n Γ e₁ e₂ τ τ₁ τ₂}
               {D₁ : n ； Γ ⊢ e₁ ↦ τ} {m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
               {D₂ : n ； Γ ⊢ e₂ ↤ τ₁}
           → (υ : ⌊ τ₂ ⌋)
           → MinSyn D₁ (unmatch⇒ m ⊥ₛ υ)
           → MinSyn (↦∘ D₁ m D₂) υ

  min<>    : ∀ {n Γ e τ τ' σ}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ ∀· □ ≡ ∀· τ'} {wf : n ⊢wf σ}
           → (υ : ⌊ [ zero ↦ σ ] τ' ⌋)
           → MinSyn D (unmatch∀ m (unsub υ))
           → MinSyn (↦<> D m wf) υ

  min&     : ∀ {n Γ e₁ e₂ τ₁ τ₂}
               {D₁ : n ； Γ ⊢ e₁ ↦ τ₁} {D₂ : n ； Γ ⊢ e₂ ↦ τ₂}
           → (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
           → MinSyn D₁ υ₁
           → MinSyn D₂ υ₂
           → MinSyn (↦& D₁ D₂) (υ₁ ×ₛ υ₂)

  minπ₁    : ∀ {n Γ e τ τ₁ τ₂}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
           → (υ : ⌊ τ₁ ⌋)
           → MinSyn D (unmatch× m υ ⊥ₛ)
           → MinSyn (↦π₁ D m) υ

  minπ₂    : ∀ {n Γ e τ τ₁ τ₂}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
           → (υ : ⌊ τ₂ ⌋)
           → MinSyn D (unmatch× m ⊥ₛ υ)
           → MinSyn (↦π₂ D m) υ

  mincase₁ : ∀ {n Γ e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂'}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ + □ ≡ τ₁ + τ₂}
               {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
               {con : τ₁' ~ τ₂'}
           → (υ : ⌊ τ₁' ⊔ τ₂' ⌋) (υ₁ : ⌊ τ₁ ⌋)
           → MinSyn D (unmatch+ m υ₁ ⊥ₛ)
           → MinSyn D₁ (⊔ₛ-proj₁ con υ)
           → MinSyn (↦case D m D₁ D₂ con) υ

  mincase₂ : ∀ {n Γ e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂'}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ + □ ≡ τ₁ + τ₂}
               {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
               {con : τ₁' ~ τ₂'}
           → (υ : ⌊ τ₁' ⊔ τ₂' ⌋) (υ₂ : ⌊ τ₂ ⌋)
           → MinSyn D (unmatch+ m ⊥ₛ υ₂)
           → MinSyn D₂ (⊔ₛ-proj₂ con υ)
           → MinSyn (↦case D m D₁ D₂ con) υ

  -- ↦case, both branches: both contribute to the type slice
  mincase  : ∀ {n Γ e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂'}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ + □ ≡ τ₁ + τ₂}
               {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
               {con : τ₁' ~ τ₂'}
           → (υ : ⌊ τ₁' ⊔ τ₂' ⌋) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
           → MinSyn D (unmatch+ m υ₁ υ₂)
           → MinSyn D₁ (⊔ₛ-proj₁ con υ)
           → MinSyn D₂ (⊔ₛ-proj₂ con υ)
           → MinSyn (↦case D m D₁ D₂ con) υ

-- Soundness: extract a SynSlice from a MinSyn
postulate
  extract : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → MinSyn D υ → IsMinSynSlice D υ

-- Completeness: every minimal SynSlice arises from some MinSyn
  complete : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
             → (s : IsMinSynSlice D υ)
             → Σ[ m ∈ MinSyn D υ ] ((extract m) .proj₁) ≈ s
