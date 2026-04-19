open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.List using (_∷_)
open import Core
open import Semantics.Statics
open import Slicing.Synthesis.Synthesis

module Slicing.Synthesis.SynSliceCalc where

-- Embed slices into join
⊔ₛ-inj₁ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ⌊ τ₁ ⌋ → ⌊ τ₁ ⊔ τ₂ ⌋
⊔ₛ-inj₁ con s = weaken (~.⊔-ub₁ con) s

⊔ₛ-inj₂ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ⌊ τ₂ ⌋ → ⌊ τ₁ ⊔ τ₂ ⌋
⊔ₛ-inj₂ con s = weaken (~.⊔-ub₂ con) s

⊔ₛ-proj₁ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ⌊ τ₁ ⊔ τ₂ ⌋ → ⌊ τ₁ ⌋
⊔ₛ-proj₁ {τ₁} _ s = ↑ (⊑Lat.x⊓y⊑y (s .↓) τ₁)

⊔ₛ-proj₂ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ⌊ τ₁ ⊔ τ₂ ⌋ → ⌊ τ₂ ⌋
⊔ₛ-proj₂ {τ₂ = τ₂} _ s = ↑ (⊑Lat.x⊓y⊑y (s .↓) τ₂)

-- Minimal synthesis slice derivation.
-- Φ : ⌊ Γ ⌋ is a 'lower bound' on assumption slices
-- representing binder-introduced types that cannot be sliced further
-- without making an external part of the slice (e.g. a function arg part)
data MinSyn {n : ℕ} : ∀ {Γ : Assms} {e : Exp} {τ : Typ}
          → ⌊ Γ ⌋ → (D : n ； Γ ⊢ e ↦ τ) → ⌊ τ ⌋ → Set where

  min□     : ∀ {Γ e τ} {Φ : ⌊ Γ ⌋} {D : n ； Γ ⊢ e ↦ τ}
           → MinSyn Φ D ⊥ₛ

  min*     : ∀ {Γ} {Φ : ⌊ Γ ⌋}
           → MinSyn Φ (↦* {n} {Γ}) ⊤ₛ

  minVar   : ∀ {Γ k τ} {Φ : ⌊ Γ ⌋} {p : Γ at k ≡ just τ}
           → (υ : ⌊ τ ⌋)
           → lookupₛ Φ p ⊑ₛ υ
           → MinSyn Φ (↦Var {n = n} p) υ

  minλ:    : ∀ {Γ e τ₁ τ₂} {Φ : ⌊ Γ ⌋} {wf : n ⊢wf τ₁} {D : n ； (τ₁ ∷ Γ) ⊢ e ↦ τ₂}
           → (ϕ₁ : ⌊ τ₁ ⌋) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
           → υ₁ ⊑ₛ ϕ₁
           → MinSyn (ϕ₁ ∷ₛ Φ) D υ₂
           → MinSyn Φ (↦λ: wf D) (υ₁ ⇒ₛ υ₂)

  mindef   : ∀ {Γ e' e τ' τ} {Φ : ⌊ Γ ⌋}
               {D₁ : n ； Γ ⊢ e' ↦ τ'} {D₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ}
           → (ϕ : ⌊ τ' ⌋) (υ' : ⌊ τ' ⌋) (υ : ⌊ τ ⌋)
           → MinSyn Φ D₁ υ'
           → MinSyn (ϕ ∷ₛ Φ) D₂ υ
           → MinSyn Φ (↦def D₁ D₂) υ

  minΛ     : ∀ {Γ e τ} {Φ : ⌊ Γ ⌋} {D : suc n ； shiftΓ (suc zero) Γ ⊢ e ↦ τ}
           → (υ : ⌊ τ ⌋)
           → MinSyn (shiftΓₛ Φ) D υ
           → MinSyn Φ (↦Λ D) (∀·ₛ υ)

  min∘     : ∀ {Γ e₁ e₂ τ τ₁ τ₂} {Φ : ⌊ Γ ⌋}
               {D₁ : n ； Γ ⊢ e₁ ↦ τ} {m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
               {D₂ : n ； Γ ⊢ e₂ ↤ τ₁}
           → (υ : ⌊ τ₂ ⌋)
           → MinSyn Φ D₁ (unmatch⇒ m ⊥ₛ υ)
           → MinSyn Φ (↦∘ D₁ m D₂) υ

  min<>    : ∀ {Γ e τ τ' σ} {Φ : ⌊ Γ ⌋}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ ∀· □ ≡ ∀· τ'} {wf : n ⊢wf σ}
           → (υ : ⌊ [ zero ↦ σ ] τ' ⌋) (υ' : ⌊ τ' ⌋) (ϕ₁ : ⌊ σ ⌋)
           → υ ⊑ₛ subₛ ϕ₁ υ'
           → MinSyn Φ D (unmatch∀ m υ')
           → MinSyn Φ (↦<> D m wf) υ

  min&     : ∀ {Γ e₁ e₂ τ₁ τ₂} {Φ : ⌊ Γ ⌋}
               {D₁ : n ； Γ ⊢ e₁ ↦ τ₁} {D₂ : n ； Γ ⊢ e₂ ↦ τ₂}
           → (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
           → MinSyn Φ D₁ υ₁ → MinSyn Φ D₂ υ₂
           → MinSyn Φ (↦& D₁ D₂) (υ₁ ×ₛ υ₂)

  minπ₁    : ∀ {Γ e τ τ₁ τ₂} {Φ : ⌊ Γ ⌋}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
           → (υ : ⌊ τ₁ ⌋)
           → MinSyn Φ D (unmatch× m υ ⊥ₛ)
           → MinSyn Φ (↦π₁ D m) υ

  minπ₂    : ∀ {Γ e τ τ₁ τ₂} {Φ : ⌊ Γ ⌋}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
           → (υ : ⌊ τ₂ ⌋)
           → MinSyn Φ D (unmatch× m ⊥ₛ υ)
           → MinSyn Φ (↦π₂ D m) υ

  -- Single case constructor — when a branch doesn't contribute,
  -- its query is ⊥ₛ and sub-proof is min□
  mincase  : ∀ {Γ e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂'} {Φ : ⌊ Γ ⌋}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ + □ ≡ τ₁ + τ₂}
               {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
               {c : τ₁' ~ τ₂'}
           → (υ : ⌊ τ₁' ⊔ τ₂' ⌋) (ς₁ : ⌊ τ₁ ⌋) (ς₂ : ⌊ τ₂ ⌋)
               (υ₁ : ⌊ τ₁' ⌋) (υ₂ : ⌊ τ₂' ⌋)
           → MinSyn Φ D (unmatch+ m ς₁ ς₂)
           → MinSyn (ς₁ ∷ₛ Φ) D₁ υ₁
           → MinSyn (ς₂ ∷ₛ Φ) D₂ υ₂
           → MinSyn Φ (↦case D m D₁ D₂ c) υ

-- Construction helpers (postulated for now)
postulate
  build-Var   : ∀ {n Γ k τ} → (Φ : ⌊ Γ ⌋) → (p : Γ at k ≡ just τ) → (υ : ⌊ τ ⌋)
              → lookupₛ Φ p ⊑ₛ υ
              → SynSlice (↦Var {n = n} p) ◂ υ

-- Build a SynSlice from a MinSyn derivation
build-extract : ∀ {n Γ e τ} {Φ : ⌊ Γ ⌋} {D : n ； Γ ⊢ e ↦ τ} {υ}
              → MinSyn Φ D υ → SynSlice D ◂ υ
build-extract min□ = ⊥-syn
build-extract (min* {Γ = Γ}) = (⊥ₛ {a = Γ} ,ₛ ⊤ₛ) ⇑ ⊤ₛ ∈ ↦* ⊒ ⊑ₛ.refl {x = ⊤ₛ}
build-extract (minVar {Φ = Φ} {p = p} υ lb) = build-Var Φ p υ lb
build-extract (minλ: ϕ₁ υ₁ υ₂ υ₁⊑ϕ₁ m₂) = {!λ:syn!}
build-extract (mindef ϕ υ' υ m₁ m₂) = {!defsyn!}
build-extract (minΛ υ m) = {!Λsyn!}
build-extract (min∘ υ m) = {!∘syn!}
build-extract (min<> υ υ' ϕ₁ υ⊑sub m) = {!<>syn!}
build-extract (min& υ₁ υ₂ m₁ m₂) = {!&syn!}
build-extract (minπ₁ υ m) = {!π₁syn!}
build-extract (minπ₂ υ m) = {!π₂syn!}
build-extract (mincase υ ς₁ ς₂ υ₁ υ₂ m m₁ m₂) = {!casesyn!}

-- □ can only synthesize □
□-syn-inv : ∀ {n Γ τ} → n ； Γ ⊢ □ ↦ τ → τ ≡ □
□-syn-inv ↦□ = refl

-- ⊥-syn is minimal: the bottom program slice is the smallest
minimal-□ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} → IsMinimal (⊥-syn {D = D})
minimal-□ s' s'⊑ = ⊑.antisym ⦃ prog-slice-precision ⦄
                    (⊑ₛLat.⊥ₛ-min (s' .progₛ)) s'⊑

-- Minimality: each constructed SynSlice is minimal
postulate
  minimal : ∀ {n Γ e τ} {Φ : ⌊ Γ ⌋} {D : n ； Γ ⊢ e ↦ τ} {υ}
          → (m : MinSyn Φ D υ) → IsMinimal (build-extract m)

-- Soundness: extract a minimal SynSlice from a MinSyn
extract-min : ∀ {n Γ e τ} {Φ : ⌊ Γ ⌋} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → MinSyn Φ D υ → MinSynSlice D ◂ υ
extract-min m = build-extract m , minimal m

-- Completeness: every minimal SynSlice arises from some MinSyn
postulate
  complete : ∀ {n Γ e τ} {Φ : ⌊ Γ ⌋} {D : n ； Γ ⊢ e ↦ τ} {υ}
           → (s : MinSynSlice D ◂ υ)
           → Σ[ m ∈ MinSyn Φ D υ ] build-extract m ≈ s .proj₁
