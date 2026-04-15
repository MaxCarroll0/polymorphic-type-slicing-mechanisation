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

-- Construction helpers for each recursive case (postulated)
postulate
  build-Var   : ∀ {n Γ k τ} → (p : Γ at k ≡ just τ) → (υ : ⌊ τ ⌋)
              → SynSlice (↦Var {n = n} {Γ = Γ} {k = k} {τ = τ} p) υ
  build-λ:    : ∀ {n Γ e τ₁ τ₂} {wf : n ⊢wf τ₁} {D : n ； (τ₁ ∷ Γ) ⊢ e ↦ τ₂}
              → (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋) → SynSlice D υ₂
              → SynSlice (↦λ: wf D) (υ₁ ⇒ₛ υ₂)
  build-def   : ∀ {n Γ e' e τ' τ} {D₁ : n ； Γ ⊢ e' ↦ τ'} {D₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ}
              → (υ' : ⌊ τ' ⌋) (υ : ⌊ τ ⌋) → SynSlice D₁ υ' → SynSlice D₂ υ
              → SynSlice (↦def D₁ D₂) υ
  build-Λ     : ∀ {n Γ e τ} {D : suc n ； shiftΓ (suc zero) Γ ⊢ e ↦ τ}
              → (υ : ⌊ τ ⌋) → SynSlice D υ
              → SynSlice (↦Λ D) (∀·ₛ υ)
  build-∘     : ∀ {n Γ e₁ e₂ τ τ₁ τ₂}
                  {D₁ : n ； Γ ⊢ e₁ ↦ τ} {m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                  {D₂ : n ； Γ ⊢ e₂ ↤ τ₁}
              → (υ : ⌊ τ₂ ⌋) → SynSlice D₁ (unmatch⇒ m ⊥ₛ υ)
              → SynSlice (↦∘ D₁ m D₂) υ
  build-<>    : ∀ {n Γ e τ τ' σ}
                  {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ ∀· □ ≡ ∀· τ'} {wf : n ⊢wf σ}
              → (υ : ⌊ [ zero ↦ σ ] τ' ⌋) → SynSlice D (unmatch∀ m (unsub υ))
              → SynSlice (↦<> D m wf) υ
  build-&     : ∀ {n Γ e₁ e₂ τ₁ τ₂}
                  {D₁ : n ； Γ ⊢ e₁ ↦ τ₁} {D₂ : n ； Γ ⊢ e₂ ↦ τ₂}
              → (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
              → SynSlice D₁ υ₁ → SynSlice D₂ υ₂
              → SynSlice (↦& D₁ D₂) (υ₁ ×ₛ υ₂)
  build-π₁    : ∀ {n Γ e τ τ₁ τ₂}
                  {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
              → (υ : ⌊ τ₁ ⌋) → SynSlice D (unmatch× m υ ⊥ₛ)
              → SynSlice (↦π₁ D m) υ
  build-π₂    : ∀ {n Γ e τ τ₁ τ₂}
                  {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
              → (υ : ⌊ τ₂ ⌋) → SynSlice D (unmatch× m ⊥ₛ υ)
              → SynSlice (↦π₂ D m) υ
  build-case₁ : ∀ {n Γ e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂'}
                  {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
                  {con : τ₁' ~ τ₂'}
              → (υ : ⌊ τ₁' ⊔ τ₂' ⌋) (υ₁ : ⌊ τ₁ ⌋)
              → SynSlice D (unmatch+ m υ₁ ⊥ₛ)
              → SynSlice D₁ (⊔ₛ-proj₁ con υ)
              → SynSlice (↦case D m D₁ D₂ con) υ
  build-case₂ : ∀ {n Γ e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂'}
                  {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
                  {con : τ₁' ~ τ₂'}
              → (υ : ⌊ τ₁' ⊔ τ₂' ⌋) (υ₂ : ⌊ τ₂ ⌋)
              → SynSlice D (unmatch+ m ⊥ₛ υ₂)
              → SynSlice D₂ (⊔ₛ-proj₂ con υ)
              → SynSlice (↦case D m D₁ D₂ con) υ
  build-case  : ∀ {n Γ e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂'}
                  {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                  {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
                  {con : τ₁' ~ τ₂'}
              → (υ : ⌊ τ₁' ⊔ τ₂' ⌋) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
              → SynSlice D (unmatch+ m υ₁ υ₂)
              → SynSlice D₁ (⊔ₛ-proj₁ con υ)
              → SynSlice D₂ (⊔ₛ-proj₂ con υ)
              → SynSlice (↦case D m D₁ D₂ con) υ

-- Build a SynSlice from a MinSyn derivation
build-extract : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
              → MinSyn D υ → SynSlice D υ
build-extract min□ = ⊥-syn
build-extract min* = ⊥ₛ ,ₛ ⊤ₛ isSynSlice ↦*
build-extract (minVar {p = p} υ) = build-Var p υ
build-extract (minλ: υ₁ υ₂ m) = build-λ: υ₁ υ₂ (build-extract m)
build-extract (mindef υ' υ m₁ m₂) = build-def υ' υ (build-extract m₁) (build-extract m₂)
build-extract (minΛ υ m) = build-Λ υ (build-extract m)
build-extract (min∘ υ m) = build-∘ υ (build-extract m)
build-extract (min<> υ m) = build-<> υ (build-extract m)
build-extract (min& υ₁ υ₂ m₁ m₂) = build-& υ₁ υ₂ (build-extract m₁) (build-extract m₂)
build-extract (minπ₁ υ m) = build-π₁ υ (build-extract m)
build-extract (minπ₂ υ m) = build-π₂ υ (build-extract m)
build-extract (mincase₁ υ υ₁ m₁ m₂) = build-case₁ υ υ₁ (build-extract m₁) (build-extract m₂)
build-extract (mincase₂ υ υ₂ m₁ m₂) = build-case₂ υ υ₂ (build-extract m₁) (build-extract m₂)
build-extract (mincase υ υ₁ υ₂ m m₁ m₂) =
  build-case υ υ₁ υ₂ (build-extract m) (build-extract m₁) (build-extract m₂)

-- □ can only synthesize □
□-syn-inv : ∀ {n Γ τ} → n ； Γ ⊢ □ ↦ τ → τ ≡ □
□-syn-inv ↦□ = refl

-- ⊥-syn is minimal: the bottom program slice is the smallest
minimal-□ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} → IsMinimal (⊥-syn {D = D})
minimal-□ s' s'⊑ = ⊑.antisym ⦃ prog-slice-precision ⦄
                    (⊑ₛLat.⊥ₛ-min (s' .progₛ)) s'⊑

-- The * slice is minimal
minimal-* : ∀ {n Γ} → IsMinimal (build-extract (min* {n = n} {Γ = Γ}))
minimal-* s' (γ⊑ , ⊑□) with □-syn-inv (s' .valid)
... | ()
minimal-* s' (γ⊑ , ⊑*) = ⊑.antisym ⦃ prog-slice-precision ⦄
                          (⊑ₛLat.⊥ₛ-min (fstₛ (s' .progₛ)) , ⊑*) (γ⊑ , ⊑*)

-- Minimality: each constructed SynSlice is minimal
postulate
  minimal-Var   : ∀ {n Γ k τ} {p : Γ at k ≡ just τ} (υ : ⌊ τ ⌋)
                → IsMinimal (build-extract (minVar {n = n} {Γ = Γ} {p = p} υ))
  minimal-λ:    : ∀ {n Γ e τ₁ τ₂} {wf : n ⊢wf τ₁} {D : n ； (τ₁ ∷ Γ) ⊢ e ↦ τ₂}
                  (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋) (m : MinSyn D υ₂)
                → IsMinimal (build-extract (minλ: {wf = wf} υ₁ υ₂ m))
  minimal-def   : ∀ {n Γ e' e τ' τ} {D₁ : n ； Γ ⊢ e' ↦ τ'} {D₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ}
                  (υ' : ⌊ τ' ⌋) (υ : ⌊ τ ⌋) (m₁ : MinSyn D₁ υ') (m₂ : MinSyn D₂ υ)
                → IsMinimal (build-extract (mindef υ' υ m₁ m₂))
  minimal-Λ     : ∀ {n Γ e τ} {D : suc n ； shiftΓ (suc zero) Γ ⊢ e ↦ τ}
                  (υ : ⌊ τ ⌋) (m : MinSyn D υ)
                → IsMinimal (build-extract (minΛ υ m))
  minimal-∘     : ∀ {n Γ e₁ e₂ τ τ₁ τ₂}
                    {D₁ : n ； Γ ⊢ e₁ ↦ τ} {eq : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
                    {D₂ : n ； Γ ⊢ e₂ ↤ τ₁}
                  (υ : ⌊ τ₂ ⌋) (m : MinSyn D₁ (unmatch⇒ eq ⊥ₛ υ))
                → IsMinimal (build-extract (min∘ {D₂ = D₂} υ m))
  minimal-<>    : ∀ {n Γ e τ τ' σ}
                    {D : n ； Γ ⊢ e ↦ τ} {eq : τ ⊔ ∀· □ ≡ ∀· τ'} {wf : n ⊢wf σ}
                  (υ : ⌊ [ zero ↦ σ ] τ' ⌋) (m : MinSyn D (unmatch∀ eq (unsub υ)))
                → IsMinimal (build-extract (min<> {wf = wf} υ m))
  minimal-&     : ∀ {n Γ e₁ e₂ τ₁ τ₂}
                    {D₁ : n ； Γ ⊢ e₁ ↦ τ₁} {D₂ : n ； Γ ⊢ e₂ ↦ τ₂}
                  (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋) (m₁ : MinSyn D₁ υ₁) (m₂ : MinSyn D₂ υ₂)
                → IsMinimal (build-extract (min& υ₁ υ₂ m₁ m₂))
  minimal-π₁    : ∀ {n Γ e τ τ₁ τ₂}
                    {D : n ； Γ ⊢ e ↦ τ} {eq : τ ⊔ □ × □ ≡ τ₁ × τ₂}
                  (υ : ⌊ τ₁ ⌋) (m : MinSyn D (unmatch× eq υ ⊥ₛ))
                → IsMinimal (build-extract (minπ₁ υ m))
  minimal-π₂    : ∀ {n Γ e τ τ₁ τ₂}
                    {D : n ； Γ ⊢ e ↦ τ} {eq : τ ⊔ □ × □ ≡ τ₁ × τ₂}
                  (υ : ⌊ τ₂ ⌋) (m : MinSyn D (unmatch× eq ⊥ₛ υ))
                → IsMinimal (build-extract (minπ₂ υ m))
  minimal-case₁ : ∀ {n Γ e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂'}
                    {D : n ； Γ ⊢ e ↦ τ} {eq : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                    (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁') (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
                  (con : τ₁' ~ τ₂')
                  (υ : ⌊ τ₁' ⊔ τ₂' ⌋) (υ₁ : ⌊ τ₁ ⌋)
                  (m₁ : MinSyn D (unmatch+ eq υ₁ ⊥ₛ)) (m₂ : MinSyn D₁ (⊔ₛ-proj₁ con υ))
                → IsMinimal (build-extract (mincase₁ {D₂ = D₂} {con = con} υ υ₁ m₁ m₂))
  minimal-case₂ : ∀ {n Γ e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂'}
                    {D : n ； Γ ⊢ e ↦ τ} {eq : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                  (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁') (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
                  (con : τ₁' ~ τ₂')
                  (υ : ⌊ τ₁' ⊔ τ₂' ⌋) (υ₂ : ⌊ τ₂ ⌋)
                  (m₁ : MinSyn D (unmatch+ eq ⊥ₛ υ₂)) (m₂ : MinSyn D₂ (⊔ₛ-proj₂ con υ))
                → IsMinimal (build-extract (mincase₂ {D₁ = D₁} {con = con} υ υ₂ m₁ m₂))
  minimal-case  : ∀ {n Γ e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂'}
                    {D : n ； Γ ⊢ e ↦ τ} {eq : τ ⊔ □ + □ ≡ τ₁ + τ₂}
                  (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁') (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
                  (con : τ₁' ~ τ₂')
                  (υ : ⌊ τ₁' ⊔ τ₂' ⌋) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
                  (m : MinSyn D (unmatch+ eq υ₁ υ₂))
                  (m₁ : MinSyn D₁ (⊔ₛ-proj₁ con υ)) (m₂ : MinSyn D₂ (⊔ₛ-proj₂ con υ))
                → IsMinimal (build-extract (mincase {con = con} υ υ₁ υ₂ m m₁ m₂))

minimal : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
        → (m : MinSyn D υ) → IsMinimal (build-extract m)
minimal min□ = minimal-□
minimal min* = minimal-*
minimal (minVar υ) = minimal-Var υ
minimal (minλ: υ₁ υ₂ m) = minimal-λ: υ₁ υ₂ m
minimal (mindef υ' υ m₁ m₂) = minimal-def υ' υ m₁ m₂
minimal (minΛ υ m) = minimal-Λ υ m
minimal (min∘ υ m) = minimal-∘ υ m
minimal (min<> υ m) = minimal-<> υ m
minimal (min& υ₁ υ₂ m₁ m₂) = minimal-& υ₁ υ₂ m₁ m₂
minimal (minπ₁ υ m) = minimal-π₁ υ m
minimal (minπ₂ υ m) = minimal-π₂ υ m
minimal (mincase₁ {D₁ = D₁} {D₂ = D₂} {con = con} υ υ₁ m₁ m₂) =
  minimal-case₁ D₁ D₂ con υ υ₁ m₁ m₂
minimal (mincase₂ {D₁ = D₁} {D₂ = D₂} {con = con} υ υ₂ m₁ m₂) =
  minimal-case₂ D₁ D₂ con υ υ₂ m₁ m₂
minimal (mincase {D₁ = D₁} {D₂ = D₂} {con = con} υ υ₁ υ₂ m m₁ m₂) =
  minimal-case D₁ D₂ con υ υ₁ υ₂ m m₁ m₂

-- Soundness: extract a minimal SynSlice from a MinSyn
extract-min : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → MinSyn D υ → IsMinSynSlice D υ
extract-min m = build-extract m , minimal m

-- Completeness: every minimal SynSlice arises from some MinSyn
postulate
  complete : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
             → (s : IsMinSynSlice D υ)
             → Σ[ m ∈ MinSyn D υ ] build-extract m ≈ s .proj₁
