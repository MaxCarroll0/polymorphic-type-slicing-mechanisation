open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; cong) renaming (refl to ≡refl; sym to ≡sym; trans to ≡trans)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.List using (_∷_)
open import Core
open import Semantics.Statics
open import Semantics.Graduality using (syn-unicity; static-gradual-syn; syn-precision)

open import Slicing.Synthesis.Synthesis using (IsMinimal; MinSynSlice_◂_; SynSlice_◂_; _⇑_∈_⊒_; type; valid; syn)
import Slicing.Synthesis.Synthesis as SS
open import Slicing.MinSub using (min-sub; min-sub-valid; min-sub-minimal; unsub-non□; unsub-⊑-body)
open import Slicing.Synthesis.FixedAssmsSynthesis
open import Slicing.Synthesis.BranchPair

module Slicing.Synthesis.FixedAssmsCalc where

⊔-inlₛ : ∀ {τ₁ τ₂ : Typ} → (c : τ₁ ~ τ₂) → ⌊ τ₁ ⌋ → ⌊ τ₁ ⊔ τ₂ ⌋
⊔-inlₛ c s = ↑ (⊑.trans {Typ} (s .proof) (~.⊔-ub₁ c))

⊔-inrₛ : ∀ {τ₁ τ₂ : Typ} → (c : τ₁ ~ τ₂) → ⌊ τ₂ ⌋ → ⌊ τ₁ ⊔ τ₂ ⌋
⊔-inrₛ c s = ↑ (⊑.trans {Typ} (s .proof) (~.⊔-ub₂ c))

-- Fixed-context minimal expression slice calculus
-- D ◂ υ ⤳ σ ↦ ψ ⊣ γ: derivation D explains type query υ via expression σ,
-- actually synthesising ψ (where υ ⊑ₛ ψ), actually using context entries γ.
-- We need to track used context entries to decide how to slice unannotated let bindings and case scrutinees
-- This context (γ) will end up being minimal
infix 4 _◂_⤳_↦_⊣_
data _◂_⤳_↦_⊣_ {n : ℕ} {Γ : Assms} : ∀ {e : Exp} {τ : Typ}
          → (D : n ； Γ ⊢ e ↦ τ) → ⌊ τ ⌋ → ⌊ e ⌋ → ⌊ τ ⌋ → ⌊ Γ ⌋ → Set where

  minVar   : ∀ {n' τ'} (p : Γ at n' ≡ just τ') {υ : ⌊ τ' ⌋}
             → (υ .↓ ≢ □)
             → ↦Var p ◂ υ ⤳ ⊤ₛ ↦ ⊤ₛ ⊣ ⊥ₛ [ p ≔ υ ]ₛ

  min□     : ∀ {e τ} {D : n ； Γ ⊢ e ↦ τ}
             → D ◂ ⊥ₛ ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ

  min*     : ↦* ◂ ⊤ₛ ⤳ ⊤ₛ ↦ ⊤ₛ ⊣ ⊥ₛ

  minλ:    : ∀ {e τ₁ τ₂ υ₁ υ₂ ψ₂ ψ₂' ϕ₁ γ σ₂} {wf : n ⊢wf τ₁}
               {D : n ； (τ₁ ∷ Γ) ⊢ e ↦ τ₂}
             → D ◂ υ₂ ⤳ σ₂ ↦ ψ₂ ⊣ (ϕ₁ ∷ₛ γ)
             → n ； ((ϕ₁ ⊔ₛ υ₁) .↓ ∷ Γ) ⊢ σ₂ .↓ ↦ ψ₂' .↓
             → (↦λ: wf D) ◂ (υ₁ ⇒ₛ υ₂) ⤳ λ:ₛ (ϕ₁ ⊔ₛ υ₁) σ₂ ↦ ((ϕ₁ ⊔ₛ υ₁) ⇒ₛ ψ₂') ⊣ γ

  minΛ     : ∀ {e τ υ ψ' γ' σ-body}
               {D : suc n ； shiftΓ 1 Γ ⊢ e ↦ τ}
             → D ◂ υ ⤳ σ-body ↦ ψ' ⊣ γ'
             → (↦Λ D) ◂ (∀·ₛ υ) ⤳ Λₛ σ-body ↦ (∀·ₛ ψ') ⊣ unshiftΓₛ γ'

  min&     : ∀ {e₁ e₂ τ₁ τ₂ υ₁ υ₂ ψ₁ ψ₂ γ₁ γ₂ σ₁ σ₂}
               {D₁ : n ； Γ ⊢ e₁ ↦ τ₁} {D₂ : n ； Γ ⊢ e₂ ↦ τ₂}
             → D₁ ◂ υ₁ ⤳ σ₁ ↦ ψ₁ ⊣ γ₁ → D₂ ◂ υ₂ ⤳ σ₂ ↦ ψ₂ ⊣ γ₂
             → (↦& D₁ D₂) ◂ (υ₁ ×ₛ υ₂) ⤳ σ₁ &ₛ σ₂ ↦ (ψ₁ ×ₛ ψ₂) ⊣ γ₁ ⊔ₛ γ₂

  min∘     : ∀ {e₁ e₂ τ τ₁ τ₂ ψ₁ γ₁ σ-fn}
               {D₁ : n ； Γ ⊢ e₁ ↦ τ} {m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
               {D₂ : n ； Γ ⊢ e₂ ↤ τ₁}
               {υ : ⌊ τ₂ ⌋}
             → (υ .↓ ≢ □)
             → D₁ ◂ (unmatch⇒ m ⊥ₛ υ) ⤳ σ-fn ↦ ψ₁ ⊣ γ₁
             → (↦∘ D₁ m D₂) ◂ υ ⤳ ∘ₛ σ-fn ⊥ₛ ↦ cod⇒ₛ ψ₁ m ⊣ γ₁

  -- Makes use of min-sub which finds the minimum type argument for a typfun
  min<>    : ∀ {e τ τ' σ ψ₁ γ σ-e}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ ∀· □ ≡ ∀· τ'} {wf : n ⊢wf σ}
               {υ : ⌊ [ zero ↦ σ ] τ' ⌋}
             → (υ .↓ ≢ □)
             → D ◂ (unmatch∀ m (unsub {τ'} {σ} υ)) ⤳ σ-e ↦ ψ₁ ⊣ γ
             → (↦<> D m wf) ◂ υ ⤳ <>ₛ σ-e (min-sub {τ'} υ)
               ↦ subₛ (min-sub {τ'} υ) (body∀ₛ ψ₁ m) ⊣ γ

  -- D₂'s required assumption on def used to slice D₁
  mindef   : ∀ {e' e τ' τ υ₂ υ₁ ψ₁ ψ₂ ψ₂' γ₁ γ₂ σ-body σ-def}
               {D₁ : n ； Γ ⊢ e' ↦ τ'} {D₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ}
             → (υ₂ .↓ ≢ □)
             → D₂ ◂ υ₂ ⤳ σ-body ↦ ψ₂ ⊣ (υ₁ ∷ₛ γ₂)
             → D₁ ◂ υ₁ ⤳ σ-def ↦ ψ₁ ⊣ γ₁
             → n ； (ψ₁ .↓ ∷ Γ) ⊢ σ-body .↓ ↦ ψ₂' .↓
             → (↦def D₁ D₂) ◂ υ₂ ⤳ defₛ σ-def σ-body ↦ ψ₂' ⊣ γ₁ ⊔ₛ γ₂

  minπ₁   : ∀ {e τ τ₁ τ₂ υ ψ₁ γ σ-e}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
             → (υ .↓ ≢ □)
             → D ◂ (unmatch× m υ ⊥ₛ) ⤳ σ-e ↦ ψ₁ ⊣ γ
             → (↦π₁ D m) ◂ υ ⤳ π₁ₛ σ-e ↦ fst×ₛ' ψ₁ m ⊣ γ

  minπ₂   : ∀ {e τ τ₁ τ₂ υ ψ₁ γ σ-e}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
             → (υ .↓ ≢ □)
             → D ◂ (unmatch× m ⊥ₛ υ) ⤳ σ-e ↦ ψ₁ ⊣ γ
             → (↦π₂ D m) ◂ υ ⤳ π₂ₛ σ-e ↦ snd×ₛ ψ₁ m ⊣ γ

  -- mincase variant where optimisation to skip scrutinee slice descent is possible
  mincase-cov
           : ∀ {e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂' ψ₀ ψ₁ ψ₂ υ₁ υ₂ ς₁ ς₂ γ₀ γ₁ γ₂ σ₀ σ₁ σ₂}
               {ϕ₁ : ⌊ τ₁' ⌋} {ϕ₂ : ⌊ τ₂' ⌋}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ + □ ≡ τ₁ + τ₂}
               {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
               {c : τ₁' ~ τ₂'}
               {υ : ⌊ τ₁' ⊔ τ₂' ⌋}
             → (υ .↓ ≢ □)
             → D₁ ◂ υ₁ ⤳ σ₁ ↦ ψ₁ ⊣ ς₁ ∷ₛ γ₁
             → D₂ ◂ υ₂ ⤳ σ₂ ↦ ψ₂ ⊣ ς₂ ∷ₛ γ₂
             → ⊔-inlₛ c υ₁ ⊑ₛ (υ \\ₛ ⊔-inrₛ c ψ₂)
             → ⊔-inrₛ c υ₂ ⊑ₛ (υ \\ₛ ⊔-inlₛ c ψ₁)
             → υ .↓ ⊑ υ₁ .↓ ⊔ υ₂ .↓
             → D ◂ unmatch+-min m ς₁ ς₂ ⤳ σ₀ ↦ ψ₀ ⊣ γ₀
             → n ； (fst+ₛ' ψ₀ m .↓ ∷ Γ) ⊢ σ₁ .↓ ↦ ϕ₁ .↓
             → n ； (snd+ₛ' ψ₀ m .↓ ∷ Γ) ⊢ σ₂ .↓ ↦ ϕ₂ .↓
             → (↦case D m D₁ D₂ c) ◂ υ ⤳ caseₛ σ₀ σ₁ σ₂
               ↦ (ϕ₁ ⊔~ₛ ϕ₂) {c} ⊣ (γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂

  -- TODO: find some way to make minimality of branch contexts internal to this rule
  mincase-desc
           : ∀ {e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂' ς₁ ς₂ ψ₀ ψ₁ ψ₂ υ₁ υ₂ γ₀ γ₁ γ₂ σ₀ σ₁ σ₂}
               {ϕ₁ : ⌊ τ₁' ⌋} {ϕ₂ : ⌊ τ₂' ⌋}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ + □ ≡ τ₁ + τ₂}
               {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
               {c : τ₁' ~ τ₂'}
               {υ : ⌊ τ₁' ⊔ τ₂' ⌋}
             → (υ .↓ ≢ □)
             -- 'Phase 1'
             -- fixed point on branches enforcing irredundancy of branch slices
             → D₁ ◂ υ₁ ⤳ σ₁ ↦ ψ₁ ⊣ γ₁
             → D₂ ◂ υ₂ ⤳ σ₂ ↦ ψ₂ ⊣ γ₂
             → ⊔-inlₛ c υ₁ ⊑ₛ (υ \\ₛ ⊔-inrₛ c ψ₂)
             → ⊔-inrₛ c υ₂ ⊑ₛ (υ \\ₛ ⊔-inlₛ c ψ₁)
             -- 'Phase 2'
             -- calculating the scrutinee slice that provide sufficient assumptions to cover the query
             → n ； (fst+ₛ' ψ₀ m .↓ ∷ Γ) ⊢ σ₁ .↓ ↦ ϕ₁ .↓
             → n ； (snd+ₛ' ψ₀ m .↓ ∷ Γ) ⊢ σ₂ .↓ ↦ ϕ₂ .↓
             → υ .↓ ⊑ ϕ₁ .↓ ⊔ ϕ₂ .↓ -- (coverage)
             → D ◂ unmatch+-min m ς₁ ς₂ ⤳ σ₀ ↦ ψ₀ ⊣ γ₀
             -- Local head minimality: only ranges over expression sub-slices of
             → IsCaseBranchPairMin D m D₁ D₂ σ₀ σ₁ σ₂ υ ψ₀
             -- 'Phase 3' -- Minimal context 
             → (mcc : MinCaseCover D m D₁ D₂ σ₀ σ₁ σ₂ υ)
             → (↦case D m D₁ D₂ c) ◂ υ ⤳ caseₛ σ₀ σ₁ σ₂
               ↦ (ϕ₁ ⊔~ₛ ϕ₂) {c}
               ⊣ proj₁ mcc .γ-out

-- helper lemma
join-project : ∀ {τ : Typ} {a b c d : ⌊ τ ⌋}
  → a ⊑ₛ (b ⊔ₛ c) → c ⊑ₛ d → (a \\ₛ d) ⊑ₛ b
join-project {τ} {a} {b} {c} {d} a⊑b⊔c c⊑d =
  proj₁ (typ-\\-exponential b d a)
        (⊑.trans {Typ} a⊑b⊔c
          (⊑ₛLat.⊔-monotonic {A = Typ} {a = τ} {x = b} {b} {c} {d}
            (⊑.refl {Typ} {b .↓}) c⊑d))

-- Lemmas for minimality proof
⊤⋢⊥ : ∀ {τ : Typ} → τ ≢ □ → (⊤ₛ {a = τ}) ⊑ₛ  (⊥ₛ {a = τ}) → Data.Empty.⊥
⊤⋢⊥ {□} τ≢□ _ = τ≢□ ≡refl

⊑ₛ⊥-inv : ∀ {τ : Typ} {υ : ⌊ τ ⌋} → υ ⊑ₛ (⊥ₛ {a = τ}) → υ .↓ ≡ □
⊑ₛ⊥-inv ⊑□ = ≡refl

*-non□ : ∀ {n Γ} {D : n ； Γ ⊢ * ↦ *}
       → (s' : FixedAssmsSynSlice D ⊤ₛ)
       → (⊤ₛ {a = *}) ⊑ₛ (s' .type)
       → n ； Γ ⊢ s' ↓σ ↦ s' ↓ϕ
       → ⊤ₛ ⊑ₛ (s' .expₛ)
*-non□ s' v d with s' .expₛ
... | □ isSlice ⊑□ with d
... | ↦□ = ⊥-elim (⊤⋢⊥ (λ ()) v)
*-non□ s' v d | * isSlice ⊑* = ⊑*

var-non□ : ∀ {n Γ n' τ'} {υ : ⌊ τ' ⌋}
         → {p : Γ at n' ≡ just τ'}
         → (s' : FixedAssmsSynSlice {n = n} {Γ = Γ} (↦Var p) υ)
         → υ .↓ ≢ □
         → υ ⊑ₛ (s' .type)
         → n ； Γ ⊢ s' ↓σ ↦ s' ↓ϕ
         → ⊤ₛ ⊑ₛ (s' .expₛ)
var-non□ {τ' = τ'} {υ = υ} s' υ≢□ v d with s' .expₛ
... | □ isSlice ⊑□ with d
... | ↦□ = ⊥-elim (υ≢□ (⊑ₛ⊥-inv {τ = τ'} {υ = υ} v))
var-non□ s' υ≢□ v d | ⟨ _ ⟩ isSlice ⊑Var = ⊑Var


-- Extract a MinFixedAssmsSynSlice from a calculus derivation, with proofs that .type ≡ ψ and .expₛ ≡ σ as specified
extract'
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → D ◂ υ ⤳ σ ↦ ψ ⊣ γ
    → Σ[ (s , _) ∈ MinFixedAssmsSynSlice D υ ] s .type ≡ ψ ∧ s .expₛ ≡ σ

extract : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → D ◂ υ ⤳ σ ↦ ψ ⊣ γ → FixedAssmsSynSlice D υ
extract c = proj₁ (proj₁ (extract' c))

extract-minimal
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → (c : D ◂ υ ⤳ σ ↦ ψ ⊣ γ) → IsMinimal (extract c)
extract-minimal c = proj₂ (proj₁ (extract' c))

extract-ψ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → (c : D ◂ υ ⤳ σ ↦ ψ ⊣ γ) → (extract c) .type ≡ ψ
extract-ψ c = proj₁ (proj₂ (extract' c))

extract-σ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → (c : D ◂ υ ⤳ σ ↦ ψ ⊣ γ) → (extract c) .expₛ ≡ σ
extract-σ c = proj₂ (proj₂ (extract' c))

extract-min
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → D ◂ υ ⤳ σ ↦ ψ ⊣ γ → MinFixedAssmsSynSlice D υ
extract-min c = proj₁ (extract' c)

-- The sliced expression σ types under the used context γ
extract-ctx
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → D ◂ υ ⤳ σ ↦ ψ ⊣ γ
    → Σ[ ψ-ctx ∈ ⌊ τ ⌋ ] (n ； γ .↓ ⊢ σ .↓ ↦ ψ-ctx .↓) ∧ (υ ⊑ₛ ψ-ctx)

-- Context minimality
extract-ctx-min
  : ∀ {n Γ Γ' e τ τ'} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → (c : D ◂ υ ⤳ σ ↦ ψ ⊣ γ)
    → n ； Γ' ⊢ σ .↓ ↦ τ'
    → υ .↓ ⊑ τ'
    → Γ' ⊑ Γ
    → γ .↓ ⊑ Γ'

-- Proofs --
-- Extracting a MinAssmsSynSlice from a derivation
-- Base Cases:
extract' (minVar {τ' = τ'} p {υ = υ} υ≢□)
  = (s , min) , ≡refl , ≡refl
  where
    s = ⊤ₛ ⇑ ⊤ₛ ∈ ↦Var p ⊒ ⊤ₛ-max {a = τ'} υ
    min : IsMinimal s
    min s' s'⊑ = ⊑.antisym {Exp} (var-non□ s' υ≢□ (s' .valid) (s' .syn)) s'⊑

extract' min□
  = (s , min) , ≡refl , ≡refl
  where
    s = ⊥ₛ ⇑ ⊥ₛ ∈ ↦□ ⊒ ⊑□
    min : IsMinimal s
    min s' s'⊑ = ⊑.antisym {Exp} (⊑ₛLat.⊥ₛ-min (s' .expₛ)) s'⊑

extract' min*
  = (s , min) , ≡refl , ≡refl
  where
    s = ⊤-fixedassms-syn ↦*
    min : IsMinimal s
    min s' s'⊑ = ⊑.antisym {Exp} (*-non□ s' (s' .valid) (s' .syn)) s'⊑

-- Inductive Cases:
-- λ: τ₁ . e : υ₁ ⇒ υ₂ — body under (ϕ₁ ⊔ υ₁), validity via extract-ctx
extract' (minλ: {υ₁ = υ₁} {ϕ₁ = ϕ₁} {γ = γ} {wf = wf} {D = D} sub d-ann)
  with extract' sub | extract-ctx sub
...  | ((σ₂ ⇑ ψ₂ ∈ d₂ ⊒ v₂) , ih) , ≡refl , ≡refl
     | ψ₂' , d₂' , v₂'
  = let p = syn-precision (⊑∷ (⊑ₛLat.x⊑ₛx⊔ₛy ϕ₁ υ₁) (γ .proof))
              (⊑.refl {Exp}) d-ann d₂'                        -- ψ₂' ⊑ ψ₂'
    in (s p , min p) , ≡refl , ≡refl
  where
    s = λ p → λ:ₛ (ϕ₁ ⊔ₛ υ₁) σ₂
       ⇑ (ϕ₁ ⊔ₛ υ₁) ⇒ₛ _
       ∈ ↦λ: (wf-⊑ wf ((ϕ₁ ⊔ₛ υ₁) .proof)) d-ann
       ⊒ ⊑⇒ (⊑ₛLat.y⊑ₛx⊔ₛy ϕ₁ υ₁) (⊑.trans {Typ} v₂' p)
    min : ∀ p → IsMinimal (s p)
    min p s' s'⊑
      with s' .syn | s' .valid | s' ↓σ⊑ | s' ↓ϕ⊑ | s'⊑
    ... | ↦□ | () | _ | _ | _
    ... | ↦λ: wf' d' | ⊑⇒ v₁' v₂' | ⊑λ p₁ p₂ | _ | ⊑λ e₁⊑ e₂⊑
      with static-gradual-syn (⊑.refl {Assms}) p₂ D           -- Γ ⊢ body' ↦ τ₂'
    ... | _ , d'' , τ₂'⊑
      with ih (↑ p₂ ⇑ ↑ τ₂'⊑ ∈ d''
                 ⊒ ⊑.trans {Typ} v₂'
                     (syn-precision (⊑∷ p₁ (⊑.refl {Assms}))
                       (⊑.refl {Exp}) d'' d')) e₂⊑
    ... | ≡refl
      with static-gradual-syn (⊑∷ p₁ (⊑.refl {Assms}))       -- (ann'∷Γ) ⊢ σ₂ ↦ τ₂''
             (σ₂ .proof) D
    ... | _ , d''' , _
      with extract-ctx-min sub d'''
             (⊑.trans {Typ} v₂'
               (syn-precision (⊑.refl {Assms}) (⊑.refl {Exp}) d''' d'))
             (⊑∷ p₁ (⊑.refl {Assms}))
    ... | ⊑∷ ϕ₁⊑ _
      = cong (λ x → λ: x ⇒ σ₂ .↓)
            (⊑.antisym {Typ}
              (⊑ₛLat.⊔ₛ-least {x = ϕ₁} {y = υ₁} {z = ↑ p₁} ϕ₁⊑ v₁')
              e₁⊑)

extract' (minΛ sub)
  with extract' sub
... | ((σ-body ⇑ ϕ-body ∈ d-body ⊒ v-body) , ih-min) , ≡refl , ≡refl
  = (s , min) , ≡refl , ≡refl
  where
    s = Λₛ σ-body ⇑ ∀·ₛ ϕ-body ∈ ↦Λ d-body ⊒ ⊑∀ v-body
    min : IsMinimal s
    min s' s'⊑
      with s' .syn | s' .valid | s' ↓σ⊑ | s' ↓ϕ⊑ | s'⊑
    ... | ↦□    | ()     | _     | _     | _
    ... | ↦Λ d' | ⊑∀ v' | ⊑Λ p | ⊑∀ q | ⊑Λ e⊑
      with ih-min (↑ p ⇑ ↑ q ∈ d' ⊒ v') e⊑
    ... | ≡refl = ≡refl

extract' (min& s₁ s₂)
  with extract' s₁ | extract' s₂
... | ((σ₁ ⇑ ϕ₁ ∈ d₁ ⊒ v₁) , ih₁) , ≡refl , ≡refl
    | ((σ₂ ⇑ ϕ₂ ∈ d₂ ⊒ v₂) , ih₂) , ≡refl , ≡refl
  = (s , min) , ≡refl , ≡refl
  where
    s = σ₁ &ₛ σ₂ ⇑ ϕ₁ ×ₛ ϕ₂ ∈ ↦& d₁ d₂ ⊒ ⊑× v₁ v₂
    min : IsMinimal s
    min s' s'⊑
      with s' .syn | s' .valid | s' ↓σ⊑ | s' ↓ϕ⊑ | s'⊑
    ... | ↦□          | ()          | _          | _          | _
    ... | ↦& d₁' d₂' | ⊑× v₁' v₂' | ⊑& p₁ p₂  | ⊑× q₁ q₂  | ⊑& e₁⊑ e₂⊑
      with ih₁ (↑ p₁ ⇑ ↑ q₁ ∈ d₁' ⊒ v₁') e₁⊑
         | ih₂ (↑ p₂ ⇑ ↑ q₂ ∈ d₂' ⊒ v₂') e₂⊑
    ... | ≡refl | ≡refl = ≡refl

-- e₁ e₂ : υ — decompose fn type, extract codomain
extract' (min∘ {τ = τ} {τ₂ = τ₂} {D₁ = D₁} {m = m} {υ = υ} υ≢□ sub)
  with extract' sub
... | ((σ₁ ⇑ ψ₁ ∈ d₁ ⊒ v₁) , ih) , ≡refl , ≡refl
  with ⊔-⇒-⊑ v₁ (match⇒ₛ ψ₁ m)
... | _ , _ , m' , _ , v'
  rewrite ≡sym (unmatch⇒-≡-snd {τ} m ⊥ₛ υ m')
  = (s , min) , ≡refl , ≡refl
  where
    s = ∘ₛ σ₁ ⊥ₛ ⇑ cod⇒ₛ ψ₁ m ∈ ↦∘ d₁ (match⇒ₛ ψ₁ m) (↤Sub ↦□ ~?₁) ⊒ v'
    min : IsMinimal s
    min s' s'⊑
      with s' .syn | s' .valid | s' ↓σ⊑ | s' ↓ϕ⊑ | s'⊑
    ... | ↦□              | v'  | _         | _  | _
        = ⊥-elim (υ≢□ (⊑ₛ⊥-inv {υ = υ} v'))
    ... | ↦∘ d₁' m' d₂'  | v'  | ⊑∘ p₁ p₂ | q  | ⊑∘ e₁⊑ ⊑□
      with syn-precision (⊑.refl {Assms}) p₁ D₁ d₁'
    ... | τ₃⊑τ
      with ih (↑ p₁ ⇑ ↑ τ₃⊑τ ∈ d₁' ⊒ unmatch⇒-mono-cod m υ υ≢□ τ₃⊑τ m' v') e₁⊑
    ... | ≡refl = ≡refl

-- e ⟨σ⟩ : υ — decompose ∀ type, substitute
extract' (min<> {τ = τ} {τ' = τ'} {σ = σ} {D = D} {m = m} {wf = wf} {υ = υ} υ≢□ sub)
  with extract' sub
... | ((σ-e ⇑ ψ₁ ∈ d ⊒ v) , ih-min) , ≡refl , ≡refl
  with ⊔-∀-⊑ v (match∀ₛ ψ₁ m)
... | _ , m'' , υ'⊑body
  rewrite ≡sym (unmatch∀-≡ {τ} m _ m'')
  = (s , min) , ≡refl , ≡refl
  where
    s = <>ₛ σ-e (min-sub υ) ⇑ subₛ (min-sub υ) (body∀ₛ ψ₁ m)
        ∈ ↦<> d (match∀ₛ ψ₁ m) (wf-⊑ wf (min-sub υ .proof))
        ⊒ ⊑.trans {Typ} (min-sub-valid υ) (sub-⊑ zero (⊑.refl {Typ}) υ'⊑body)
    ∀·-inj : ∀ {a b : Typ} → ∀· a ≡ ∀· b → a ≡ b
    ∀·-inj ≡refl = ≡refl

    min : IsMinimal s
    min s' s'⊑
      with s' .syn | s' .valid | s' ↓σ⊑ | s' ↓ϕ⊑ | s'⊑
    ... | ↦□              | v'  | _          | _  | _
        = ⊥-elim (υ≢□ (⊑ₛ⊥-inv {υ = υ} v'))
    ... | ↦<> d' m' wf'  | v'  | ⊑<> p₁ p₂ | q  | ⊑<> e⊑ τ⊑
      with syn-precision (⊑.refl {Assms}) p₁ D d'
         | ⊔-∀-⊑ (syn-precision (⊑.refl {Assms}) p₁ D d') m
    ... | τ₃⊑τ | _ , m₃ , τ₃body⊑
      with ih-min (↑ p₁ ⇑ ↑ τ₃⊑τ ∈ d'
                     ⊒ unmatch∀-mono m (unsub υ) (unsub-non□ {τ' = τ'} υ υ≢□)
                         τ₃⊑τ m₃ (unsub-⊑-body {τ' = τ'} υ τ₃⊑τ m₃)) e⊑
    ... | ≡refl
      rewrite ∀·-inj (≡trans (≡sym m₃) m')
      with ⊑.antisym {Typ} (min-sub-minimal υ (↑ p₂) (↑ τ₃body⊑) v') τ⊑
    ... | ≡refl = ≡refl

-- def e₁ in e₂ : υ₂ — body under (ψ₁ ∷ Γ), ctx minimality for def binding
extract' (mindef {υ₂ = υ₂} {υ₁ = υ₁} {γ₂ = γ₂} {D₁ = D₁} {D₂ = D₂} υ≢□ s-body s-def d-def)
  with extract' s-body | extract' s-def | extract-ctx s-body
... | ((σ₂ ⇑ ϕ₂ ∈ d₂ ⊒ v₂) , ih₂) , ≡refl , ≡refl
    | ((σ₁ ⇑ ϕ₁ ∈ d₁ ⊒ v₁) , ih₁) , ≡refl , ≡refl
    | ψ₂' , d₂' , v₂'
  = let p = syn-precision (⊑∷ v₁ (γ₂ .proof))                -- ψ₂' ⊑ ψ₂'
                           (⊑.refl {Exp}) d-def d₂'
    in (s p , min p) , ≡refl , ≡refl
  where
    s = λ p → defₛ σ₁ σ₂ ⇑ _ ∈ ↦def d₁ d-def ⊒ ⊑.trans {Typ} v₂' p
    min : ∀ p → IsMinimal (s p)
    min p s' s'⊑
      with s' .syn | s' .valid | s' ↓σ⊑ | s' ↓ϕ⊑ | s'⊑
    ... | ↦□       | v'        | _      | _      | _
        = ⊥-elim (υ≢□ (⊑ₛ⊥-inv {υ = υ₂} v'))
    ... | ↦def d₁' d₂' | v' | ⊑def p₁ p₂ | q | ⊑def e₁⊑ e₂⊑
      with syn-precision (⊑.refl {Assms}) p₁ D₁ d₁'           -- τ₁' ⊑ τ'
    ... | τ₁'⊑
      with static-gradual-syn (⊑.refl {Assms}) p₂ D₂          -- Γ ⊢ σ₂' ↦ τ₂'
    ... | _ , d₂'' , τ₂'⊑
      with ih₂ (↑ p₂ ⇑ ↑ τ₂'⊑ ∈ d₂''
                  ⊒ ⊑.trans {Typ} v'
                      (syn-precision (⊑∷ τ₁'⊑ (⊑.refl {Assms}))
                        (⊑.refl {Exp}) d₂'' d₂')) e₂⊑
    ... | ≡refl
      with static-gradual-syn (⊑∷ τ₁'⊑ (⊑.refl {Assms}))     -- (τ₁'∷Γ) ⊢ σ₂ ↦ τ₂''
             (σ₂ .proof) D₂
    ... | _ , d₂''' , _
      with extract-ctx-min s-body d₂'''
             (⊑.trans {Typ} v'
               (syn-precision (⊑.refl {Assms}) (⊑.refl {Exp}) d₂''' d₂'))
             (⊑∷ τ₁'⊑ (⊑.refl {Assms}))
    ... | ⊑∷ υ₁⊑ _
      with ih₁ (↑ p₁ ⇑ ↑ τ₁'⊑ ∈ d₁' ⊒ υ₁⊑) e₁⊑
    ... | ≡refl = ≡refl

-- π₁ e : υ — decompose product type, extract fst
extract' (minπ₁ {τ = τ} {τ₁ = τ₁} {υ = υ} {D = D} {m = m} υ≢□ sub)
  with extract' sub
... | ((σ ⇑ ψ₁ ∈ d ⊒ v) , ih-min) , ≡refl , ≡refl
  with ⊔-×-⊑ v (match×ₛ ψ₁ m)
... | _ , _ , m'' , υ⊑fst , _
  rewrite ≡sym (unmatch×-≡-fst {τ} m _ ⊥ₛ m'')
  = (s , min) , ≡refl , ≡refl
  where
    s = π₁ₛ σ ⇑ fst×ₛ' ψ₁ m ∈ ↦π₁ d (match×ₛ ψ₁ m) ⊒ υ⊑fst
    min : IsMinimal s
    min s' s'⊑
      with s' .syn   | s' .valid | s' ↓σ⊑ | s' ↓ϕ⊑ | s'⊑
    ... | ↦□         | v'        | _      | _      | _
        = ⊥-elim (υ≢□ (⊑ₛ⊥-inv {υ = υ} v'))
    ... | ↦π₁ d' m'  | v'        | ⊑π₁ p  | q      | ⊑π₁ e⊑
      with syn-precision (⊑.refl {Assms}) p D d'
    ... | τ₃⊑τ
      with ih-min (↑ p ⇑ ↑ τ₃⊑τ ∈ d' ⊒ unmatch×-mono-fst m υ υ≢□ τ₃⊑τ m' v') e⊑
    ... | ≡refl = ≡refl

-- π₂ e : υ — decompose product type, extract snd
extract' (minπ₂ {τ = τ} {τ₂ = τ₂} {υ = υ} {D = D} {m = m} υ≢□ sub)
  with extract' sub
... | ((σ ⇑ ψ₁ ∈ d ⊒ v) , ih-min) , ≡refl , ≡refl
  with ⊔-×-⊑ v (match×ₛ ψ₁ m)
... | _ , _ , m'' , _ , υ⊑snd
  rewrite ≡sym (unmatch×-≡-snd {τ} m ⊥ₛ _ m'')
  = (s , min) , ≡refl , ≡refl
  where
    s = π₂ₛ σ ⇑ snd×ₛ ψ₁ m ∈ ↦π₂ d (match×ₛ ψ₁ m) ⊒ υ⊑snd
    min : IsMinimal s
    min s' s'⊑
      with s' .syn   | s' .valid | s' ↓σ⊑ | s' ↓ϕ⊑ | s'⊑
    ... | ↦□         | v'        | _      | _      | _
        = ⊥-elim (υ≢□ (⊑ₛ⊥-inv {υ = υ} v'))
    ... | ↦π₂ d' m'  | v'        | ⊑π₂ p  | q      | ⊑π₂ e⊑
      with syn-precision (⊑.refl {Assms}) p D d'
    ... | τ₃⊑τ
      with ih-min (↑ p ⇑ ↑ τ₃⊑τ ∈ d' ⊒ unmatch×-mono-snd m υ υ≢□ τ₃⊑τ m' v') e⊑
    ... | ≡refl = ≡refl

extract' (mincase-cov {τ = τ} {τ₁' = τ₁'} {τ₂' = τ₂'} {ψ₁ = ψ₁} {ψ₂ = ψ₂}
                  {υ₁ = υ₁} {υ₂ = υ₂} {ς₁ = ς₁} {ς₂ = ς₂}
                  {γ₁ = γ₁} {γ₂ = γ₂}
                  {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂}
                  {D = D} {m = m} {D₁ = D₁} {D₂ = D₂} {c = c} {υ = υ}
                  υ≢□ s₁ s₂ z₁ z₂ υ⊑ s-scr d₁-syn d₂-syn)
  with extract' s₁ | extract' s₂ | extract' s-scr
     | extract-ctx s₁ | extract-ctx s₂
... | ((σ₁ ⇑ ψ₁e ∈ d₁ ⊒ v₁) , ih₁) , ≡refl , ≡refl
    | ((σ₂ ⇑ ψ₂e ∈ d₂ ⊒ v₂) , ih₂) , ≡refl , ≡refl
    | ((σ₀ ⇑ ψ₀ ∈ d₀ ⊒ v₀) , ih₀) , ≡refl , ≡refl
    | ψ₁c , d₁c , v₁c
    | ψ₂c , d₂c , v₂c
  = (s , min) , ≡refl , ≡refl
  where
    c' : ϕ₁ .↓ ~ ϕ₂ .↓
    c' = ~-⊑-down c (ϕ₁ .proof) (ϕ₂ .proof)

    -- υ ⊑ υ₁ ⊔ υ₂ ⊑ ψ₁c ⊔ ψ₂c ⊑ ϕ₁ ⊔ ϕ₂:
    ς₁⊑fst : ς₁ .↓ ⊑ fst+ₛ' ψ₀ m .↓
    ς₁⊑fst = fst-unmatch+-min τ m ς₁ ς₂ ψ₀ v₀
    ς₂⊑snd : ς₂ .↓ ⊑ snd+ₛ' ψ₀ m .↓
    ς₂⊑snd = snd-unmatch+-min τ m ς₁ ς₂ ψ₀ v₀

    ψ₁c⊑ϕ₁ : ψ₁c .↓ ⊑ ϕ₁ .↓
    ψ₁c⊑ϕ₁ = syn-precision (⊑∷ ς₁⊑fst (γ₁ .proof))
                            (⊑.refl {Exp}) d₁-syn d₁c
    ψ₂c⊑ϕ₂ : ψ₂c .↓ ⊑ ϕ₂ .↓
    ψ₂c⊑ϕ₂ = syn-precision (⊑∷ ς₂⊑snd (γ₂ .proof))
                            (⊑.refl {Exp}) d₂-syn d₂c

    υ⊑ϕ⊔ : υ .↓ ⊑ ϕ₁ .↓ ⊔ ϕ₂ .↓
    υ⊑ϕ⊔ = ⊑.trans {Typ} υ⊑
             (⊔-mono-⊑ c' (⊑.trans {Typ} v₁c ψ₁c⊑ϕ₁)
                          (⊑.trans {Typ} v₂c ψ₂c⊑ϕ₂))

    s = caseₛ σ₀ σ₁ σ₂
       ⇑ (ϕ₁ ⊔~ₛ ϕ₂) {c}
       ∈ ↦case d₀ (match+ₛ ψ₀ m) d₁-syn d₂-syn c'
       ⊒ υ⊑ϕ⊔

    min : IsMinimal s
    min s' s'⊑
      with s' .syn | s' .valid | s' ↓σ⊑ | s' ↓ϕ⊑ | s'⊑
    ... | ↦□ | v' | _ | _ | _
        = ⊥-elim (υ≢□ (⊑ₛ⊥-inv {υ = υ} v'))
    ... | ↦case d₀' m' d₁' d₂' c'' | v' | ⊑case p₀ p₁ p₂ | q | ⊑case e₀⊑ e₁⊑ e₂⊑
      with syn-precision (⊑.refl {Assms}) p₀ D d₀'
    ... | τ₀⊑
      with syn-precision (⊑.refl {Assms}) e₀⊑ d₀ d₀'
    ... | _
      with ⊔-+-⊑ τ₀⊑ m
    ... | τ₃ , τ₄ , m₃ , τ₃⊑τ₁ , τ₄⊑τ₂
      with ≡refl ← ≡trans (≡sym m₃) m'
      with static-gradual-syn (⊑.refl {Assms}) p₁ D₁
    ... | _ , d-body₁' , τ-hi₁⊑τ₁'
      with static-gradual-syn (⊑.refl {Assms}) p₂ D₂
    ... | _ , d-body₂' , τ-hi₂⊑τ₂'
      with ih₁ (let τ₁c⊑τ₁' = ⊑.trans {Typ}
                        (syn-precision (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms}))
                          (⊑.refl {Exp}) d-body₁' d₁') τ-hi₁⊑τ₁'
                    τ₂c⊑τ₂' = ⊑.trans {Typ}
                        (syn-precision (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms}))
                          (⊑.refl {Exp}) d-body₂' d₂') τ-hi₂⊑τ₂'
                    τ₂c⊑ψ₂ = syn-precision (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms}))
                                e₂⊑ d₂ d₂'
                 in ↑ p₁ ⇑ ↑ τ-hi₁⊑τ₁' ∈ d-body₁'
                  ⊒ ⊑.trans {Typ}
                      (⊑.trans {Typ} z₁
                        (join-project {a = υ} {b = ⊔-inlₛ c (↑ τ₁c⊑τ₁')} {c = ⊔-inrₛ c (↑ τ₂c⊑τ₂')}
                                      {d = ⊔-inrₛ c ψ₂}
                                      v' τ₂c⊑ψ₂))
                      (syn-precision (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms}))
                        (⊑.refl {Exp}) d-body₁' d₁')) e₁⊑
         | ih₂ (let τ₁c⊑τ₁' = ⊑.trans {Typ}
                        (syn-precision (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms}))
                          (⊑.refl {Exp}) d-body₁' d₁') τ-hi₁⊑τ₁'
                    τ₂c⊑τ₂' = ⊑.trans {Typ}
                        (syn-precision (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms}))
                          (⊑.refl {Exp}) d-body₂' d₂') τ-hi₂⊑τ₂'
                    τ₁c⊑ψ₁ = syn-precision (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms}))
                                e₁⊑ d₁ d₁'
                 in ↑ p₂ ⇑ ↑ τ-hi₂⊑τ₂' ∈ d-body₂'
                  ⊒ ⊑.trans {Typ}
                      (⊑.trans {Typ} z₂
                        (join-project {a = υ} {b = ⊔-inrₛ c (↑ τ₂c⊑τ₂')} {c = ⊔-inlₛ c (↑ τ₁c⊑τ₁')}
                                      {d = ⊔-inlₛ c ψ₁}
                                      (subst (υ .↓ ⊑_) (⊑ₛLat.⊔-comm (⊔-inlₛ c (↑ τ₁c⊑τ₁')) (⊔-inrₛ c (↑ τ₂c⊑τ₂'))) v')
                                      τ₁c⊑ψ₁))
                      (syn-precision (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms}))
                        (⊑.refl {Exp}) d-body₂' d₂')) e₂⊑
    ... | ≡refl | ≡refl
      with extract-ctx-min s₁ d₁'
             (⊑.trans {Typ} z₁
               (join-project {a = υ}
                 {b = ⊔-inlₛ c (↑ (⊑.trans {Typ}
                        (syn-precision (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms}))
                          (⊑.refl {Exp}) d-body₁' d₁')
                        τ-hi₁⊑τ₁'))}
                 {c = ⊔-inrₛ c (↑ (⊑.trans {Typ}
                        (syn-precision (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms}))
                          (⊑.refl {Exp}) d-body₂' d₂')
                        τ-hi₂⊑τ₂'))}
                 {d = ⊔-inrₛ c ψ₂}
                 v'
                 (syn-precision (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms}))
                   e₂⊑ d₂ d₂')))
             (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms}))
         | extract-ctx-min s₂ d₂'
             (⊑.trans {Typ} z₂
               (join-project {a = υ}
                 {b = ⊔-inrₛ c (↑ (⊑.trans {Typ}
                        (syn-precision (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms}))
                          (⊑.refl {Exp}) d-body₂' d₂')
                        τ-hi₂⊑τ₂'))}
                 {c = ⊔-inlₛ c (↑ (⊑.trans {Typ}
                        (syn-precision (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms}))
                          (⊑.refl {Exp}) d-body₁' d₁')
                        τ-hi₁⊑τ₁'))}
                 {d = ⊔-inlₛ c ψ₁}
                 (subst (υ .↓ ⊑_)
                   (⊑ₛLat.⊔-comm
                     (⊔-inlₛ c (↑ (⊑.trans {Typ}
                       (syn-precision (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms}))
                         (⊑.refl {Exp}) d-body₁' d₁')
                       τ-hi₁⊑τ₁')))
                     (⊔-inrₛ c (↑ (⊑.trans {Typ}
                       (syn-precision (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms}))
                         (⊑.refl {Exp}) d-body₂' d₂')
                       τ-hi₂⊑τ₂'))))
                   v')
                 (syn-precision (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms}))
                   e₁⊑ d₁ d₁')))
             (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms}))
    ... | ⊑∷ ς₁⊑τ₃' _ | ⊑∷ ς₂⊑τ₄' _
      with ih₀ (↑ p₀ ⇑ ↑ τ₀⊑ ∈ d₀'
                  ⊒ unmatch+-min-⊑ τ m ς₁ ς₂ τ₀⊑ m' ς₁⊑τ₃' ς₂⊑τ₄') e₀⊑
    ... | ≡refl = ≡refl

extract' (mincase-desc {τ = τ} {τ₁' = τ₁'} {τ₂' = τ₂'} {ς₁ = ς₁} {ς₂ = ς₂}
                  {ψ₁ = ψ₁} {ψ₂ = ψ₂}
                  {υ₁ = υ₁} {υ₂ = υ₂}
                  {γ₁ = γ₁} {γ₂ = γ₂}
                  {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂}
                  {D = D} {m = m} {D₁ = D₁} {D₂ = D₂} {c = c} {υ = υ}
                  υ≢□ s₁ s₂ z₁ z₂ d₁-syn d₂-syn υ⊑ϕ⊔
                  s-scr head-min (cov , min-cov))
  with extract' s₁ | extract' s₂ | extract' s-scr
... | ((σ₁ ⇑ ψ₁e ∈ d₁ ⊒ v₁) , ih₁) , ≡refl , ≡refl
    | ((σ₂ ⇑ ψ₂e ∈ d₂ ⊒ v₂) , ih₂) , ≡refl , ≡refl
    | ((σ₀ ⇑ ψ₀ ∈ d₀ ⊒ v₀) , ih₀) , ≡refl , ≡refl
  = (s , min) , ≡refl , ≡refl
  where
    c' : ϕ₁ .↓ ~ ϕ₂ .↓
    c' = ~-⊑-down c (ϕ₁ .proof) (ϕ₂ .proof)

    s = caseₛ σ₀ σ₁ σ₂
       ⇑ (ϕ₁ ⊔~ₛ ϕ₂) {c}
       ∈ ↦case d₀ (match+ₛ ψ₀ m) d₁-syn d₂-syn c'
       ⊒ υ⊑ϕ⊔

    min : IsMinimal s
    min s' s'⊑
      with s' .syn | s' .valid | s' ↓σ⊑ | s' ↓ϕ⊑ | s'⊑
    ... | ↦□ | v' | _ | _ | _
        = ⊥-elim (υ≢□ (⊑ₛ⊥-inv {υ = υ} v'))
    ... | ↦case d₀' m' d₁' d₂' c'' | v' | ⊑case p₀ p₁ p₂ | q | ⊑case e₀⊑ e₁⊑ e₂⊑
      with syn-precision (⊑.refl {Assms}) p₀ D d₀' -- τ₀ ⊑ τ
    ... | τ₀⊑
      with syn-precision (⊑.refl {Assms}) e₀⊑ d₀ d₀' -- τ₀ ⊑ ψ₀ .↓
    ... | τ₀⊑ψ₀
      with ⊔-+-⊑ τ₀⊑ m
    ... | τ₃ , τ₄ , m₃ , τ₃⊑τ₁ , τ₄⊑τ₂ -- m₃ : τ₀ ⊔ □+□ ≡ τ₃ + τ₄
      with ≡refl ← ≡trans (≡sym m₃) m' -- m' = m₃
      with static-gradual-syn (⊑.refl {Assms}) p₁ D₁
    ... | _ , d-body₁' , τ-hi₁⊑τ₁' -- d-body₁' : (τ₁ ∷ Γ) ⊢ σ₁' ↦ τ-hi₁
      with static-gradual-syn (⊑.refl {Assms}) p₂ D₂
    ... | _ , d-body₂' , τ-hi₂⊑τ₂' -- d-body₂' : (τ₂ ∷ Γ) ⊢ σ₂' ↦ τ-hi₂
      with ih₁ (let τ₁c⊑τ₁' = ⊑.trans {Typ}
                        (syn-precision (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms}))
                          (⊑.refl {Exp}) d-body₁' d₁') τ-hi₁⊑τ₁'
                    τ₂c⊑τ₂' = ⊑.trans {Typ}
                        (syn-precision (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms}))
                          (⊑.refl {Exp}) d-body₂' d₂') τ-hi₂⊑τ₂'
                    τ₂c⊑ψ₂ = syn-precision (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms}))
                                e₂⊑ d₂ d₂'
                 in ↑ p₁ ⇑ ↑ τ-hi₁⊑τ₁' ∈ d-body₁'
                  ⊒ ⊑.trans {Typ}
                      (⊑.trans {Typ} z₁
                        (join-project {a = υ} {b = ⊔-inlₛ c (↑ τ₁c⊑τ₁')} {c = ⊔-inrₛ c (↑ τ₂c⊑τ₂')}
                                      {d = ⊔-inrₛ c ψ₂}
                                      v' τ₂c⊑ψ₂))
                      (syn-precision (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms}))
                        (⊑.refl {Exp}) d-body₁' d₁')) e₁⊑
         | ih₂ (let τ₁c⊑τ₁' = ⊑.trans {Typ}
                        (syn-precision (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms}))
                          (⊑.refl {Exp}) d-body₁' d₁') τ-hi₁⊑τ₁'
                    τ₂c⊑τ₂' = ⊑.trans {Typ}
                        (syn-precision (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms}))
                          (⊑.refl {Exp}) d-body₂' d₂') τ-hi₂⊑τ₂'
                    τ₁c⊑ψ₁ = syn-precision (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms}))
                                e₁⊑ d₁ d₁'
                 in ↑ p₂ ⇑ ↑ τ-hi₂⊑τ₂' ∈ d-body₂'
                  ⊒ ⊑.trans {Typ}
                      (⊑.trans {Typ} z₂
                        (join-project {a = υ} {b = ⊔-inrₛ c (↑ τ₂c⊑τ₂')} {c = ⊔-inlₛ c (↑ τ₁c⊑τ₁')}
                                      {d = ⊔-inlₛ c ψ₁}
                                      (subst (υ .↓ ⊑_) (⊑ₛLat.⊔-comm (⊔-inlₛ c (↑ τ₁c⊑τ₁')) (⊔-inrₛ c (↑ τ₂c⊑τ₂'))) v')
                                      τ₁c⊑ψ₁))
                      (syn-precision (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms}))
                        (⊑.refl {Exp}) d-body₂' d₂')) e₂⊑
    ... | ≡refl | ≡refl
      -- Apply local head-min-witness with σ₀' = competitor scrutinee (from e₀⊑).
      -- Need typings of σ₁ .↓ / σ₂ .↓ (rule's branches) at (τ₃ ∷ Γ), (τ₄ ∷ Γ).
      -- Lift competitor's d₁'/d₂' (typing σ₁'/σ₂') to D₁/D₂ images of σ_i .↓.
      with static-gradual-syn (⊑∷ τ₃⊑τ₁ (⊑.refl {Assms})) (σ₁ .proof) D₁
         | static-gradual-syn (⊑∷ τ₄⊑τ₂ (⊑.refl {Assms})) (σ₂ .proof) D₂
    ... | _ , d₁-fst , p₁-fst | _ , d₂-snd , p₂-snd
      with υ-cov-lifted ← ⊑.trans {Typ} v'
                            (⊔-mono-⊑ (~-⊑-down c p₁-fst p₂-snd)
                               (syn-precision (⊑.refl {Assms}) e₁⊑ d₁-fst d₁')
                               (syn-precision (⊑.refl {Assms}) e₂⊑ d₂-snd d₂'))
      with τ₃≡fst , τ₄≡snd ← head-min-witness head-min e₀⊑ d₀' m' d₁-fst d₂-snd υ-cov-lifted
      with ih₀ (↑ p₀ ⇑ ↑ τ₀⊑ ∈ d₀'
                  ⊒ unmatch+-min-⊑ τ m ς₁ ς₂ τ₀⊑ m'
                      (subst (λ x → ς₁ .↓ ⊑t x) (≡sym τ₃≡fst)
                         (fst-unmatch+-min τ m ς₁ ς₂ ψ₀ v₀))
                      (subst (λ x → ς₂ .↓ ⊑t x) (≡sym τ₄≡snd)
                         (snd-unmatch+-min τ m ς₁ ς₂ ψ₀ v₀))) e₀⊑
    ... | ≡refl = ≡refl

-- Verify the proposed minimal context is a valid context
-- Base Cases:
extract-ctx (minVar {n' = n'} {τ' = τ'} p {υ = υ} _) = υ , ↦Var (≔ₛ-↓ {k = n'} ⊥ₛ p υ) , ⊑.refl {Typ}
extract-ctx min□ = ⊥ₛ , ↦□ , ⊑□
extract-ctx min* = ⊤ₛ , ↦* , ⊑*

-- Inductive cases:
-- Λ e : ∀· υ — wrap body result
extract-ctx (minΛ {γ' = γ'} sub)
  with extract-ctx sub
... | ψ' , d' , v'
  = ∀·ₛ ψ' , ↦Λ (subst (λ Γ' → _ ； Γ' ⊢ _ ↦ _) (≡sym (shift-unshiftΓ {a = 1} (γ' .↓) (γ' .proof))) d') , ⊑∀ v'

-- e₁ & e₂ : υ₁ × υ₂ — lift sub-derivations to γ₁ ⊔ γ₂
extract-ctx {σ = σ} (min& {γ₁ = γ₁} {γ₂ = γ₂} {D₁ = D₁} {D₂ = D₂} s₁ s₂)
  with extract-ctx s₁ | extract-ctx s₂ | σ .proof
... | ψ₁ , d₁ , v₁ | ψ₂ , d₂ , v₂ | ⊑& σ₁⊑ σ₂⊑
  with static-gradual-syn ((γ₁ ⊔ₛ γ₂) .proof) σ₁⊑ D₁  -- γ₁⊔γ₂ ⊢ σ₁ ↦ τ₁'
     | static-gradual-syn ((γ₁ ⊔ₛ γ₂) .proof) σ₂⊑ D₂  -- γ₁⊔γ₂ ⊢ σ₂ ↦ τ₂'
... | _ , d₁' , p₁ | _ , d₂' , p₂
  = ↑ p₁ ×ₛ ↑ p₂ , ↦& d₁' d₂'
  , ⊑× (⊑.trans {Typ} v₁
          (syn-precision (⊑ₛLat.x⊑ₛx⊔ₛy γ₁ γ₂) (⊑.refl {Exp}) d₁' d₁))
       (⊑.trans {Typ} v₂
          (syn-precision (⊑ₛLat.y⊑ₛx⊔ₛy γ₁ γ₂) (⊑.refl {Exp}) d₂' d₂))

-- e₁ e₂ : υ — decompose fn type, extract codomain
extract-ctx (min∘ {τ = τ} {m = m} {υ = υ} υ≢□ sub)
  with extract-ctx sub
... | ψ' , d' , v'
  with ⊔-⇒-⊑ v' (match⇒ₛ ψ' m)
... | _ , _ , m' , _ , v''
  rewrite ≡sym (unmatch⇒-≡-snd {τ} m ⊥ₛ υ m')
  = cod⇒ₛ ψ' m , ↦∘ d' (match⇒ₛ ψ' m) (↤Sub ↦□ ~?₁) , v''

-- e ⟨σ⟩ : υ — decompose ∀ type, substitute
extract-ctx (min<> {τ = τ} {m = m} {wf = wf} {υ = υ} υ≢□ sub)
  with extract-ctx sub
... | ψ' , d' , v'
  with ⊔-∀-⊑ v' (match∀ₛ ψ' m)
... | _ , m' , v''
  rewrite ≡sym (unmatch∀-≡ {τ} m _ m')
  = subₛ (min-sub υ) (body∀ₛ ψ' m)
  , ↦<> d' (match∀ₛ ψ' m) (wf-⊑ wf (min-sub υ .proof))
  , ⊑.trans {Typ} (min-sub-valid υ) (sub-⊑ zero (⊑.refl {Typ}) v'')

-- λ: τ₁ . e : υ₁ ⇒ υ₂ — body under (ϕ₁ ⊔ υ₁ ∷ γ), lift annotation to Γ
extract-ctx (minλ: {υ₁ = υ₁} {ψ₂' = ψ₂'} {ϕ₁ = ϕ₁} {γ = γ} {σ₂ = σ₂} {wf = wf} sub d-ann)
  with extract-ctx sub
... | ψ' , d' , v'                                          -- ϕ₁∷γ ⊢ σ₂ ↦ ψ'
  with static-gradual-syn (⊑∷ (⊑.refl {Typ}) (γ .proof))   -- (ϕ₁⊔υ₁ ∷ Γ) ⊢ σ₂ ↦ ψ''
         (⊑.refl {Exp}) d-ann
... | _ , d'' , p''
  = (ϕ₁ ⊔ₛ υ₁) ⇒ₛ (↑ (⊑.trans {Typ} p'' (ψ₂' .proof)))
  , ↦λ: (wf-⊑ wf ((ϕ₁ ⊔ₛ υ₁) .proof)) d''
  , ⊑⇒ (⊑ₛLat.y⊑ₛx⊔ₛy ϕ₁ υ₁)
       (⊑.trans {Typ} v'
         (syn-precision (⊑∷ (⊑ₛLat.x⊑ₛx⊔ₛy ϕ₁ υ₁) (⊑.refl {Assms}))
           (⊑.refl {Exp}) d'' d'))

-- def e₁ in e₂ : υ₂ — lift def and body to γ₁ ⊔ γ₂
extract-ctx (mindef {γ₁ = γ₁} {γ₂ = γ₂} {σ-body = σ-body} {σ-def = σ-def} {D₁ = D₁} {D₂ = D₂} _ s-body s-def d-def)
  with extract-ctx s-body | extract-ctx s-def
... | ψ₂ , d₂ , v₂ | ψ₁ , d₁ , v₁                           -- γ₂ ⊢ σ₂ ↦ ψ₂, γ₁ ⊢ σ₁ ↦ ψ₁
  with static-gradual-syn ((γ₁ ⊔ₛ γ₂) .proof)               -- γ₁⊔γ₂ ⊢ σ₁ ↦ τ₁'
         (σ-def .proof) D₁
... | _ , d₁' , p₁
  with static-gradual-syn (⊑∷ p₁ ((γ₁ ⊔ₛ γ₂) .proof))       -- (τ₁' ∷ γ₁⊔γ₂) ⊢ σ₂ ↦ τ₂'
         (σ-body .proof) D₂
... | _ , d₂' , p₂
  = ↑ p₂ , ↦def d₁' d₂'
  , ⊑.trans {Typ} v₂                                        -- υ₂ ⊑ ψ₂ ⊑ τ₂'
      (syn-precision (⊑∷ (⊑.trans {Typ} v₁
        (syn-precision (⊑ₛLat.x⊑ₛx⊔ₛy γ₁ γ₂)
          (⊑.refl {Exp}) d₁' d₁))
        (⊑ₛLat.y⊑ₛx⊔ₛy γ₁ γ₂))
        (⊑.refl {Exp}) d₂' d₂)

-- π₁ e : υ — decompose product type, extract fst
extract-ctx (minπ₁ {τ = τ} {υ = υ} {m = m} υ≢□ sub)
  with extract-ctx sub
... | ψ' , d' , v'
  with ⊔-×-⊑ v' (match×ₛ ψ' m)
... | _ , _ , m' , v'' , _
  rewrite ≡sym (unmatch×-≡-fst {τ} m _ ⊥ₛ m')
  = fst×ₛ' ψ' m , ↦π₁ d' (match×ₛ ψ' m) , v''

-- π₂ e : υ — decompose product type, extract snd
extract-ctx (minπ₂ {τ = τ} {υ = υ} {m = m} υ≢□ sub)
  with extract-ctx sub
... | ψ' , d' , v'
  with ⊔-×-⊑ v' (match×ₛ ψ' m)
... | _ , _ , m' , _ , v''
  rewrite ≡sym (unmatch×-≡-snd {τ} m ⊥ₛ _ m')
  = snd×ₛ ψ' m , ↦π₂ d' (match×ₛ ψ' m) , v''

-- case e of e₁ · e₂ : υ — lift scrutinee and branches to (γ₀ ⊔ γ₁) ⊔ γ₂
extract-ctx (mincase-cov {τ = τ} {ς₁ = ς₁} {ς₂ = ς₂}
                    {γ₀ = γ₀} {γ₁ = γ₁} {γ₂ = γ₂}
                    {σ₀ = σ₀} {σ₁ = σ₁} {σ₂ = σ₂}
                    {D = D} {m = m} {D₁ = D₁} {D₂ = D₂} {c = c} {υ = υ}
                    _ s₁ s₂ _ _ υ⊑ s-scrut _ _)
  with extract-ctx s₁ | extract-ctx s₂ | extract-ctx s-scrut
... | ψ₁c , d₁ , v₁ -- (ς₁ ∷ γ₁) ⊢ σ₁ ↦ ψ₁c, υ₁ ⊑ ψ₁c
    | ψ₂c , d₂ , v₂
    | ψ₀ , d₀ , v₀
  with static-gradual-syn (((γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂) .proof)
         (σ₀ .proof) D
... | τ₀ , d₀' , p₀
  with ⊔-+-⊑ p₀ m
... | τa , τb , m' , pa , pb
  with static-gradual-syn (⊑∷ pa (((γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂) .proof)) (σ₁ .proof) D₁
     | static-gradual-syn (⊑∷ pb (((γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂) .proof)) (σ₂ .proof) D₂
... | τl , dl , pl | τr , dr , pr
  = ↑ (⊔-mono-⊑ c pl pr)
  , ↦case d₀' m' dl dr c''
  , ⊑.trans {Typ} υ⊑ (⊔-mono-⊑ c'' υ₁⊑τl υ₂⊑τr)
  where
    open ⊑ {A = Typ}
    c'' = ~-⊑-down c pl pr
    γ₁⊑ = ⊑.trans {Assms} (⊑ₛLat.y⊑ₛx⊔ₛy γ₀ γ₁)
           (⊑ₛLat.x⊑ₛx⊔ₛy (γ₀ ⊔ₛ γ₁) γ₂)
    γ₂⊑ = ⊑ₛLat.y⊑ₛx⊔ₛy (γ₀ ⊔ₛ γ₁) γ₂
    γ₀⊑ = ⊑.trans {Assms} (⊑ₛLat.x⊑ₛx⊔ₛy γ₀ γ₁)
          (⊑ₛLat.x⊑ₛx⊔ₛy (γ₀ ⊔ₛ γ₁) γ₂)
    q₀  = syn-precision γ₀⊑ (⊑.refl {Exp}) d₀' d₀
    ς₁⊑ = ⊑.trans {Typ} (fst-unmatch+-min τ m ς₁ ς₂ ψ₀ v₀)
            (fst+ₛ'-⊔ ψ₀ m q₀ m')
    ς₂⊑ = ⊑.trans {Typ} (snd-unmatch+-min τ m ς₁ ς₂ ψ₀ v₀)
            (snd+ₛ'-⊔ ψ₀ m q₀ m')
    -- v₁ : υ₁ ⊑ ψ₁c (extract-ctx of s₁ at (ς₁ ∷ γ₁)). Lift via syn-precision.
    υ₁⊑τl = ⊑.trans {Typ} v₁
              (syn-precision (⊑∷ ς₁⊑ γ₁⊑) (⊑.refl {Exp}) dl d₁)
    υ₂⊑τr = ⊑.trans {Typ} v₂
              (syn-precision (⊑∷ ς₂⊑ γ₂⊑) (⊑.refl {Exp}) dr d₂)

extract-ctx (mincase-desc {τ = τ}
                    {σ₀ = σ₀} {σ₁ = σ₁} {σ₂ = σ₂}
                    {D = D} {m = m} {D₁ = D₁} {D₂ = D₂} {c = c} {υ = υ}
                    _ _ _ _ _ _ _ _ _ _ (cov , _))
  -- The cover packages a case typing at cov.γ-out directly.
  with syn-precision ((cov .γ-out) .proof) (σ₀ .proof) D (cov .d-scr)
... | τ-scr⊑τ
  with ⊔-+-⊑ τ-scr⊑τ m
... | _ , _ , m'' , τ-h₁⊑τ₁ , τ-h₂⊑τ₂
  with ≡refl ← ≡trans (≡sym m'') (cov .m-h)
  with τ-c₁⊑τ₁' ← syn-precision (⊑∷ τ-h₁⊑τ₁ ((cov .γ-out) .proof))
                     (σ₁ .proof) D₁ (cov .d-br₁)
     | τ-c₂⊑τ₂' ← syn-precision (⊑∷ τ-h₂⊑τ₂ ((cov .γ-out) .proof))
                     (σ₂ .proof) D₂ (cov .d-br₂)
  = ↑ (⊔-mono-⊑ c τ-c₁⊑τ₁' τ-c₂⊑τ₂')
  , ↦case (cov .d-scr) (cov .m-h) (cov .d-br₁) (cov .d-br₂)
          (~-⊑-down c τ-c₁⊑τ₁' τ-c₂⊑τ₂')
  , cov .valid

-- Context minimality proof
-- Base cases
extract-ctx-min {Γ = Γ} min□ d' v Γ'⊑ = ⊑ₛLat.⊥ₛ-min {A = Assms} {a = Γ} (↑ Γ'⊑)
extract-ctx-min {Γ = Γ} min* d' v Γ'⊑ = ⊑ₛLat.⊥ₛ-min {A = Assms} {a = Γ} (↑ Γ'⊑)

extract-ctx-min (minVar {n' = n'} {τ' = τ'} p {υ = υ} υ≢□) (↦Var p') v Γ'⊑
  = ⊥ₛ-≔-min υ Γ'⊑ p p' v
  where
    ⊥ₛ-≔-min : ∀ {Γ Γ' : Assms} {k : ℕ} {τ τ'}
              → (υ' : ⌊ τ ⌋)
              → Γ' ⊑ Γ → (p : Γ at k ≡ just τ) → Γ' at k ≡ just τ'
              → υ' .↓ ⊑ τ'
              → (⊥ₛ {A = Assms} {a = Γ} [ p ≔ υ' ]ₛ) .↓ ⊑ Γ'
    ⊥ₛ-≔-min {k = zero} υ' (⊑∷ _ t) ≡refl ≡refl v' = ⊑∷ v' (⊑ₛLat.⊥ₛ-min {A = Assms} (↑ t))
    ⊥ₛ-≔-min {k = suc _} υ' (⊑∷ _ t) p₁ p₂ v' = ⊑∷ ⊑□ (⊥ₛ-≔-min υ' t p₁ p₂ v')

-- Structural cases
extract-ctx-min (minΛ sub) (↦Λ d') (⊑∀ v') Γ'⊑
  with extract-ctx-min sub d' v' (shiftΓ-⊑ Γ'⊑)
... | ih = unshiftΓ-shiftΓ-⊑ ih

extract-ctx-min (min& {γ₁ = γ₁} {γ₂ = γ₂} s₁ s₂) (↦& d₁' d₂') v Γ'⊑
  with v
... | ⊑× v₁ v₂
  = ⊑ₛLat.⊔ₛ-least {A = Assms} {x = γ₁} {y = γ₂} {z = ↑ Γ'⊑}
      (extract-ctx-min s₁ d₁' v₁ Γ'⊑)
      (extract-ctx-min s₂ d₂' v₂ Γ'⊑)

extract-ctx-min (minλ: {υ₁ = υ₁} {ϕ₁ = ϕ₁} {γ = γ} {σ₂ = σ₂} sub d-ann) (↦λ: wf' d-body') (⊑⇒ v₁ v₂) Γ'⊑
  with extract-ctx-min sub d-body' v₂ (⊑∷ ((ϕ₁ ⊔ₛ υ₁) .proof) Γ'⊑)
... | ⊑∷ _ γ⊑ = γ⊑

-- Elimination cases
extract-ctx-min (min∘ {σ-fn = σ-fn} {D₁ = D₁} {m = m} {υ = υ} υ≢□ sub) (↦∘ d₁' m' d₂') v Γ'⊑
  with syn-precision Γ'⊑ (σ-fn .proof) D₁ d₁'
... | τ-fn⊑
  = extract-ctx-min sub d₁' (unmatch⇒-mono-cod m υ υ≢□ τ-fn⊑ m' v) Γ'⊑

extract-ctx-min (minπ₁ {υ = υ} {σ-e = σ-e} {D = D} {m = m} υ≢□ sub) (↦π₁ d' m') v Γ'⊑
  with syn-precision Γ'⊑ (σ-e .proof) D d'
... | τ⊑
  = extract-ctx-min sub d' (unmatch×-mono-fst m υ υ≢□ τ⊑ m' v) Γ'⊑

extract-ctx-min (minπ₂ {υ = υ} {σ-e = σ-e} {D = D} {m = m} υ≢□ sub) (↦π₂ d' m') v Γ'⊑
  with syn-precision Γ'⊑ (σ-e .proof) D d'
... | τ⊑
  = extract-ctx-min sub d' (unmatch×-mono-snd m υ υ≢□ τ⊑ m' v) Γ'⊑

extract-ctx-min (min<> {τ' = τ'} {σ = σ} {σ-e = σ-e} {D = D} {m = m} {υ = υ} υ≢□ sub) (↦<> d' m' wf') v Γ'⊑
  with syn-precision Γ'⊑ (σ-e .proof) D d'
... | τ⊑
  with ⊔-∀-⊑ τ⊑ m
... | _ , m₃ , τ₃body⊑
  = extract-ctx-min sub d'
      (unmatch∀-mono m (unsub {τ'} υ) (unsub-non□ {τ' = τ'} υ υ≢□) τ⊑ m₃ (unsub-⊑-body {τ' = τ'} υ τ⊑ m₃))
      Γ'⊑

extract-ctx-min (mindef {γ₁ = γ₁} {γ₂ = γ₂} {σ-def = σ-def} {D₁ = D₁} υ≢□ s-body s-def d-def) (↦def d₁' d₂') v Γ'⊑
  with syn-precision Γ'⊑ (σ-def .proof) D₁ d₁'
... | τ₁'⊑
  with extract-ctx-min s-body d₂' v (⊑∷ τ₁'⊑ Γ'⊑)
... | ⊑∷ υ₁⊑ γ₂⊑
  with extract-ctx-min s-def d₁' υ₁⊑ Γ'⊑
... | γ₁⊑
  = ⊑ₛLat.⊔ₛ-least {A = Assms} {x = γ₁} {y = γ₂} {z = ↑ Γ'⊑} γ₁⊑ γ₂⊑

extract-ctx-min (mincase-cov {τ = τ} {ψ₁ = ψ₁} {ψ₂ = ψ₂} {ς₁ = ς₁} {ς₂ = ς₂}
                         {γ₀ = γ₀} {γ₁ = γ₁} {γ₂ = γ₂} {σ₀ = σ₀}
                         {D = D} {m = m} {c = c} {υ = υ}
                         υ≢□ cs₁ cs₂ z₁ z₂ _ cs₀ _ _)
                (↦case d₀' m' db₁' db₂' c'') v Γ'⊑
  with syn-precision Γ'⊑ (σ₀ .proof) D d₀'
... | τ₀⊑
  with ⊔-+-⊑ τ₀⊑ m
... | τ₃ , τ₄ , m₃ , τ₃⊑τ₁ , τ₄⊑τ₂
  with ≡refl ← ≡trans (≡sym m₃) m'
  with extract cs₁ | extract-ψ cs₁ | extract-σ cs₁
     | extract cs₂ | extract-ψ cs₂ | extract-σ cs₂
... | ec₁ | ≡refl | ≡refl | ec₂ | ≡refl | ≡refl
  with ⊑.trans {Typ}
         (syn-precision (⊑∷ τ₃⊑τ₁ Γ'⊑) (⊑.refl {Exp}) (ec₁ .syn) db₁')
         (ec₁ .type .proof)
     | ⊑.trans {Typ}
         (syn-precision (⊑∷ τ₄⊑τ₂ Γ'⊑) (⊑.refl {Exp}) (ec₂ .syn) db₂')
         (ec₂ .type .proof)
... | τc1⊑τ₁' | τc2⊑τ₂'
  with syn-precision (⊑∷ τ₃⊑τ₁ Γ'⊑) (⊑.refl {Exp}) (ec₁ .syn) db₁'
     | syn-precision (⊑∷ τ₄⊑τ₂ Γ'⊑) (⊑.refl {Exp}) (ec₂ .syn) db₂'
... | τc1⊑ψ1 | τc2⊑ψ2
  with ⊑.trans {Typ} z₁
        (join-project {a = υ}
                      {b = ⊔-inlₛ c (↑ τc1⊑τ₁')} {c = ⊔-inrₛ c (↑ τc2⊑τ₂')}
                      {d = ⊔-inrₛ c ψ₂}
                      v τc2⊑ψ2)
     | ⊑.trans {Typ} z₂
        (join-project {a = υ}
                      {b = ⊔-inrₛ c (↑ τc2⊑τ₂')} {c = ⊔-inlₛ c (↑ τc1⊑τ₁')}
                      {d = ⊔-inlₛ c ψ₁}
                      (subst (υ .↓ ⊑_)
                             (⊑ₛLat.⊔-comm (⊔-inlₛ c (↑ τc1⊑τ₁')) (⊔-inrₛ c (↑ τc2⊑τ₂')))
                             v)
                      τc1⊑ψ1)
... | υ₁⊑τc1 | υ₂⊑τc2
  with extract-ctx-min cs₁ db₁' υ₁⊑τc1 (⊑∷ τ₃⊑τ₁ Γ'⊑)
     | extract-ctx-min cs₂ db₂' υ₂⊑τc2 (⊑∷ τ₄⊑τ₂ Γ'⊑)
... | ⊑∷ ς₁'⊑ γ₁⊑ | ⊑∷ ς₂'⊑ γ₂⊑
  with extract-ctx-min cs₀ d₀' (unmatch+-min-⊑ τ m ς₁ ς₂ τ₀⊑ m' ς₁'⊑ ς₂'⊑) Γ'⊑
... | γ₀⊑
  = ⊑ₛLat.⊔ₛ-least {A = Assms} {x = γ₀ ⊔ₛ γ₁} {y = γ₂} {z = ↑ Γ'⊑}
      (⊑ₛLat.⊔ₛ-least {A = Assms} {x = γ₀} {y = γ₁} {z = ↑ Γ'⊑} γ₀⊑ γ₁⊑) γ₂⊑

-- ctx minimality currently external to the rule
extract-ctx-min (mincase-desc
                         _ _ _ _ _ _ _ _ _ _ (cov , min-cov))
                (↦case d₀' m' db₁' db₂' c'') v Γ'⊑
  = min-cov Γ'⊑ d₀' m' db₁' db₂' v


-- Final soundness corollary:
-- Extract the derivation to a MinFixedAssmsSynSlice,
-- then use minimality of γ to construct a MinSynSlice
soundness : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → (c : D ◂ υ ⤳ σ ↦ ψ ⊣ γ)
    → MinSynSlice D ◂ υ
soundness {D = D} {υ = υ} {γ = γ} c
  with extract' c | extract-ctx c
... | ((σₛ ⇑ ψₛ ∈ d ⊒ v) , ih-exp) , ≡refl , ≡refl
    | ψ-ctx , d-ctx , υ⊑ctx
  = s , min
  where
    s : SynSlice D ◂ υ
    s = γ ,ₛ σₛ ⇑ ψ-ctx ∈ d-ctx ⊒ υ⊑ctx
    min : IsMinimal s
    min s' s'⊑
      with static-gradual-syn-exp D (SS._↓σₛ s')
    ... | ψ-s' , d-s'
      with ih-exp (SS._↓σₛ s' ⇑ ψ-s' ∈ d-s'
                     ⊒ ⊑.trans {Typ} (s' .valid) (syn-precision (SS._↓γ⊑ s') (⊑.refl {Exp}) d-s' (s' .syn)))
                  (proj₂ s'⊑)
    ... | ≡refl
      with extract-ctx-min c (s' .syn) (s' .valid) (SS._↓γ⊑ s')
    ... | γ⊑γ' = ⊑.antisym {Assms ∧ Exp}
        (γ⊑γ' , ⊑.refl {Exp}) s'⊑
