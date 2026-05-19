open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; cong) renaming (refl to ≡refl; sym to ≡sym)
open import Relation.Nullary using (yes; no; ¬_; Dec)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.List using (_∷_)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Relation.Unary.All using (All; lookup)
open import Data.List.Relation.Unary.All.Properties.Core using (¬Any⇒All¬)
open import Induction.WellFounded using (Acc; acc)
open import Core
open import Core.Typ.WellFounded
  using (⊏ₛ-wf; max-strict-slices; max-strict-slices-valid; max-strict-slices-complete)
open import Semantics.Statics
open import Semantics.Graduality using (static-gradual-syn)

open import Slicing.Synthesis.FixedAssmsCalc
open import Slicing.Synthesis.FixedAssmsSynthesis
open import Slicing.Synthesis.BranchPair
open import Slicing.Synthesis.QueryWeaken using (query-weaken)

open import Semantics.Graduality using (syn-precision; syn-unicity)

module Slicing.Synthesis.FixedAssmsSlicing where

↓□→⊥ₛ : ∀ {τ : Typ} (υ : ⌊ τ ⌋) → υ .↓ ≡ □ → υ ≡ ⊥ₛ {a = τ}
↓□→⊥ₛ (□ isSlice ⊑□) ≡refl = ≡refl

-- Corollary: Slicing at ⊤ₛ produces ψ with ψ .↓ ≡ τ
-- invariant (sub : D ◂ υ ⤳ σ ↦ ψ ⊣ γ implies υ ⊑ₛ ψ): for υ = ⊤ₛ, we get
-- ⊤ₛ ⊑ ψ alongside ψ .↓ ⊑ τ, hence ψ .↓ ≡ τ by antisymmetry.
slice-⊤-yields-⊤
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ ψ γ}
    → D ◂ (⊤ₛ {a = τ}) ⤳ σ ↦ ψ ⊣ γ
    → ψ .↓ ≡ τ
slice-⊤-yields-⊤ {ψ = ψ} sub =
  let ⊤⊑ψ = subst (⊤ₛ ⊑ₛ_) (extract-ψ sub) ((extract sub) .valid)
  in ⊑.antisym {Typ} (ψ .proof) ⊤⊑ψ

-- Project a slice of the join down to a slice of the left/right component.
-- proj-L c υ has .↓ = υ .↓ ⊓ τ₁; proj-R c υ has .↓ = υ .↓ ⊓ τ₂.
proj-L : ∀ {τ₁ τ₂ : Typ} → τ₁ ~ τ₂ → ⌊ τ₁ ⊔ τ₂ ⌋ → ⌊ τ₁ ⌋
proj-L c υ = ↑ (⊑ₛLat.x⊓ₛy⊑ₛy {A = Typ} υ (↑ (~.⊔-ub₁ c)))

proj-R : ∀ {τ₁ τ₂ : Typ} → τ₁ ~ τ₂ → ⌊ τ₁ ⊔ τ₂ ⌋ → ⌊ τ₂ ⌋
proj-R c υ = ↑ (⊑ₛLat.x⊓ₛy⊑ₛy {A = Typ} υ (↑ (~.⊔-ub₂ c)))

-- Phase 1: postulated joint branch fixed point
-- branch slices subject to Heyting irredundancy bounds (z₁, z₂)
-- and the coverage of υ (used in Phase 2)
record BranchFP {n : ℕ} {Γ : Assms} {e₁ e₂ : Exp}
                {τ τ₁ τ₂ τ₁' τ₂' : Typ}
                (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
                (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
                (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
                (c : τ₁' ~ τ₂') (υ : ⌊ τ₁' ⊔ τ₂' ⌋) : Set where
  field
    υ₁  : ⌊ τ₁' ⌋
    υ₂  : ⌊ τ₂' ⌋
    ψ₁  : ⌊ τ₁' ⌋
    ψ₂  : ⌊ τ₂' ⌋
    ς₁  : ⌊ τ₁ ⌋
    ς₂  : ⌊ τ₂ ⌋
    γ₁' : ⌊ Γ ⌋
    γ₂' : ⌊ Γ ⌋
    σ₁  : ⌊ e₁ ⌋
    σ₂  : ⌊ e₂ ⌋
    sub₁  : D₁ ◂ υ₁ ⤳ σ₁ ↦ ψ₁ ⊣ ς₁ ∷ₛ γ₁'
    sub₂  : D₂ ◂ υ₂ ⤳ σ₂ ↦ ψ₂ ⊣ ς₂ ∷ₛ γ₂'
    z₁    : ⊔-inlₛ c υ₁ ⊑ₛ (υ \\ₛ ⊔-inrₛ c ψ₂)
    z₂    : ⊔-inrₛ c υ₂ ⊑ₛ (υ \\ₛ ⊔-inlₛ c ψ₁)
    υ⊑ψ⊔  : υ .↓ ⊑ ψ₁ .↓ ⊔ ψ₂ .↓ -- ψ coverage of υ

postulate
  branch-fixed-point
    : ∀ {n} {Γ : Assms} {e₁ e₂ : Exp} (τ : Typ) {τ₁ τ₂ τ₁' τ₂'}
        (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
        (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
        (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
        (c : τ₁' ~ τ₂') (υ : ⌊ τ₁' ⊔ τ₂' ⌋) → υ .↓ ≢ □
      → (slice₁ : ∀ q → ∃[ σ ] ∃[ ψ ] ∃[ γ ] D₁ ◂ q ⤳ σ ↦ ψ ⊣ γ)
      → (slice₂ : ∀ q → ∃[ σ ] ∃[ ψ ] ∃[ γ ] D₂ ◂ q ⤳ σ ↦ ψ ⊣ γ)
      → BranchFP {τ = τ} m D₁ D₂ c υ

-- Phase 2 — Scrutinee descent: iteratively slice scrutinee to smaller sum types
-- until we get a minimal assumption such that under maximal external assumptions
-- the branches no longer sufficiently cover the query

-- At each step, `one-step-descent` either finds a strict 1-step
-- descent that still covers, or witnesses that no smaller candidate covers
-- If no descent possible, we have a minimal scrutinee slice

-- Helpers
ϕ-fst : ∀ {n} {Γ : Assms} {e₁ τ₁ τ₂ τ₁'} (τ : Typ)
      → (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
      → (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
      → (σ₁ : ⌊ e₁ ⌋) (ψ₀ : ⌊ τ ⌋) → ⌊ τ₁' ⌋
ϕ-fst {Γ = Γ} τ D₁ m σ₁ ψ₀ = ↑ (proj₂ (proj₂ (static-gradual-syn
            (⊑∷ (fst+ₛ' ψ₀ m .proof) (⊑.refl {Assms} {Γ}))
            (σ₁ .proof) D₁)))

ϕ-snd : ∀ {n} {Γ : Assms} {e₂ τ₁ τ₂ τ₂'} (τ : Typ)
      → (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
      → (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
      → (σ₂ : ⌊ e₂ ⌋) (ψ₀ : ⌊ τ ⌋) → ⌊ τ₂' ⌋
ϕ-snd {Γ = Γ} τ D₂ m σ₂ ψ₀ = ↑ (proj₂ (proj₂ (static-gradual-syn
            (⊑∷ (snd+ₛ' ψ₀ m .proof) (⊑.refl {Assms} {Γ}))
            (σ₂ .proof) D₂)))

d-fst : ∀ {n} {Γ : Assms} {e₁ τ₁ τ₂ τ₁'} (τ : Typ)
      → (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
      → (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
      → (σ₁ : ⌊ e₁ ⌋) (ψ₀ : ⌊ τ ⌋)
      → n ； (fst+ₛ' ψ₀ m .↓ ∷ Γ) ⊢ σ₁ .↓ ↦ ϕ-fst τ D₁ m σ₁ ψ₀ .↓
d-fst {Γ = Γ} τ D₁ m σ₁ ψ₀ = proj₁ (proj₂ (static-gradual-syn
             (⊑∷ (fst+ₛ' ψ₀ m .proof) (⊑.refl {Assms} {Γ}))
             (σ₁ .proof) D₁))

d-snd : ∀ {n} {Γ : Assms} {e₂ τ₁ τ₂ τ₂'} (τ : Typ)
      → (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
      → (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
      → (σ₂ : ⌊ e₂ ⌋) (ψ₀ : ⌊ τ ⌋)
      → n ； (snd+ₛ' ψ₀ m .↓ ∷ Γ) ⊢ σ₂ .↓ ↦ ϕ-snd τ D₂ m σ₂ ψ₀ .↓
d-snd {Γ = Γ} τ D₂ m σ₂ ψ₀ = proj₁ (proj₂ (static-gradual-syn
             (⊑∷ (snd+ₛ' ψ₀ m .proof) (⊑.refl {Assms} {Γ}))
             (σ₂ .proof) D₂))

-- ϕᵢ at ψ₀ jointly covers υ
record Cov {n} {Γ : Assms} {e₁ e₂ τ₁ τ₂ τ₁' τ₂'} (τ : Typ)
           (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
           (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
           (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
           (σ₁ : ⌊ e₁ ⌋) (σ₂ : ⌊ e₂ ⌋) (υ : ⌊ τ₁' ⊔ τ₂' ⌋) (ψ₀ : ⌊ τ ⌋) : Set where
  constructor mkCov
  field cov-prf : υ .↓ ⊑ ϕ-fst τ D₁ m σ₁ ψ₀ .↓ ⊔ ϕ-snd τ D₂ m σ₂ ψ₀ .↓
open Cov public

-- Initial coverage at ψ₀ = ⊤ₛ
-- υ ⊑ ψ₁ ⊔ ψ₂ ⊑ ϕ₁(⊤ₛ) ⊔ ϕ₂(⊤ₛ)
init-cov
  : ∀ {n} {Γ : Assms} {e₁ e₂ τ₁ τ₂ τ₁' τ₂'} (τ : Typ)
      (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
      (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
      (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) (c : τ₁' ~ τ₂')
      (υ : ⌊ τ₁' ⊔ τ₂' ⌋)
    → (bfp : BranchFP {τ = τ} m D₁ D₂ c υ)
    → Cov τ D₁ D₂ m (BranchFP.σ₁ bfp) (BranchFP.σ₂ bfp) υ (⊤ₛ {a = τ})
init-cov {Γ = Γ} {τ₁ = τ₁} {τ₂ = τ₂} τ D₁ D₂ m c υ bfp
  with extract (BranchFP.sub₁ bfp) | extract-σ (BranchFP.sub₁ bfp) | extract-ψ (BranchFP.sub₁ bfp)
     | extract (BranchFP.sub₂ bfp) | extract-σ (BranchFP.sub₂ bfp) | extract-ψ (BranchFP.sub₂ bfp)
... | s₁ | ≡refl | ≡refl | s₂ | ≡refl | ≡refl
  = mkCov υ⊑ϕ⊔
  where
    d₁⊤ = d-fst τ D₁ m (BranchFP.σ₁ bfp) (⊤ₛ {a = τ})
    d₂⊤ = d-snd τ D₂ m (BranchFP.σ₂ bfp) (⊤ₛ {a = τ})
    τ₁⊑fst = +-proj-fst-mono (⊤ₛ {a = τ}) m (⊑.refl {Typ}) m
    τ₂⊑snd = +-proj-snd-mono (⊤ₛ {a = τ}) m (⊑.refl {Typ}) m
    ψ₁⊑ϕ₁⊤ = syn-precision (⊑∷ τ₁⊑fst (⊑.refl {Assms})) (⊑.refl {Exp}) d₁⊤ (s₁ .syn)
    ψ₂⊑ϕ₂⊤ = syn-precision (⊑∷ τ₂⊑snd (⊑.refl {Assms})) (⊑.refl {Exp}) d₂⊤ (s₂ .syn)
    c' = ~-⊑-down c ((ϕ-fst τ D₁ m (BranchFP.σ₁ bfp) (⊤ₛ {a = τ})) .proof)
                    ((ϕ-snd τ D₂ m (BranchFP.σ₂ bfp) (⊤ₛ {a = τ})) .proof)
    υ⊑ϕ⊔ = ⊑.trans {Typ} (BranchFP.υ⊑ψ⊔ bfp) (⊔-mono-⊑ c' ψ₁⊑ϕ₁⊤ ψ₂⊑ϕ₂⊤)

-- Decidability of Cov: reduces to decidability of ⊑ at Typ.
cov-decidable
  : ∀ {n} {Γ : Assms} {e₁ e₂ τ₁ τ₂ τ₁' τ₂'} (τ : Typ)
      (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
      (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
      (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
      (σ₁ : ⌊ e₁ ⌋) (σ₂ : ⌊ e₂ ⌋) (υ : ⌊ τ₁' ⊔ τ₂' ⌋)
    → (ψ₀ : ⌊ τ ⌋) → Dec (Cov τ D₁ D₂ m σ₁ σ₂ υ ψ₀)
cov-decidable τ D₁ D₂ m σ₁ σ₂ υ ψ₀
  with υ .↓ ⊑? ((ϕ-fst τ D₁ m σ₁ ψ₀) .↓ ⊔ (ϕ-snd τ D₂ m σ₂ ψ₀) .↓)
... | yes p = yes (mkCov p)
... | no ¬p = no λ cov → ¬p (cov .cov-prf)

-- Cov is monotone in ψ₀: ψ₀' ⊑ ψ₀ ⇒ Cov ψ₀' ⇒ Cov ψ₀.
cov-mono
  : ∀ {n} {Γ : Assms} {e₁ e₂ τ₁ τ₂ τ₁' τ₂'} (τ : Typ)
      (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
      (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
      (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) (c : τ₁' ~ τ₂')
      (σ₁ : ⌊ e₁ ⌋) (σ₂ : ⌊ e₂ ⌋) (υ : ⌊ τ₁' ⊔ τ₂' ⌋)
      (ψ₀ ψ₀' : ⌊ τ ⌋)
    → ψ₀' .↓ ⊑ ψ₀ .↓
    → Cov τ D₁ D₂ m σ₁ σ₂ υ ψ₀'
    → Cov τ D₁ D₂ m σ₁ σ₂ υ ψ₀
cov-mono {Γ = Γ} τ D₁ D₂ m c σ₁ σ₂ υ ψ₀ ψ₀' ψ₀'⊑ψ₀ (mkCov υ⊑ϕ⊔')
  = mkCov (⊑.trans {Typ} υ⊑ϕ⊔' ⊔-mono-step)
  where
    fst-mono : (fst+ₛ' ψ₀' m) .↓ ⊑ (fst+ₛ' ψ₀ m) .↓
    fst-mono = +-proj-fst-mono ψ₀ m ψ₀'⊑ψ₀ (match+ₛ ψ₀' m)
    snd-mono : (snd+ₛ' ψ₀' m) .↓ ⊑ (snd+ₛ' ψ₀ m) .↓
    snd-mono = +-proj-snd-mono ψ₀ m ψ₀'⊑ψ₀ (match+ₛ ψ₀' m)
    ϕ-fst-mono : (ϕ-fst τ D₁ m σ₁ ψ₀') .↓ ⊑ (ϕ-fst τ D₁ m σ₁ ψ₀) .↓
    ϕ-fst-mono = syn-precision (⊑∷ fst-mono (⊑.refl {Assms} {Γ})) (⊑.refl {Exp})
                                (d-fst τ D₁ m σ₁ ψ₀) (d-fst τ D₁ m σ₁ ψ₀')
    ϕ-snd-mono : (ϕ-snd τ D₂ m σ₂ ψ₀') .↓ ⊑ (ϕ-snd τ D₂ m σ₂ ψ₀) .↓
    ϕ-snd-mono = syn-precision (⊑∷ snd-mono (⊑.refl {Assms} {Γ})) (⊑.refl {Exp})
                                (d-snd τ D₂ m σ₂ ψ₀) (d-snd τ D₂ m σ₂ ψ₀')
    c' : (ϕ-fst τ D₁ m σ₁ ψ₀) .↓ ~ (ϕ-snd τ D₂ m σ₂ ψ₀) .↓
    c' = ~-⊑-down c ((ϕ-fst τ D₁ m σ₁ ψ₀) .proof) ((ϕ-snd τ D₂ m σ₂ ψ₀) .proof)
    ⊔-mono-step
      : (ϕ-fst τ D₁ m σ₁ ψ₀') .↓ ⊔ (ϕ-snd τ D₂ m σ₂ ψ₀') .↓
      ⊑ (ϕ-fst τ D₁ m σ₁ ψ₀)  .↓ ⊔ (ϕ-snd τ D₂ m σ₂ ψ₀)  .↓
    ⊔-mono-step = ⊔-mono-⊑ c' ϕ-fst-mono ϕ-snd-mono

-- one-step strict descent: enumerate maximal strict predecessors via
-- max-strict-slices, decide coverage on each via cov-decidable
one-step-descent
  : ∀ {n} {Γ : Assms} {e₁ e₂ τ₁ τ₂ τ₁' τ₂'} (τ : Typ)
      (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
      (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
      (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) (c : τ₁' ~ τ₂')
      (σ₁ : ⌊ e₁ ⌋) (σ₂ : ⌊ e₂ ⌋) (υ : ⌊ τ₁' ⊔ τ₂' ⌋)
    → (ψ₀ : ⌊ τ ⌋) → Cov τ D₁ D₂ m σ₁ σ₂ υ ψ₀
    → (∃[ ψ₀' ] (ψ₀' .↓ ⊏ ψ₀ .↓) ∧ Cov τ D₁ D₂ m σ₁ σ₂ υ ψ₀')
    ⊎ (∀ {ψ₀'} → ψ₀' .↓ ⊏ ψ₀ .↓ → ¬ Cov τ D₁ D₂ m σ₁ σ₂ υ ψ₀')
one-step-descent τ D₁ D₂ m c σ₁ σ₂ υ ψ₀ cov
  with any? (cov-decidable τ D₁ D₂ m σ₁ σ₂ υ) (max-strict-slices ψ₀)
... | yes any-cov =
        let ψ-max , ψ-max∈ , cov-max = find any-cov
            ψ-max⊏ψ₀                 = lookup (max-strict-slices-valid ψ₀) ψ-max∈
        in inj₁ (ψ-max , ψ-max⊏ψ₀ , cov-max)
... | no ¬any-cov = inj₂ λ {ψ₀'} ψ₀'⊏ψ₀ cov' →
        let any-≤                   = max-strict-slices-complete ψ₀ ψ₀' ψ₀'⊏ψ₀
            ψ-max , ψ-max∈ , ψ₀'⊑ψ-max = find any-≤
            cov-max                  = cov-mono τ D₁ D₂ m c σ₁ σ₂ υ ψ-max ψ₀'
                                                ψ₀'⊑ψ-max cov'
            ¬cov-max                 = lookup (¬Any⇒All¬ (max-strict-slices ψ₀) ¬any-cov)
                                              ψ-max∈
        in ¬cov-max cov-max

-- Descent loop: well-founded recursion on _⊏_.
case-descend
  : ∀ {n} {Γ : Assms} {e₁ e₂ τ₁ τ₂ τ₁' τ₂'} (τ : Typ)
      (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
      (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
      (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) (c : τ₁' ~ τ₂')
      (σ₁ : ⌊ e₁ ⌋) (σ₂ : ⌊ e₂ ⌋) (υ : ⌊ τ₁' ⊔ τ₂' ⌋)
    → (ψ₀ : ⌊ τ ⌋) → Cov τ D₁ D₂ m σ₁ σ₂ υ ψ₀
    → Acc (λ a b → a .↓ ⊏ b .↓) ψ₀
    → ∃[ ψ₀-min ] Cov τ D₁ D₂ m σ₁ σ₂ υ ψ₀-min
                ∧ (∀ {ψ₀'} → ψ₀' .↓ ⊏ ψ₀-min .↓ → ¬ Cov τ D₁ D₂ m σ₁ σ₂ υ ψ₀')
case-descend τ D₁ D₂ m c σ₁ σ₂ υ ψ₀ cov (acc rs)
  with one-step-descent τ D₁ D₂ m c σ₁ σ₂ υ ψ₀ cov
... | inj₁ (ψ₀' , ψ₀'⊏ψ₀ , cov') =
        case-descend τ D₁ D₂ m c σ₁ σ₂ υ ψ₀' cov' (rs ψ₀'⊏ψ₀)
... | inj₂ no-descent             = ψ₀ , cov , no-descent

-- These postulates are not true, need to be reformulated
postulate
  slice-at-min
    : ∀ {n} {Γ : Assms} {e e₁ e₂ τ₁ τ₂ τ₁' τ₂'} (τ : Typ)
        (D : n ； Γ ⊢ e ↦ τ)
        (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
        (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
        (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
        (σ₁ : ⌊ e₁ ⌋) (σ₂ : ⌊ e₂ ⌋) (υ : ⌊ τ₁' ⊔ τ₂' ⌋)
      → (ψ₀ : ⌊ τ ⌋) → Cov τ D₁ D₂ m σ₁ σ₂ υ ψ₀
      → (∀ {ψ₀'} → ψ₀' .↓ ⊏ ψ₀ .↓ → ¬ Cov τ D₁ D₂ m σ₁ σ₂ υ ψ₀')
      → ∃[ σ₀ ] ∃[ γ₀ ]
          D ◂ unmatch+-min m (fst+ₛ' ψ₀ m) (snd+ₛ' ψ₀ m) ⤳ σ₀ ↦ ψ₀ ⊣ γ₀

postulate
  head-min-at-fp
    : ∀ {n} {Γ : Assms} {e₁ e₂ τ₁ τ₂ τ₁' τ₂'} (τ : Typ)
        (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
        (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
        (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
        (σ₁ : ⌊ e₁ ⌋) (σ₂ : ⌊ e₂ ⌋) (υ : ⌊ τ₁' ⊔ τ₂' ⌋)
      → (ψ₀ : ⌊ τ ⌋) → Cov τ D₁ D₂ m σ₁ σ₂ υ ψ₀
      → (∀ {ψ₀'} → ψ₀' .↓ ⊏ ψ₀ .↓ → ¬ Cov τ D₁ D₂ m σ₁ σ₂ υ ψ₀')
      → IsCaseBranchPairMin D₁ D₂ σ₁ σ₂ υ
                              (fst+ₛ' ψ₀ m) (snd+ₛ' ψ₀ m)

-- Phase 2
phase2
  : ∀ {n} {Γ : Assms} {e e₁ e₂ τ τ₁ τ₂ τ₁' τ₂'}
      (D : n ； Γ ⊢ e ↦ τ)
      (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁')
      (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
      (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) (c : τ₁' ~ τ₂')
      (υ : ⌊ τ₁' ⊔ τ₂' ⌋) (υ≢□ : υ .↓ ≢ □)
      (bfp : BranchFP {τ = τ} m D₁ D₂ c υ)
    → ∃[ σ ] ∃[ ψ ] ∃[ γ ]
        (↦case D m D₁ D₂ c) ◂ υ ⤳ σ ↦ ψ ⊣ γ
phase2 {Γ = Γ} {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} D D₁ D₂ m c υ υ≢□ bfp
  with case-descend τ D₁ D₂ m c (BranchFP.σ₁ bfp) (BranchFP.σ₂ bfp) υ
                    (⊤ₛ {a = τ})
                    (init-cov τ D₁ D₂ m c υ bfp)
                    (⊏ₛ-wf (⊤ₛ {a = τ}))
... | ψ₀-min , cov , no-desc
  = _ , _ , _ , mincase-desc {ϕ₁ = ϕ-fst τ D₁ m (BranchFP.σ₁ bfp) ψ₀-min}
                              {ϕ₂ = ϕ-snd τ D₂ m (BranchFP.σ₂ bfp) ψ₀-min}
                              υ≢□
                              (BranchFP.sub₁ bfp) (BranchFP.sub₂ bfp)
                              (BranchFP.z₁ bfp) (BranchFP.z₂ bfp)
                              (d-fst τ D₁ m (BranchFP.σ₁ bfp) ψ₀-min)
                              (d-snd τ D₂ m (BranchFP.σ₂ bfp) ψ₀-min)
                              (cov .cov-prf) sub-scr head-min mbpc
  where
    sub-scr-pkg = slice-at-min τ D D₁ D₂ m
                    (BranchFP.σ₁ bfp) (BranchFP.σ₂ bfp) υ ψ₀-min cov no-desc
    sub-scr = proj₂ (proj₂ sub-scr-pkg)
    head-min = head-min-at-fp τ D₁ D₂ m
                 (BranchFP.σ₁ bfp) (BranchFP.σ₂ bfp) υ ψ₀-min cov no-desc
    mbpc = min-branch-pair-cover D₁ D₂ (BranchFP.σ₁ bfp) (BranchFP.σ₂ bfp)
             (fst+ₛ' ψ₀-min m) (snd+ₛ' ψ₀-min m)
             (BranchFP.ς₁ bfp ∷ₛ BranchFP.γ₁' bfp)
             (BranchFP.ς₂ bfp ∷ₛ BranchFP.γ₂' bfp) υ

-- Construct a calculus derivation from a typing derivation and type query
slice
  : ∀ {n Γ e τ} → (D : n ； Γ ⊢ e ↦ τ) → (υ : ⌊ τ ⌋)
    → ∃[ σ ] ∃[ ψ ] ∃[ γ ] D ◂ υ ⤳ σ ↦ ψ ⊣ γ

slice D (□ isSlice ⊑□) = _ , _ , _ , min□
slice ↦* (.* isSlice ⊑*) = _ , _ , _ , min*
slice (↦Var {τ = τ} p) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦Var p ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ = _ , _ , _ , minVar p υ≢□

-- Lambda: use graduality to source the derivations
slice (↦λ: {τ₁ = τ₁} wf D) ((._ ⇒ ._) isSlice ⊑⇒ p₁ p₂)
  with slice D (↑ p₂)
... | _ , _ , ((ϕ₁-↓ ∷ γ-↓) isSlice ⊑∷ ϕ₁-⊑ γ-⊑) , sub
  with extract sub | extract-σ sub
... | s | ≡refl
  = let υ₁ = ↑ p₁
        ϕ₁ = ϕ₁-↓ isSlice ϕ₁-⊑
        ann = ϕ₁ ⊔ₛ υ₁
        sgs = static-gradual-syn
                (⊑∷ (ann .proof) (⊑.refl {Assms}))
                (s .expₛ .proof)
                D
        d-ann = proj₁ (proj₂ sgs)
        ψ₂'-⊑ = proj₂ (proj₂ sgs)
    in _ , _ , _ , minλ: {ψ₂' = ↑ ψ₂'-⊑} sub d-ann
slice (↦Λ D) (.∀· ._ isSlice ⊑∀ p)
  with slice D (↑ p)
... | _ , _ , _ , sub = _ , _ , _ , minΛ sub
slice (↦& D₁ D₂) ((._ × ._) isSlice ⊑× p₁ p₂)
  with slice D₁ (↑ p₁) | slice D₂ (↑ p₂)
... | _ , _ , _ , s₁ | _ , _ , _ , s₂ = _ , _ , _ , min& s₁ s₂

-- Elimination forms
slice (↦∘ D₁ m D₂) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦∘ D₁ m D₂ ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D₁ (unmatch⇒ m ⊥ₛ υ)
...   | _ , _ , _ , sub = _ , _ , _ , min∘ υ≢□ sub

slice (↦<> D m wf) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦<> D m wf ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D (unmatch∀ m (unsub υ))
...   | _ , _ , _ , sub = _ , _ , _ , min<> υ≢□ sub

slice (↦π₁ D m) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦π₁ D m ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D (unmatch× m υ ⊥ₛ)
...   | _ , _ , _ , sub = _ , _ , _ , minπ₁ υ≢□ sub

slice (↦π₂ D m) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦π₂ D m ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D (unmatch× m ⊥ₛ υ)
...   | _ , _ , _ , sub = _ , _ , _ , minπ₂ υ≢□ sub

-- Similar use of graduality to annotated lambdas
slice (↦def D₁ D₂) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦def D₁ D₂ ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□ with slice D₂ υ
...   | _ , _ , ((υ₁-↓ ∷ γ₂-↓) isSlice ⊑∷ υ₁-⊑ γ₂-⊑) , s-body
  with extract s-body | extract-σ s-body
...   | s₂ | ≡refl
  with slice D₁ (υ₁-↓ isSlice υ₁-⊑)
...   | _ , _ , _ , s-def
  with extract s-def | extract-ψ s-def
...   | s₁ | ≡refl
  = let sgs = static-gradual-syn
                (⊑∷ (s₁ ↓ϕ⊑) (⊑.refl {Assms}))
                (s₂ .expₛ .proof)
                D₂
        d-def = proj₁ (proj₂ sgs)
        ψ₂'-⊑ = proj₂ (proj₂ sgs)
    in _ , ↑ ψ₂'-⊑ , _ , mindef {ψ₂' = ↑ ψ₂'-⊑} υ≢□ s-body s-def d-def

-- Case clause:
--   υ.↓ ≡ □ → trivial ⊥ slice (min□).
--   Phase 1 (postulated) → BranchFP outputs (σ₁, σ₂, ψ₁, ψ₂, ς₁, ς₂, sub₁, sub₂, z₁, z₂, υ⊑ψ⊔)
--   Decidable check `υ.↓ ⊑? υ₁.↓ ⊔ υ₂.↓`:
--     yes  → mincase-cov (no scrutinee descent needed; branches alone cover υ).
--     no   → descent loop on υ₀ ∈ ⌊τ⌋. Each step
--            re-slices D at a smaller query; by graduality of slice the
--            σ₀, ψ₀ form a descending chain
slice (↦case {Γ = Γ} {τ = τ} D m D₁ D₂ c) υ with υ .↓ ≈? □
... | yes eq = _ , _ , _ , subst (λ υ' → ↦case D m D₁ D₂ c ◂ υ' ⤳ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ)
                                 (≡sym (↓□→⊥ₛ υ eq))
                                 min□
... | no υ≢□
  -- Phase 1 (postulated joint branch fixed point)
  with branch-fixed-point τ m D₁ D₂ c υ υ≢□ (slice D₁) (slice D₂)
... | bfp@record { υ₁ = υ₁ ; υ₂ = υ₂ ; ψ₁ = ψ₁ ; ψ₂ = ψ₂
                 ; ς₁ = ς₁ ; ς₂ = ς₂ ; γ₁' = γ₁' ; γ₂' = γ₂'
                 ; σ₁ = σ₁ ; σ₂ = σ₂
                 ; sub₁ = sub₁ ; sub₂ = sub₂
                 ; z₁ = z₁ ; z₂ = z₂ ; υ⊑ψ⊔ = υ⊑ψ⊔ }
  with υ .↓ ⊑? υ₁ .↓ ⊔ υ₂ .↓
... | no  ¬υ-cov = phase2 D D₁ D₂ m c υ υ≢□ bfp
... | yes υ-cov
  -- Only need to slice the scrutinee once at unmatch+-min m ς₁ ς₂.
  with slice D (unmatch+-min m ς₁ ς₂)
... | _ , ψ₀ , _ , sub-scr =
        let ϕ₁⊑τ₁' = proj₂ (proj₂ (static-gradual-syn
                       (⊑∷ (fst+ₛ' ψ₀ m .proof) (⊑.refl {Assms} {Γ}))
                       (σ₁ .proof) D₁))
            ϕ₂⊑τ₂' = proj₂ (proj₂ (static-gradual-syn
                       (⊑∷ (snd+ₛ' ψ₀ m .proof) (⊑.refl {Assms} {Γ}))
                       (σ₂ .proof) D₂))
            ϕ₁ = ↑ ϕ₁⊑τ₁'
            ϕ₂ = ↑ ϕ₂⊑τ₂'
            d₁-syn = proj₁ (proj₂ (static-gradual-syn
                       (⊑∷ (fst+ₛ' ψ₀ m .proof) (⊑.refl {Assms} {Γ}))
                       (σ₁ .proof) D₁))
            d₂-syn = proj₁ (proj₂ (static-gradual-syn
                       (⊑∷ (snd+ₛ' ψ₀ m .proof) (⊑.refl {Assms} {Γ}))
                       (σ₂ .proof) D₂))
        in _ , _ , _ , mincase-cov {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂}
                                    υ≢□ sub₁ sub₂ z₁ z₂ υ-cov
                                    sub-scr d₁-syn d₂-syn
