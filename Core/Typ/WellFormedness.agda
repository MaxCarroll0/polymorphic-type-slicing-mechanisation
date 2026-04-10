module Core.Typ.WellFormedness where

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n) renaming (_+_ to _ℕ+_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Typ.Base
open import Core.Typ.Substitution using (shift; [_↦_]_)

-- Type well-formedness: n ⊢wf τ means all free type variables in τ have index < n
data _⊢wf_ : ℕ → Typ → Set where
  wf*   : ∀ {n}                                       →  n ⊢wf *
  wf□   : ∀ {n}                                       →  n ⊢wf □
  wfVar : ∀ {n k}    →  k < n                          →  n ⊢wf ⟨ k ⟩
  wf+   : ∀ {n τ₁ τ₂}  →  n ⊢wf τ₁  →  n ⊢wf τ₂      →  n ⊢wf τ₁ + τ₂
  wf×   : ∀ {n τ₁ τ₂}  →  n ⊢wf τ₁  →  n ⊢wf τ₂      →  n ⊢wf τ₁ × τ₂
  wf⇒   : ∀ {n τ₁ τ₂}  →  n ⊢wf τ₁  →  n ⊢wf τ₂      →  n ⊢wf τ₁ ⇒ τ₂
  wf∀   : ∀ {n τ}    →  suc n ⊢wf τ                    →  n ⊢wf ∀· τ

infix 4 _⊢wf_

-- Context well-formedness: all types in Γ are well-formed under n type variables
data _⊢wfΓ_ : ℕ → List Typ → Set where
  wfΓ[]  : ∀ {n}                                       →  n ⊢wfΓ []
  wfΓ∷   : ∀ {n τ Γ}  →  n ⊢wf τ  →  n ⊢wfΓ Γ         →  n ⊢wfΓ (τ ∷ Γ)

infix 4 _⊢wfΓ_

-- Lemmas about well-formedness and shifting/substitution
postulate
  shift-preserves-wf  : ∀ {n c a τ}
                       → n ⊢wf τ → (n ℕ+ a) ⊢wf shift c a τ
  shiftΓ-preserves-wf : ∀ {n a Γ}
                       → n ⊢wfΓ Γ → (n ℕ+ a) ⊢wfΓ map (shift 0 a) Γ
  sub-preserves-wf    : ∀ {n σ τ}
                       → n ⊢wf σ → suc n ⊢wf τ → n ⊢wf [ zero ↦ σ ] τ
  wf-weaken           : ∀ {n τ}
                       → n ⊢wf τ → suc n ⊢wf τ
  wfΓ-weaken          : ∀ {n Γ}
                       → n ⊢wfΓ Γ → suc n ⊢wfΓ Γ
