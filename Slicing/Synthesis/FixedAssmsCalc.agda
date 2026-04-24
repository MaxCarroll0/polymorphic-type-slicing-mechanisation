open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; cong) renaming (refl to ≡refl; sym to ≡sym)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.List using (_∷_)
open import Core
open import Semantics.Statics

open import Slicing.Synthesis.FixedAssmsSynthesis

module Slicing.Synthesis.FixedAssmsCalc where

private _≟t_ = HasDecEq._≟_ typ-decEq

-- Fixed-context minimal expression slice calculus
-- D ◂ₑ υ ↦ ψ ⊣ γ: derivation D explains type query υ within full free context,
-- actually synthesising ψ (where υ ⊑ₛ ψ), using context entries γ.
infix 4 _◂ₑ_↦_⊣_
data _◂ₑ_↦_⊣_ {n : ℕ} {Γ : Assms} : ∀ {e : Exp} {τ : Typ}
          → (D : n ； Γ ⊢ e ↦ τ) → ⌊ τ ⌋ → ⌊ τ ⌋ → ⌊ Γ ⌋ → Set where

  minVar   : ∀ {n' τ'} (p : Γ at n' ≡ just τ') {υ : ⌊ τ' ⌋}
             → (υ .↓ ≢ □)
             → ↦Var p ◂ₑ υ ↦ ⊤ₛ ⊣ ⊥ₛ [ p ≔ υ ]ₛ

  min□     : ∀ {e τ} {D : n ； Γ ⊢ e ↦ τ}
             → D ◂ₑ ⊥ₛ ↦ ⊥ₛ ⊣ ⊥ₛ

  min*     : ↦* ◂ₑ ⊤ₛ ↦ ⊤ₛ ⊣ ⊥ₛ

  minλ:    : ∀ {e τ₁ τ₂ υ₁ υ₂ ψ₂ ϕ₁ γ} {wf : n ⊢wf τ₁}
               {D : n ； (τ₁ ∷ Γ) ⊢ e ↦ τ₂}
             → D ◂ₑ υ₂ ↦ ψ₂ ⊣ (ϕ₁ ∷ₛ γ)
             → (↦λ: wf D) ◂ₑ (υ₁ ⇒ₛ υ₂) ↦ ((ϕ₁ ⊔ₛ υ₁) ⇒ₛ ψ₂) ⊣ γ

  minΛ     : ∀ {e τ υ ψ' γ}
               {D : suc n ； shiftΓ 1 Γ ⊢ e ↦ τ}
             → D ◂ₑ υ ↦ ψ' ⊣ (shiftΓₛ γ)
             → (↦Λ D) ◂ₑ (∀·ₛ υ) ↦ (∀·ₛ ψ') ⊣ γ

  min&     : ∀ {e₁ e₂ τ₁ τ₂ υ₁ υ₂ ψ₁ ψ₂ γ₁ γ₂}
               {D₁ : n ； Γ ⊢ e₁ ↦ τ₁} {D₂ : n ； Γ ⊢ e₂ ↦ τ₂}
             → D₁ ◂ₑ υ₁ ↦ ψ₁ ⊣ γ₁ → D₂ ◂ₑ υ₂ ↦ ψ₂ ⊣ γ₂
             → (↦& D₁ D₂) ◂ₑ (υ₁ ×ₛ υ₂) ↦ (ψ₁ ×ₛ ψ₂) ⊣ γ₁ ⊔ₛ γ₂

  min∘     : ∀ {e₁ e₂ τ τ₁ τ₂ ψ₁ γ₁}
               {D₁ : n ； Γ ⊢ e₁ ↦ τ} {m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂}
               {D₂ : n ； Γ ⊢ e₂ ↤ τ₁}
               {υ ψ : ⌊ τ₂ ⌋}
             → D₁ ◂ₑ (unmatch⇒ m ⊥ₛ υ) ↦ ψ₁ ⊣ γ₁
             → (↦∘ D₁ m D₂) ◂ₑ υ ↦ ψ ⊣ γ₁

  min<>    : ∀ {e τ τ' σ ψ₁ γ}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ ∀· □ ≡ ∀· τ'} {wf : n ⊢wf σ}
               {υ ψ : ⌊ [ zero ↦ σ ] τ' ⌋} {υ' : ⌊ τ' ⌋} {ϕ₁ : ⌊ σ ⌋}
             → υ ⊑ₛ subₛ ϕ₁ υ'
             → D ◂ₑ (unmatch∀ m υ') ↦ ψ₁ ⊣ γ
             → (↦<> D m wf) ◂ₑ υ ↦ ψ ⊣ γ

  -- D₁'s ψ₁ becomes bound variable for D₂
  mindef   : ∀ {e' e τ' τ υ' υ ψ₁ ψ₂ γ₁ γ₂}
               {D₁ : n ； Γ ⊢ e' ↦ τ'} {D₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ}
             → D₁ ◂ₑ υ' ↦ ψ₁ ⊣ γ₁
             → D₂ ◂ₑ υ ↦ ψ₂ ⊣ (ψ₁ ∷ₛ γ₂)
             → (↦def D₁ D₂) ◂ₑ υ ↦ ψ₂ ⊣ γ₁ ⊔ₛ γ₂

  minπ₁   : ∀ {e τ τ₁ τ₂ υ ψ₁ γ}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
               {ψ : ⌊ τ₁ ⌋}
             → D ◂ₑ (unmatch× m υ ⊥ₛ) ↦ ψ₁ ⊣ γ
             → (↦π₁ D m) ◂ₑ υ ↦ ψ ⊣ γ

  minπ₂   : ∀ {e τ τ₁ τ₂ υ ψ₁ γ}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
               {ψ : ⌊ τ₂ ⌋}
             → D ◂ₑ (unmatch× m ⊥ₛ υ) ↦ ψ₁ ⊣ γ
             → (↦π₂ D m) ◂ₑ υ ↦ ψ ⊣ γ

  -- scrutinee's ψ provides bound variable types for branches
  mincase  : ∀ {e e₁ e₂ τ₁ τ₂ τ₁' τ₂' ς υ₁ υ₂ ψ₀ ψ₁ ψ₂ γ₀ γ₁ γ₂}
               {D : n ； Γ ⊢ e ↦ τ₁ + τ₂}
               {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
               {c : τ₁' ~ τ₂'}
               {υ ψ : ⌊ τ₁' ⊔ τ₂' ⌋}
             → D ◂ₑ ς ↦ ψ₀ ⊣ γ₀
             → D₁ ◂ₑ υ₁ ↦ ψ₁ ⊣ (fst+ₛ ψ₀ ∷ₛ γ₁)
             → D₂ ◂ₑ υ₂ ↦ ψ₂ ⊣ (snd+ₛ ψ₀ ∷ₛ γ₂)
             → υ .↓ ⊑ υ₁ .↓ ⊔ υ₂ .↓
             → (↦case D (⊔□+□ {τ₁} {τ₂}) D₁ D₂ c) ◂ₑ υ ↦ ψ ⊣ (γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂

-- Extract a FixedAssmsSynSlice from a calculus derivation.
extract
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ ψ γ}
    → D ◂ₑ υ ↦ ψ ⊣ γ
    → FixedAssmsSynSlice D υ

extract (minVar {τ' = τ'} p {υ = υ} _)
  = ⊤ₛ ⇑ ⊤ₛ ∈ ↦Var p ⊒ ⊤ₛ-max {A = Typ} {a = τ'} υ
extract min□
  = ⊥ₛ ⇑ ⊥ₛ ∈ ↦□ ⊒ ⊑□
extract min*
  = ⊤-fixedassms-syn ↦*
extract (minλ: {υ₁ = υ₁} {wf = wf} sub)
  with extract sub
... | σ-body ⇑ ϕ-body ∈ d-body ⊒ v-body
  = λ:ₛ ⊤ₛ σ-body
    ⇑ ⊤ₛ ⇒ₛ ϕ-body
    ∈ ↦λ: wf d-body
    ⊒ ⊑⇒ (⊤ₛ-max υ₁) v-body
extract (minΛ sub)
  with extract sub
... | σ-body ⇑ ϕ-body ∈ d-body ⊒ v-body
  = Λₛ σ-body ⇑ ∀·ₛ ϕ-body ∈ ↦Λ d-body ⊒ ⊑∀ v-body
extract (min& s₁ s₂)
  with extract s₁ | extract s₂
... | σ₁ ⇑ ϕ₁ ∈ d₁ ⊒ v₁ | σ₂ ⇑ ϕ₂ ∈ d₂ ⊒ v₂
  = σ₁ &ₛ σ₂ ⇑ ϕ₁ ×ₛ ϕ₂ ∈ ↦& d₁ d₂ ⊒ ⊑× v₁ v₂
  
extract (min∘ {τ = τ} {m = m} {υ = υ} sub)
  with extract sub
... | σ-fn ⇑ ϕ-fn ∈ d-fn ⊒ v-fn
  with ⊔-⇒-⊑ (ϕ-fn .proof) m
... | ϕ₁' , ϕ₂' , m' , _ , ϕ₂'⊑τ₂
  with ⊔-⇒-⊑ v-fn m'
... | ϕ₁'' , ϕ₂'' , m'' , ϕ₁''⊑ϕ₁' , υ⊑ϕ₂'
  rewrite ≡sym (unmatch⇒-≡-snd {τ} m ⊥ₛ υ m'')
  = ∘ₛ σ-fn ⊥ₛ
    ⇑ ↑ ϕ₂'⊑τ₂
    ∈ ↦∘ d-fn m' (↤Sub ↦□ ~?₁)
    ⊒ υ⊑ϕ₂'
    
extract (min<> {D = D} {m = m} {wf = wf} sub⊑ sub)
  with extract sub
... | σ ⇑ ϕ ∈ d ⊒ v = {!<>-case — needs sub-⊑ for substitution!}

extract (mindef {D₁ = D₁} s₁ s₂)
  with extract s₁ | extract s₂
... | σ₁ ⇑ ϕ₁ ∈ d₁ ⊒ v₁ | σ₂ ⇑ ϕ₂ ∈ d₂ ⊒ v₂
  = defₛ ⊤ₛ σ₂
    ⇑ ϕ₂
    ∈ ↦def D₁ d₂
    ⊒ v₂

extract (minπ₁ {m = m} sub)
  with extract sub
... | σ ⇑ ϕ ∈ d ⊒ v
  with ⊔-×-⊑ (ϕ .proof) m
... | τ₁' , τ₂' , m' , τ₁'⊑ , τ₂'⊑
  = π₁ₛ σ
    ⇑ ↑ τ₁'⊑
    ∈ ↦π₁ d m'
    ⊒ {!υ .↓ ⊑ τ₁'!}

extract (minπ₂ {m = m} sub)
  with extract sub
... | σ ⇑ ϕ ∈ d ⊒ v
  with ⊔-×-⊑ (ϕ .proof) m
... | τ₁' , τ₂' , m' , τ₁'⊑ , τ₂'⊑
  = π₂ₛ σ
    ⇑ ↑ τ₂'⊑
    ∈ ↦π₂ d m'
    ⊒ {!υ .↓ ⊑ τ₂'!}

extract (mincase s s₁ s₂ υ⊑)
  = {!case — same context mismatch as def: branches typed in τᵢ ∷ Γ but match gives τᵢ'' ∷ Γ!}
