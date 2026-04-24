open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; cong) renaming (refl to ≡refl; sym to ≡sym)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.List using (_∷_)
open import Core
open import Semantics.Statics
open import Semantics.Graduality using (syn-unicity)

open import Slicing.Synthesis.Synthesis using (IsMinimal)
open import Slicing.Synthesis.FixedAssmsSynthesis

module Slicing.Synthesis.FixedAssmsCalc where

-- Fixed-context minimal expression slice calculus
-- D ◂ₑ υ ↦ ψ ⊣ γ: derivation D explains type query υ within full free context,
-- actually synthesising ψ (where υ ⊑ₛ ψ), actually using context entries γ.
-- We need to track used context entries to decide how to slice unannotated let bindings and case scrutinees
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
             → (υ .↓ ≢ □)
             → D₁ ◂ₑ (unmatch⇒ m ⊥ₛ υ) ↦ ψ₁ ⊣ γ₁
             → (↦∘ D₁ m D₂) ◂ₑ υ ↦ ψ ⊣ γ₁

  min<>    : ∀ {e τ τ' σ ψ₁ γ}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ ∀· □ ≡ ∀· τ'} {wf : n ⊢wf σ}
               {υ ψ : ⌊ [ zero ↦ σ ] τ' ⌋} {υ' : ⌊ τ' ⌋} {ϕ₁ : ⌊ σ ⌋}
             → (υ .↓ ≢ □)
             → υ ⊑ₛ subₛ ϕ₁ υ'
             → D ◂ₑ (unmatch∀ m υ') ↦ ψ₁ ⊣ γ
             → (↦<> D m wf) ◂ₑ υ ↦ ψ ⊣ γ

  -- D₂'s required assumption on def used to slice D₁
  mindef   : ∀ {e' e τ' τ υ₂ υ₁ ψ₁ ψ₂ γ₁ γ₂}
               {D₁ : n ； Γ ⊢ e' ↦ τ'} {D₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ}
             → (υ₂ .↓ ≢ □)
             → D₂ ◂ₑ υ₂ ↦ ψ₂ ⊣ (υ₁ ∷ₛ γ₂)
             → D₁ ◂ₑ υ₁ ↦ ψ₁ ⊣ γ₁
             → (↦def D₁ D₂) ◂ₑ υ₂ ↦ ψ₂ ⊣ γ₁ ⊔ₛ γ₂

  minπ₁   : ∀ {e τ τ₁ τ₂ υ ψ₁ γ}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
               {ψ : ⌊ τ₁ ⌋}
             → (υ .↓ ≢ □)
             → D ◂ₑ (unmatch× m υ ⊥ₛ) ↦ ψ₁ ⊣ γ
             → (↦π₁ D m) ◂ₑ υ ↦ ψ ⊣ γ

  minπ₂   : ∀ {e τ τ₁ τ₂ υ ψ₁ γ}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
               {ψ : ⌊ τ₂ ⌋}
             → (υ .↓ ≢ □)
             → D ◂ₑ (unmatch× m ⊥ₛ υ) ↦ ψ₁ ⊣ γ
             → (↦π₂ D m) ◂ₑ υ ↦ ψ ⊣ γ

  -- Branches sliced first; their output contexts determine scrutinee query
  mincase  : ∀ {e e₁ e₂ τ₁ τ₂ τ₁' τ₂' ς₁ ς₂ υ₁ υ₂ ψ₀ ψ₁ ψ₂ γ₀ γ₁ γ₂}
               {D : n ； Γ ⊢ e ↦ τ₁ + τ₂}
               {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
               {c : τ₁' ~ τ₂'}
               {υ ψ : ⌊ τ₁' ⊔ τ₂' ⌋}
             → (υ .↓ ≢ □)
             → D₁ ◂ₑ υ₁ ↦ ψ₁ ⊣ (ς₁ ∷ₛ γ₁)
             → D₂ ◂ₑ υ₂ ↦ ψ₂ ⊣ (ς₂ ∷ₛ γ₂)
             → D ◂ₑ (ς₁ +ₛ ς₂) ↦ ψ₀ ⊣ γ₀
             → υ .↓ ⊑ υ₁ .↓ ⊔ υ₂ .↓
             → (↦case D (⊔□+□ {τ₁} {τ₂}) D₁ D₂ c) ◂ₑ υ ↦ ψ ⊣ (γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂

-- Extract a FixedAssmsSynSlice from a calculus derivation.
extract
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ ψ γ}
    → D ◂ₑ υ ↦ ψ ⊣ γ
    → FixedAssmsSynSlice D υ

extract (minVar {τ' = τ'} p {υ = υ} _)
  = ⊤ₛ ⇑ ⊤ₛ ∈ ↦Var p ⊒ ⊤ₛ-max {a = τ'} υ
  
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
  
extract (min∘ {τ = τ} {m = m} {υ = υ} _ sub)
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
    
extract (min<> {τ = τ} {σ = σ} {D = D} {m = m} {wf = wf} {ϕ₁ = ϕ₁} _ sub⊑ sub)
  with extract sub
... | σ-e ⇑ ϕ ∈ d ⊒ v
  with ⊔-∀-⊑ (ϕ .proof) m
... | τ₁' , m' , τ₁'⊑τ'
  with ⊔-∀-⊑ v m'
... | ϕ₁' , m'' , υ'⊑τ₁'
  rewrite ≡sym (unmatch∀-≡ {τ} m _ m'')
  = <>ₛ σ-e ⊤ₛ
    ⇑ ↑ (sub-⊑ zero (⊑.refl {A = Typ} {x = σ}) τ₁'⊑τ')
    ∈ ↦<> d m' wf
    ⊒ ⊑.trans {Typ} sub⊑ (sub-⊑ zero (ϕ₁ .proof) υ'⊑τ₁')

extract (mindef {D₁ = D₁} _ s-body s-def)
  with extract s-body | extract s-def
... | σ₂ ⇑ ϕ₂ ∈ d₂ ⊒ v₂ | σ₁ ⇑ ϕ₁ ∈ d₁ ⊒ v₁
  = defₛ ⊤ₛ σ₂
    ⇑ ϕ₂
    ∈ ↦def D₁ d₂
    ⊒ v₂

extract (minπ₁ {τ = τ} {m = m} _ sub)
  with extract sub
... | σ ⇑ ϕ ∈ d ⊒ v
  with ⊔-×-⊑ (ϕ .proof) m
... | τ₁' , τ₂' , m' , τ₁'⊑ , τ₂'⊑
  with ⊔-×-⊑ v m'
... | ϕ₁'' , ϕ₂'' , m'' , υ⊑τ₁' , _
  rewrite ≡sym (unmatch×-≡-fst {τ} m _ ⊥ₛ m'')
  = π₁ₛ σ
    ⇑ ↑ τ₁'⊑
    ∈ ↦π₁ d m'
    ⊒ υ⊑τ₁'

extract (minπ₂ {τ = τ} {m = m} _ sub)
  with extract sub
... | σ ⇑ ϕ ∈ d ⊒ v
  with ⊔-×-⊑ (ϕ .proof) m
... | τ₁' , τ₂' , m' , τ₁'⊑ , τ₂'⊑
  with ⊔-×-⊑ v m'
... | ϕ₁'' , ϕ₂'' , m'' , _ , υ⊑τ₂'
  rewrite ≡sym (unmatch×-≡-snd {τ} m ⊥ₛ _ m'')
  = π₂ₛ σ
    ⇑ ↑ τ₂'⊑
    ∈ ↦π₂ d m'
    ⊒ υ⊑τ₂'

extract (mincase {D = D} {c = c} _ s₁ s₂ s υ⊑)
  with extract s₁ | extract s₂ | extract s
... | σ₁ ⇑ ϕ₁ ∈ d₁ ⊒ v₁ | σ₂ ⇑ ϕ₂ ∈ d₂ ⊒ v₂ | σ₀ ⇑ ϕ₀ ∈ d₀ ⊒ v₀
  = let c' = ~-⊑-down c (ϕ₁ .proof) (ϕ₂ .proof)
    in caseₛ ⊤ₛ σ₁ σ₂
       ⇑ ↑ (⊔-mono-⊑ c (ϕ₁ .proof) (ϕ₂ .proof))
       ∈ ↦case D ⊔□+□ d₁ d₂ c'
       ⊒ ⊑.trans {Typ} υ⊑ (⊔-mono-⊑ c' v₁ v₂)

-- Lemmas for minimality proof
⊤⋢⊥ : ∀ {τ : Typ} → τ ≢ □ → (⊤ₛ {a = τ}) ⊑ₛ  (⊥ₛ {a = τ}) → Data.Empty.⊥
⊤⋢⊥ {□} τ≢□ _ = τ≢□ ≡refl

⊑ₛ⊥-inv : ∀ {τ : Typ} {υ : ⌊ τ ⌋} → _⊑ₛ_ {A = Typ} {a = τ} υ (⊥ₛ {A = Typ} {a = τ}) → υ .↓ ≡ □
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

-- extract produces minimal slices
extract-minimal
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ ψ γ}
    → (c : D ◂ₑ υ ↦ ψ ⊣ γ)
    → IsMinimal (extract c)
extract-minimal min□ s' s'⊑
  = ⊑.antisym {Exp} (⊑ₛLat.⊥ₛ-min (s' .expₛ)) s'⊑
extract-minimal min* s' s'⊑
  = ⊑.antisym {Exp} (*-non□ s' (s' .valid) (s' .syn)) s'⊑
extract-minimal (minVar p υ≢□) s' s'⊑
  = ⊑.antisym {Exp} (var-non□ s' υ≢□ (s' .valid) (s' .syn)) s'⊑
extract-minimal (minλ: sub) = {!!}
extract-minimal (minΛ sub) = {!!}
extract-minimal (min& s₁ s₂) = {!!}
extract-minimal (min∘ υ≢□ sub) = {!!}
extract-minimal (min<> υ≢□ sub⊑ sub) = {!!}
extract-minimal (mindef υ≢□ s-body s-def) = {!!}
extract-minimal (minπ₁ υ≢□ sub) = {!!}
extract-minimal (minπ₂ υ≢□ sub) = {!!}
extract-minimal (mincase υ≢□ s₁ s₂ s υ⊑) = {!!}

-- Corollary: calculus derivation gives a MinFixedAssmsSynSlice
extract-min
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ ψ γ}
    → D ◂ₑ υ ↦ ψ ⊣ γ
    → MinFixedAssmsSynSlice D υ
extract-min c = extract c , extract-minimal c
