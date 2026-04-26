{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; cong) renaming (refl to ≡refl; sym to ≡sym)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.List using (_∷_)
open import Core
open import Semantics.Statics
open import Semantics.Graduality using (syn-unicity; static-gradual-syn; syn-precision)

open import Slicing.Synthesis.Synthesis using (IsMinimal)
open import Slicing.Synthesis.FixedAssmsSynthesis

module Slicing.Synthesis.FixedAssmsCalc where

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

  minΛ     : ∀ {e τ υ ψ' γ σ-body}
               {D : suc n ； shiftΓ 1 Γ ⊢ e ↦ τ}
             → D ◂ υ ⤳ σ-body ↦ ψ' ⊣ (shiftΓₛ γ)
             → (↦Λ D) ◂ (∀·ₛ υ) ⤳ Λₛ σ-body ↦ (∀·ₛ ψ') ⊣ γ

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

  min<>    : ∀ {e τ τ' σ ψ₁ γ σ-e}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ ∀· □ ≡ ∀· τ'} {wf : n ⊢wf σ}
               {υ : ⌊ [ zero ↦ σ ] τ' ⌋} {υ' : ⌊ τ' ⌋} {ϕ₁ : ⌊ σ ⌋}
             → (υ .↓ ≢ □)
             → υ ⊑ₛ subₛ ϕ₁ υ'
             → D ◂ (unmatch∀ m υ') ⤳ σ-e ↦ ψ₁ ⊣ γ
             → (↦<> D m wf) ◂ υ ⤳ <>ₛ σ-e ϕ₁ ↦ subₛ ϕ₁ (body∀ₛ ψ₁ m) ⊣ γ

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

  -- Branches sliced first; their output contexts determine scrutinee query
  -- ψ is the join of branch realized types
  mincase  : ∀ {e e₁ e₂ τ₁ τ₂ τ₁' τ₂' ς₁ ς₂ υ₁ υ₂ ψ₀ ψ₁ ψ₂ ψ₁' ψ₂' γ₀ γ₁ γ₂ σ₀ σ₁ σ₂}
               {D : n ； Γ ⊢ e ↦ τ₁ + τ₂}
               {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
               {c : τ₁' ~ τ₂'}
               {υ : ⌊ τ₁' ⊔ τ₂' ⌋}
             → (υ .↓ ≢ □)
             → D₁ ◂ υ₁ ⤳ σ₁ ↦ ψ₁ ⊣ (ς₁ ∷ₛ γ₁)
             → D₂ ◂ υ₂ ⤳ σ₂ ↦ ψ₂ ⊣ (ς₂ ∷ₛ γ₂)
             → D ◂ (ς₁ +ₛ ς₂) ⤳ σ₀ ↦ ψ₀ ⊣ γ₀
             → n ； (fst+ₛ ψ₀ .↓ ∷ Γ) ⊢ σ₁ .↓ ↦ ψ₁' .↓
             → n ； (snd+ₛ ψ₀ .↓ ∷ Γ) ⊢ σ₂ .↓ ↦ ψ₂' .↓
             → ψ₁' .↓ ~ ψ₂' .↓
             → υ .↓ ⊑ υ₁ .↓ ⊔ υ₂ .↓
             → (↦case D (⊔□+□ {τ₁} {τ₂}) D₁ D₂ c) ◂ υ ⤳ caseₛ σ₀ σ₁ σ₂
               ↦ (ψ₁' ⊔~ₛ ψ₂') {c} ⊣ (γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂

-- Extract a FixedAssmsSynSlice from a calculus derivation, with proofs that .type ≡ ψ and .expₛ ≡ σ
extract'
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → D ◂ υ ⤳ σ ↦ ψ ⊣ γ
    → Σ[ s ∈ FixedAssmsSynSlice D υ ] s .type ≡ ψ ∧ s .expₛ ≡ σ

extract : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → D ◂ υ ⤳ σ ↦ ψ ⊣ γ → FixedAssmsSynSlice D υ
extract c = proj₁ (extract' c)

extract-ψ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → (c : D ◂ υ ⤳ σ ↦ ψ ⊣ γ) → (extract c) .type ≡ ψ
extract-ψ c = proj₁ (proj₂ (extract' c))

extract-σ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → (c : D ◂ υ ⤳ σ ↦ ψ ⊣ γ) → (extract c) .expₛ ≡ σ
extract-σ c = proj₂ (proj₂ (extract' c))

-- The extracted expression types under the used context γ, synthesising ψ
postulate
  extract-ctx
    : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
      → (c : D ◂ υ ⤳ σ ↦ ψ ⊣ γ)
      → n ； γ .↓ ⊢ (extract c) ↓σ ↦ ψ .↓

extract' (minVar {τ' = τ'} p {υ = υ} _)
  = (⊤ₛ ⇑ ⊤ₛ ∈ ↦Var p ⊒ ⊤ₛ-max {a = τ'} υ) , ≡refl , ≡refl

extract' min□
  = (⊥ₛ ⇑ ⊥ₛ ∈ ↦□ ⊒ ⊑□) , ≡refl , ≡refl

extract' min*
  = ⊤-fixedassms-syn ↦* , ≡refl , ≡refl

extract' (minλ: {υ₁ = υ₁} {ϕ₁ = ϕ₁} {γ = γ} {wf = wf} sub d-ann)
  with extract' sub | extract-ctx sub
...  | (σ₂ ⇑ ψ₂ ∈ d₂ ⊒ v₂) , ≡refl , ≡refl | d-ctx
  = let ψ₂⊑ψ₂' = syn-precision (⊑∷ (⊑ₛLat.x⊑ₛx⊔ₛy ϕ₁ υ₁) (γ .proof))
                     (⊑.refl {Exp}) d-ann d-ctx
    in (λ:ₛ (ϕ₁ ⊔ₛ υ₁) σ₂
       ⇑ (ϕ₁ ⊔ₛ υ₁) ⇒ₛ _
       ∈ ↦λ: (wf-⊑ wf ((ϕ₁ ⊔ₛ υ₁) .proof)) d-ann
       ⊒ ⊑⇒ (⊑ₛLat.y⊑ₛx⊔ₛy ϕ₁ υ₁) (⊑.trans {Typ} v₂ ψ₂⊑ψ₂')) , ≡refl , ≡refl
    
extract' (minΛ sub)
  with extract' sub
... | (σ-body ⇑ ϕ-body ∈ d-body ⊒ v-body) , ≡refl , ≡refl
  = (Λₛ σ-body ⇑ ∀·ₛ ϕ-body ∈ ↦Λ d-body ⊒ ⊑∀ v-body) , ≡refl , ≡refl

extract' (min& s₁ s₂)
  with extract' s₁ | extract' s₂
... | (σ₁ ⇑ ϕ₁ ∈ d₁ ⊒ v₁) , ≡refl , ≡refl | (σ₂ ⇑ ϕ₂ ∈ d₂ ⊒ v₂) , ≡refl , ≡refl
  = (σ₁ &ₛ σ₂ ⇑ ϕ₁ ×ₛ ϕ₂ ∈ ↦& d₁ d₂ ⊒ ⊑× v₁ v₂) , ≡refl , ≡refl
  
extract' (min∘ {τ = τ} {m = m} {υ = υ} _ sub)
  with extract' sub
... | (σ-fn ⇑ ψ₁ ∈ d-fn ⊒ v-fn) , ≡refl , ≡refl
  with ⊔-⇒-⊑ v-fn (match⇒ₛ ψ₁ m)
... | _ , _ , m'' , _ , υ⊑cod
  rewrite ≡sym (unmatch⇒-≡-snd {τ} m ⊥ₛ υ m'')
  = (∘ₛ σ-fn ⊥ₛ
    ⇑ cod⇒ₛ ψ₁ m
    ∈ ↦∘ d-fn (match⇒ₛ ψ₁ m) (↤Sub ↦□ ~?₁)
    ⊒ υ⊑cod) , ≡refl , ≡refl
    
extract' (min<> {τ = τ} {σ = σ} {D = D} {m = m} {wf = wf} {ϕ₁ = ϕ₁} _ sub⊑ sub)
  with extract' sub
... | (σ-e ⇑ ψ₁ ∈ d ⊒ v) , ≡refl , ≡refl
  with ⊔-∀-⊑ v (match∀ₛ ψ₁ m)
... | _ , m'' , υ'⊑body
  rewrite ≡sym (unmatch∀-≡ {τ} m _ m'')
  = (<>ₛ σ-e ϕ₁
    ⇑ subₛ ϕ₁ (body∀ₛ ψ₁ m)
    ∈ ↦<> d (match∀ₛ ψ₁ m) (wf-⊑ wf (ϕ₁ .proof))
    ⊒ ⊑.trans {Typ} sub⊑ (sub-⊑ zero (⊑.refl {Typ}) υ'⊑body)) , ≡refl , ≡refl

extract' (mindef {γ₂ = γ₂} _ s-body s-def d-def)
  with extract' s-body | extract' s-def | extract-ctx s-body
... | (σ₂ ⇑ ϕ₂ ∈ d₂ ⊒ v₂) , ≡refl , ≡refl | (σ₁ ⇑ ϕ₁ ∈ d₁ ⊒ v₁) , ≡refl , ≡refl | d-ctx
  = let ψ₂⊑ψ₂' = syn-precision (⊑∷ v₁ (γ₂ .proof))
                     (⊑.refl {Exp}) d-def d-ctx
    in (defₛ σ₁ σ₂
       ⇑ _
       ∈ ↦def d₁ d-def
       ⊒ ⊑.trans {Typ} v₂ ψ₂⊑ψ₂') , ≡refl , ≡refl

extract' (minπ₁ {τ = τ} {m = m} _ sub)
  with extract' sub
... | (σ ⇑ ψ₁ ∈ d ⊒ v) , ≡refl , ≡refl
  with ⊔-×-⊑ v (match×ₛ ψ₁ m)
... | _ , _ , m'' , υ⊑fst , _
  rewrite ≡sym (unmatch×-≡-fst {τ} m _ ⊥ₛ m'')
  = (π₁ₛ σ
    ⇑ fst×ₛ' ψ₁ m
    ∈ ↦π₁ d (match×ₛ ψ₁ m)
    ⊒ υ⊑fst) , ≡refl , ≡refl

extract' (minπ₂ {τ = τ} {m = m} _ sub)
  with extract' sub
... | (σ ⇑ ψ₁ ∈ d ⊒ v) , ≡refl , ≡refl
  with ⊔-×-⊑ v (match×ₛ ψ₁ m)
... | _ , _ , m'' , _ , υ⊑snd
  rewrite ≡sym (unmatch×-≡-snd {τ} m ⊥ₛ _ m'')
  = (π₂ₛ σ
    ⇑ snd×ₛ ψ₁ m
    ∈ ↦π₂ d (match×ₛ ψ₁ m)
    ⊒ υ⊑snd) , ≡refl , ≡refl

extract' (mincase {ς₁ = ς₁} {ς₂ = ς₂} {ψ₁' = ψ₁'} {ψ₂' = ψ₂'} {γ₁ = γ₁} {γ₂ = γ₂} {c = c}
                  _ s₁ s₂ s d₁-case d₂-case c' υ⊑)
  with extract' s₁ | extract' s₂ | extract' s | extract-ctx s₁ | extract-ctx s₂
... | (σ₁ ⇑ ψ₁ ∈ d₁ ⊒ v₁) , ≡refl , ≡refl
    | (σ₂ ⇑ ψ₂ ∈ d₂ ⊒ v₂) , ≡refl , ≡refl
    | (σ₀ ⇑ ψ₀ ∈ d₀ ⊒ v₀) , ≡refl , ≡refl
    | d-ctx₁ | d-ctx₂
  = let ς₁⊑ = fst+ₛ-⊑ {s₁ = ς₁ +ₛ ς₂} v₀
        ς₂⊑ = snd+ₛ-⊑ {s₁ = ς₁ +ₛ ς₂} v₀
        v₁' = syn-precision (⊑∷ ς₁⊑ (γ₁ .proof)) (⊑.refl {Exp}) d₁-case d-ctx₁
        v₂' = syn-precision (⊑∷ ς₂⊑ (γ₂ .proof)) (⊑.refl {Exp}) d₂-case d-ctx₂
    in (caseₛ σ₀ σ₁ σ₂
       ⇑ (ψ₁' ⊔~ₛ ψ₂') {c}
       ∈ ↦case d₀ (diag+ₛ ψ₀) d₁-case d₂-case c'
       ⊒ ⊑.trans {Typ} υ⊑ (⊔-mono-⊑ c' (⊑.trans {Typ} v₁ v₁') (⊑.trans {Typ} v₂ v₂'))) , ≡refl , ≡refl


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

-- extract produces minimal slices
extract-minimal
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → (c : D ◂ υ ⤳ σ ↦ ψ ⊣ γ)
    → IsMinimal (extract c)
extract-minimal min□ s' s'⊑
  = ⊑.antisym {Exp} (⊑ₛLat.⊥ₛ-min (s' .expₛ)) s'⊑
extract-minimal min* s' s'⊑
  = ⊑.antisym {Exp} (*-non□ s' (s' .valid) (s' .syn)) s'⊑
extract-minimal (minVar p υ≢□) s' s'⊑
  = ⊑.antisym {Exp} (var-non□ s' υ≢□ (s' .valid) (s' .syn)) s'⊑
extract-minimal (minλ: sub _) = {!!}
extract-minimal (minΛ sub) = {!!}
extract-minimal (min& s₁ s₂) = {!!}
extract-minimal (min∘ υ≢□ sub) = {!!}
extract-minimal (min<> υ≢□ sub⊑ sub) = {!!}
extract-minimal (mindef υ≢□ s-body s-def _) = {!!}
extract-minimal (minπ₁ υ≢□ sub) = {!!}
extract-minimal (minπ₂ υ≢□ sub) = {!!}
extract-minimal (mincase υ≢□ s₁ s₂ s _ _ _ υ⊑) = {!!}

extract-min
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
    → D ◂ υ ⤳ σ ↦ ψ ⊣ γ
    → MinFixedAssmsSynSlice D υ
extract-min c = extract c , extract-minimal c
