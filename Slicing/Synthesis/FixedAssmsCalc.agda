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
               {υ : ⌊ τ₂ ⌋}
             → (υ .↓ ≢ □)
             → D₁ ◂ₑ (unmatch⇒ m ⊥ₛ υ) ↦ ψ₁ ⊣ γ₁
             → (↦∘ D₁ m D₂) ◂ₑ υ ↦ cod⇒ₛ ψ₁ m ⊣ γ₁

  min<>    : ∀ {e τ τ' σ ψ₁ γ}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ ∀· □ ≡ ∀· τ'} {wf : n ⊢wf σ}
               {υ : ⌊ [ zero ↦ σ ] τ' ⌋} {υ' : ⌊ τ' ⌋} {ϕ₁ : ⌊ σ ⌋}
             → (υ .↓ ≢ □)
             → υ ⊑ₛ subₛ ϕ₁ υ'
             → D ◂ₑ (unmatch∀ m υ') ↦ ψ₁ ⊣ γ
             → (↦<> D m wf) ◂ₑ υ ↦ subₛ ⊤ₛ (body∀ₛ ψ₁ m) ⊣ γ

  -- D₂'s required assumption on def used to slice D₁
  mindef   : ∀ {e' e τ' τ υ₂ υ₁ ψ₁ ψ₂ γ₁ γ₂}
               {D₁ : n ； Γ ⊢ e' ↦ τ'} {D₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ}
             → (υ₂ .↓ ≢ □)
             → D₂ ◂ₑ υ₂ ↦ ψ₂ ⊣ (υ₁ ∷ₛ γ₂)
             → D₁ ◂ₑ υ₁ ↦ ψ₁ ⊣ γ₁
             → (↦def D₁ D₂) ◂ₑ υ₂ ↦ ψ₂ ⊣ γ₁ ⊔ₛ γ₂

  minπ₁   : ∀ {e τ τ₁ τ₂ υ ψ₁ γ}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
             → (υ .↓ ≢ □)
             → D ◂ₑ (unmatch× m υ ⊥ₛ) ↦ ψ₁ ⊣ γ
             → (↦π₁ D m) ◂ₑ υ ↦ fst×ₛ' ψ₁ m ⊣ γ

  minπ₂   : ∀ {e τ τ₁ τ₂ υ ψ₁ γ}
               {D : n ； Γ ⊢ e ↦ τ} {m : τ ⊔ □ × □ ≡ τ₁ × τ₂}
             → (υ .↓ ≢ □)
             → D ◂ₑ (unmatch× m ⊥ₛ υ) ↦ ψ₁ ⊣ γ
             → (↦π₂ D m) ◂ₑ υ ↦ snd×ₛ ψ₁ m ⊣ γ

  -- Branches sliced first; their output contexts determine scrutinee query
  -- ψ is the join of branch realized types
  mincase  : ∀ {e e₁ e₂ τ₁ τ₂ τ₁' τ₂' ς₁ ς₂ υ₁ υ₂ ψ₀ ψ₁ ψ₂ γ₀ γ₁ γ₂}
               {D : n ； Γ ⊢ e ↦ τ₁ + τ₂}
               {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
               {c : τ₁' ~ τ₂'}
               {υ : ⌊ τ₁' ⊔ τ₂' ⌋}
             → (υ .↓ ≢ □)
             → D₁ ◂ₑ υ₁ ↦ ψ₁ ⊣ (ς₁ ∷ₛ γ₁)
             → D₂ ◂ₑ υ₂ ↦ ψ₂ ⊣ (ς₂ ∷ₛ γ₂)
             → D ◂ₑ (ς₁ +ₛ ς₂) ↦ ψ₀ ⊣ γ₀
             → υ .↓ ⊑ υ₁ .↓ ⊔ υ₂ .↓
             → (↦case D (⊔□+□ {τ₁} {τ₂}) D₁ D₂ c) ◂ₑ υ ↦ (ψ₁ ⊔~ₛ ψ₂) {c} ⊣ (γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂

-- Extract a FixedAssmsSynSlice from a calculus derivation, with proof that .type ≡ ψ
extract'
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ ψ γ}
    → D ◂ₑ υ ↦ ψ ⊣ γ
    → Σ[ s ∈ FixedAssmsSynSlice D υ ] s .type ≡ ψ

extract : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ ψ γ}
    → D ◂ₑ υ ↦ ψ ⊣ γ → FixedAssmsSynSlice D υ
extract c = proj₁ (extract' c)

extract-ψ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ ψ γ}
    → (c : D ◂ₑ υ ↦ ψ ⊣ γ) → (extract c) .type ≡ ψ
extract-ψ c = proj₂ (extract' c)

-- The extracted expression types under the used context γ, synthesising ψ
postulate
  extract-ctx
    : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ ψ γ}
      → (c : D ◂ₑ υ ↦ ψ ⊣ γ)
      → n ； γ .↓ ⊢ (extract c) ↓σ ↦ ψ .↓

extract' (minVar {τ' = τ'} p {υ = υ} _)
  = (⊤ₛ ⇑ ⊤ₛ ∈ ↦Var p ⊒ ⊤ₛ-max {a = τ'} υ) , ≡refl

extract' min□
  = (⊥ₛ ⇑ ⊥ₛ ∈ ↦□ ⊒ ⊑□) , ≡refl

extract' min*
  = ⊤-fixedassms-syn ↦* , ≡refl

-- Using graduality and unicity to derive derivation with minimal annotation
extract' (minλ: {υ₁ = υ₁} {υ₂ = υ₂} {ψ₂ = ψ₂} {ϕ₁ = ϕ₁} {γ = γ} {wf = wf} {D = D} sub)
  with extract' sub                | extract-ctx sub
...  | (σ₂ ⇑ ψ₂ ∈ d₂ ⊒ v₂) , ≡refl | d₂-ϕ₁
  with static-gradual-syn-exp (↦λ: wf D) (λ:ₛ (ϕ₁ ⊔ₛ υ₁) σ₂)
     | static-gradual-syn (⊑∷ ((ϕ₁ ⊔ₛ υ₁) .proof) (⊑.refl {Assms})) (σ₂ .proof) D
...  | ϕ-λ , d-λ | ϕ-body-⊔ , d-body-⊔ , ϕ-body-⊔⊑τ₂
  = let d-λ-ϕ₁ = ↦λ: (wf-⊑ wf (ϕ₁ .proof)) d₂-ϕ₁
        d-λ-⊔  = ↦λ: (wf-⊑ wf ((ϕ₁ ⊔ₛ υ₁) .proof)) d-body-⊔
        ψ₂⊑ϕ⊔ = syn-precision (⊑∷ (⊑ₛLat.x⊑ₛx⊔ₛy ϕ₁ υ₁) (γ .proof))
                   (⊑.refl {Exp}) d-body-⊔ d₂-ϕ₁
    in (λ:ₛ (ϕ₁ ⊔ₛ υ₁) σ₂
       ⇑ ϕ-λ
       ∈ d-λ
       ⊒ subst ((υ₁ ⇒ₛ υ₂) .↓ ⊑_) (syn-unicity d-λ-⊔ d-λ)
           (⊑⇒ (⊑ₛLat.y⊑ₛx⊔ₛy ϕ₁ υ₁) (⊑.trans {Typ} v₂ ψ₂⊑ϕ⊔))) , {!!}
    
extract' (minΛ sub)
  with extract' sub
... | σ-body ⇑ ϕ-body ∈ d-body ⊒ v-body , ≡refl
  = (Λₛ σ-body ⇑ ∀·ₛ ϕ-body ∈ ↦Λ d-body ⊒ ⊑∀ v-body) , ≡refl
  
extract' (min& s₁ s₂)
  with extract' s₁ | extract' s₂
... | (σ₁ ⇑ ϕ₁ ∈ d₁ ⊒ v₁) , ≡refl | (σ₂ ⇑ ϕ₂ ∈ d₂ ⊒ v₂) , ≡refl
  = (σ₁ &ₛ σ₂ ⇑ ϕ₁ ×ₛ ϕ₂ ∈ ↦& d₁ d₂ ⊒ ⊑× v₁ v₂) , ≡refl
  
extract' (min∘ {τ = τ} {m = m} {υ = υ} _ sub)
  with extract' sub
... | (σ-fn ⇑ ψ₁ ∈ d-fn ⊒ v-fn) , ≡refl
  with ⊔-⇒-⊑ v-fn (match⇒ₛ ψ₁ m)
... | _ , _ , m'' , _ , υ⊑cod
  rewrite ≡sym (unmatch⇒-≡-snd {τ} m ⊥ₛ υ m'')
  = (∘ₛ σ-fn ⊥ₛ
    ⇑ cod⇒ₛ ψ₁ m
    ∈ ↦∘ d-fn (match⇒ₛ ψ₁ m) (↤Sub ↦□ ~?₁)
    ⊒ υ⊑cod) , ≡refl
    
extract' (min<> {τ = τ} {σ = σ} {D = D} {m = m} {wf = wf} {ϕ₁ = ϕ₁} _ sub⊑ sub)
  with extract' sub
... | (σ-e ⇑ ψ₁ ∈ d ⊒ v) , ≡refl
  with ⊔-∀-⊑ v (match∀ₛ ψ₁ m)
... | _ , m'' , υ'⊑body
  rewrite ≡sym (unmatch∀-≡ {τ} m _ m'')
  = (<>ₛ σ-e ⊤ₛ
    ⇑ subₛ ⊤ₛ (body∀ₛ ψ₁ m)
    ∈ ↦<> d (match∀ₛ ψ₁ m) wf
    ⊒ ⊑.trans {Typ} sub⊑ (sub-⊑ zero (ϕ₁ .proof) υ'⊑body)) , ≡refl

extract' (mindef {D₁ = D₁} _ s-body s-def)
  with extract' s-body | extract' s-def
... | (σ₂ ⇑ ϕ₂ ∈ d₂ ⊒ v₂) , ≡refl | (σ₁ ⇑ ϕ₁ ∈ d₁ ⊒ v₁) , _
  = (defₛ ⊤ₛ σ₂
    ⇑ ϕ₂
    ∈ ↦def D₁ d₂
    ⊒ v₂) , ≡refl

extract' (minπ₁ {τ = τ} {m = m} _ sub)
  with extract' sub
... | (σ ⇑ ψ₁ ∈ d ⊒ v) , ≡refl
  with ⊔-×-⊑ v (match×ₛ ψ₁ m)
... | _ , _ , m'' , υ⊑fst , _
  rewrite ≡sym (unmatch×-≡-fst {τ} m _ ⊥ₛ m'')
  = (π₁ₛ σ
    ⇑ fst×ₛ' ψ₁ m
    ∈ ↦π₁ d (match×ₛ ψ₁ m)
    ⊒ υ⊑fst) , ≡refl

extract' (minπ₂ {τ = τ} {m = m} _ sub)
  with extract' sub
... | (σ ⇑ ψ₁ ∈ d ⊒ v) , ≡refl
  with ⊔-×-⊑ v (match×ₛ ψ₁ m)
... | _ , _ , m'' , _ , υ⊑snd
  rewrite ≡sym (unmatch×-≡-snd {τ} m ⊥ₛ _ m'')
  = (π₂ₛ σ
    ⇑ snd×ₛ ψ₁ m
    ∈ ↦π₂ d (match×ₛ ψ₁ m)
    ⊒ υ⊑snd) , ≡refl

extract' (mincase {D = D} {c = c} _ s₁ s₂ s υ⊑)
  with extract' s₁ | extract' s₂ | extract' s
... | (σ₁ ⇑ ψ₁ ∈ d₁ ⊒ v₁) , ≡refl | (σ₂ ⇑ ψ₂ ∈ d₂ ⊒ v₂) , ≡refl | (σ₀ ⇑ ψ₀ ∈ d₀ ⊒ v₀) , _
  = let c' = ~-⊑-down c (ψ₁ .proof) (ψ₂ .proof)
    in (caseₛ ⊤ₛ σ₁ σ₂
       ⇑ (ψ₁ ⊔~ₛ ψ₂) {c}
       ∈ ↦case D ⊔□+□ d₁ d₂ c'
       ⊒ ⊑.trans {Typ} υ⊑ (⊔-mono-⊑ c' v₁ v₂)) , ≡refl


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

extract-min
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ ψ γ}
    → D ◂ₑ υ ↦ ψ ⊣ γ
    → MinFixedAssmsSynSlice D υ
extract-min c = extract c , extract-minimal c
