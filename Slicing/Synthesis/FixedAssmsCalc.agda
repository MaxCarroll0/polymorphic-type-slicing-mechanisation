{-# OPTIONS --allow-unsolved-metas #-}
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
open import Core.Assms.Lift using (≔ₛ-↓)

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

  -- Branches sliced first; their output contexts determine scrutinee query.
  -- Branch queries are complements: υ₁ = ¬ₛ ψ₂' and υ₂ = ¬ₛ ψ₁', ensuring
  -- no redundancy
  mincase  : ∀ {e e₁ e₂ τ₁ τ₂ τ₁' τ₂' ς₁ ς₂ υ₁ υ₂ ψ₀ ψ₁ ψ₂ ψ₁' ψ₂' γ₀ γ₁ γ₂ σ₀ σ₁ σ₂}
               {D : n ； Γ ⊢ e ↦ τ₁ + τ₂}
               {D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁'} {D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂'}
               {c : τ₁' ~ τ₂'}
               {υ : ⌊ τ₁' ⊔ τ₂' ⌋}
             → (υ .↓ ≢ □)
             → D₁ ◂ υ₁ ⤳ σ₁ ↦ ψ₁ ⊣ (ς₁ ∷ₛ γ₁)
             → D₂ ◂ υ₂ ⤳ σ₂ ↦ ψ₂ ⊣ (ς₂ ∷ₛ γ₂)
             → ⊔-inlₛ c υ₁ ≡ ¬ₛ (⊔-inrₛ c ψ₂) -- No mutual redundancy
             → ⊔-inrₛ c υ₂ ≡ ¬ₛ (⊔-inlₛ c ψ₁)
             → D ◂ (ς₁ +ₛ ς₂) ⤳ σ₀ ↦ ψ₀ ⊣ γ₀
             → n ； (fst+ₛ ψ₀ .↓ ∷ Γ) ⊢ σ₁ .↓ ↦ ψ₁' .↓
             → n ； (snd+ₛ ψ₀ .↓ ∷ Γ) ⊢ σ₂ .↓ ↦ ψ₂' .↓
             → ψ₁' .↓ ~ ψ₂' .↓
             → υ .↓ ⊑ υ₁ .↓ ⊔ υ₂ .↓ -- TODO: derive from boolean properties
             → (↦case D (⊔□+□ {τ₁} {τ₂}) D₁ D₂ c) ◂ υ ⤳ caseₛ σ₀ σ₁ σ₂
               ↦ (ψ₁' ⊔~ₛ ψ₂') {c} ⊣ (γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂

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

-- Extract a MinFixedAssmsSynSlice from a calculus derivation, with proofs that .type ≡ ψ and .expₛ ≡ σ
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
postulate
  extract-ctx-min
    : ∀ {n Γ Γ' e τ τ'} {D : n ； Γ ⊢ e ↦ τ} {σ υ ψ γ}
      → (c : D ◂ υ ⤳ σ ↦ ψ ⊣ γ)
      → n ； Γ' ⊢ σ .↓ ↦ τ'
      → υ .↓ ⊑ τ'
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

extract' (mincase {ς₁ = ς₁} {ς₂ = ς₂} {ψ₁' = ψ₁'} {ψ₂' = ψ₂'} {γ₁ = γ₁} {γ₂ = γ₂}
                  {D = D} {D₁ = D₁} {D₂ = D₂} {c = c} {υ = υ}
                  υ≢□ s₁ s₂ υ₁≡ υ₂≡ s-scr d₁-case d₂-case c' υ⊑)
  with extract' s₁ | extract' s₂ | extract' s-scr | extract-ctx s₁ | extract-ctx s₂
... | ((σ₁ ⇑ ψ₁ ∈ d₁ ⊒ v₁) , ih₁) , ≡refl , ≡refl
    | ((σ₂ ⇑ ψ₂ ∈ d₂ ⊒ v₂) , ih₂) , ≡refl , ≡refl
    | ((σ₀ ⇑ ψ₀ ∈ d₀ ⊒ v₀) , ih₀) , ≡refl , ≡refl
    | ψ-ctx₁ , d-ctx₁ , υ₁⊑ctx₁ | ψ-ctx₂ , d-ctx₂ , υ₂⊑ctx₂
  = let ς₁⊑ = fst+ₛ-⊑ {s₁ = ς₁ +ₛ ς₂} v₀
        ς₂⊑ = snd+ₛ-⊑ {s₁ = ς₁ +ₛ ς₂} v₀
        v₁' = syn-precision (⊑∷ ς₁⊑ (γ₁ .proof)) (⊑.refl {Exp}) d₁-case d-ctx₁
        v₂' = syn-precision (⊑∷ ς₂⊑ (γ₂ .proof)) (⊑.refl {Exp}) d₂-case d-ctx₂
    in (s v₁' v₂' , min v₁' v₂') , ≡refl , ≡refl
  where
    s = λ v₁' v₂' → caseₛ σ₀ σ₁ σ₂
       ⇑ (ψ₁' ⊔~ₛ ψ₂') {c}
       ∈ ↦case d₀ (diag+ₛ ψ₀) d₁-case d₂-case c'
       ⊒ ⊑.trans {Typ} υ⊑ (⊔-mono-⊑ c' (⊑.trans {Typ} υ₁⊑ctx₁ v₁') (⊑.trans {Typ} υ₂⊑ctx₂ v₂'))

    min : ∀ v₁' v₂' → IsMinimal (s v₁' v₂')
    min v₁' v₂' s' s'⊑
      with s' .syn | s' .valid | s' ↓σ⊑ | s' ↓ϕ⊑ | s'⊑
    ... | ↦□ | v' | _ | _ | _
        = ⊥-elim (υ≢□ (⊑ₛ⊥-inv {υ = υ} v'))
    ... | ↦case d₀' m' d₁' d₂' c'' | v' | ⊑case p₀ p₁ p₂ | q | ⊑case e₀⊑ e₁⊑ e₂⊑
      with static-gradual-syn (⊑.refl {Assms}) p₁ D₁
    ... | _ , d-body₁' , τ-hi₁⊑τ₁'
      with static-gradual-syn (⊑.refl {Assms}) p₂ D₂
    ... | _ , d-body₂' , τ-hi₂⊑τ₂'
      with ih₁ (↑ p₁ ⇑ ↑ τ-hi₁⊑τ₁' ∈ d-body₁'
                  ⊒ {!!}) e₁⊑
         | ih₂ (↑ p₂ ⇑ ↑ τ-hi₂⊑τ₂' ∈ d-body₂'
                  ⊒ {!!}) e₂⊑ 
    ... | ≡refl | ≡refl
      with extract-ctx-min s₁ d-body₁' {!!} | extract-ctx-min s₂ d-body₂' {!!}
    ... | ⊑∷ ς₁⊑' _ | ⊑∷ ς₂⊑' _
      with syn-precision (⊑.refl {Assms}) p₀ D d₀'
    ... | τ₀⊑
      with ih₀ (↑ p₀ ⇑ ↑ τ₀⊑ ∈ d₀' ⊒ {!!}) e₀⊑  -- scrutinee validity from ς₁⊑', ς₂⊑' probably
    ... | ≡refl = ≡refl

-- Verify the proposed minimal context is a valid context
-- Base Cases:
extract-ctx (minVar {n' = n'} {τ' = τ'} p {υ = υ} _) = υ , ↦Var (≔ₛ-↓ {k = n'} ⊥ₛ p υ) , ⊑.refl {Typ}
extract-ctx min□ = ⊥ₛ , ↦□ , ⊑□
extract-ctx min* = ⊤ₛ , ↦* , ⊑*

-- Inductive cases:
-- Λ e : ∀· υ — wrap body result
extract-ctx (minΛ sub)
  with extract-ctx sub
... | ψ' , d' , v'
  = ∀·ₛ ψ' , ↦Λ d' , ⊑∀ v'

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
  with static-gradual-syn ((γ₁ ⊔ₛ γ₂) .proof)                -- γ₁⊔γ₂ ⊢ σ₁ ↦ τ₁'
         (σ-def .proof) D₁
... | _ , d₁' , p₁
  with static-gradual-syn (⊑∷ p₁ ((γ₁ ⊔ₛ γ₂) .proof))       -- (τ₁' ∷ γ₁⊔γ₂) ⊢ σ₂ ↦ τ₂'
         (σ-body .proof) D₂
... | _ , d₂' , p₂
  = ↑ p₂ , ↦def d₁' d₂'
  , ⊑.trans {Typ} v₂                                          -- υ₂ ⊑ ψ₂ ⊑ τ₂'
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
extract-ctx (mincase {ς₁ = ς₁} {ς₂ = ς₂} {γ₀ = γ₀} {γ₁ = γ₁} {γ₂ = γ₂}
                    {σ₀ = σ₀} {σ₁ = σ₁} {σ₂ = σ₂}
                    {D = D} {D₁ = D₁} {D₂ = D₂} {c = c} {υ = υ}
                    _ s₁ s₂ _ _ s-scrut d₁-case d₂-case c' υ⊑)
  with extract-ctx s₁ | extract-ctx s₂ | extract-ctx s-scrut
... | ψ₁ , d₁ , v₁                                            -- ς₁∷γ₁ ⊢ σ₁ ↦ ψ₁
    | ψ₂ , d₂ , v₂                                            -- ς₂∷γ₂ ⊢ σ₂ ↦ ψ₂
    | ψ₀ , d₀ , v₀                                            -- γ₀ ⊢ σ₀ ↦ ψ₀
  with static-gradual-syn (((γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂) .proof)       -- γ ⊢ σ₀ ↦ τ₀
         (σ₀ .proof) D
... | τ₀ , d₀' , p₀
  with ⊔-+-⊑ p₀ (⊔□+□ {_} {_})                               -- τ₀ ⊔ □+□ ≡ τa + τb
... | τa , τb , m' , pa , pb
  with static-gradual-syn (⊑∷ pa (((γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂) .proof)) (σ₁ .proof) D₁  -- (τa∷γ) ⊢ σ₁ ↦ τl
     | static-gradual-syn (⊑∷ pb (((γ₀ ⊔ₛ γ₁) ⊔ₛ γ₂) .proof)) (σ₂ .proof) D₂  -- (τb∷γ) ⊢ σ₂ ↦ τr
... | τl , dl , pl | τr , dr , pr
  = let c'' = ~-⊑-down c pl pr
        γ₁⊑ = ⊑.trans {Assms} (⊑ₛLat.y⊑ₛx⊔ₛy γ₀ γ₁)        -- γ₁ ⊑ γ
              (⊑ₛLat.x⊑ₛx⊔ₛy (γ₀ ⊔ₛ γ₁) γ₂)
        γ₂⊑ = ⊑ₛLat.y⊑ₛx⊔ₛy (γ₀ ⊔ₛ γ₁) γ₂                 -- γ₂ ⊑ γ
        γ₀⊑ = ⊑.trans {Assms} (⊑ₛLat.x⊑ₛx⊔ₛy γ₀ γ₁)        -- γ₀ ⊑ γ
              (⊑ₛLat.x⊑ₛx⊔ₛy (γ₀ ⊔ₛ γ₁) γ₂)
        q₀  = syn-precision γ₀⊑ (⊑.refl {Exp}) d₀' d₀        -- ψ₀ ⊑ τ₀
        ς₁⊑ = ⊑.trans {Typ} (fst+ₛ-⊑ {s₁ = ς₁ +ₛ ς₂} {s₂ = ψ₀} v₀)
                (fst+ₛ-⊔ ψ₀ q₀ m')                            -- ς₁ ⊑ τa
        ς₂⊑ = ⊑.trans {Typ} (snd+ₛ-⊑ {s₁ = ς₁ +ₛ ς₂} {s₂ = ψ₀} v₀)
                (snd+ₛ-⊔ ψ₀ q₀ m')                            -- ς₂ ⊑ τb
        q₁  = syn-precision (⊑∷ ς₁⊑ γ₁⊑) (⊑.refl {Exp}) dl d₁  -- ψ₁ ⊑ τl
        q₂  = syn-precision (⊑∷ ς₂⊑ γ₂⊑) (⊑.refl {Exp}) dr d₂  -- ψ₂ ⊑ τr
    in ↑ (⊔-mono-⊑ c pl pr)
     , ↦case d₀' m' dl dr c''
     , ⊑.trans {Typ} υ⊑                                       -- υ ⊑ υ₁⊔υ₂ ⊑ τl⊔τr
         (⊔-mono-⊑ c'' (⊑.trans {Typ} v₁ q₁) (⊑.trans {Typ} v₂ q₂))

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
      with extract-ctx-min c (s' .syn) (s' .valid)
    ... | γ⊑γ' = ⊑.antisym {Assms ∧ Exp}
        (γ⊑γ' , ⊑.refl {Exp}) s'⊑
