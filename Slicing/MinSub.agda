open import Data.Nat using (ℕ; zero; suc) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax; Σ-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_) renaming (refl to ≡refl; sym to ≡sym; trans to ≡trans; subst to ≡subst)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Core
open import Core.Typ.Equality using (typ-decEq)
open import Core.Typ.Properties using (sub-⊑; ⊔t-zeroᵣ; ⊔-∀-⊑)

-- Decomposition of a type-application query through ∀-substitution.
-- Dissertation: §8.5.3 Type Application (algorithms.tex, sec:term-min-tapp).
module Slicing.MinSub where

private
  _≟t_ = HasDecEq._≟_ typ-decEq

open ⊑ {A = Typ} using () renaming (refl to ⊑t-refl; trans to ⊑t-trans)

record TyAppMatch (τ' σ : Typ) (υ : ⌊ [ zero ↦ σ ] τ' ⌋) : Set where
  field
    tyarg  : ⌊ σ  ⌋
    decomp : υ ⊑ₛ subₛ {τ' = τ'} {σ = σ} tyarg (match-α {τ'} {σ} υ)

private
  tyapp-var :
      ∀ (k : ℕ) {σ : Typ} (m : ℕ) (s : ⌊ [ k ↦ σ ] ⟨ m ⟩ ⌋)
    → Σ[ M ∈ ⌊ σ ⌋ ] s .↓ ⊑t [ k ⇑ M .↓ ] (match-α-aux k ⟨ m ⟩ s) .↓
  tyapp-var k m s with m ≟ℕ k
  ... | yes ≡refl with s .↓ ≟t □
  ...   | yes p
        = (□ isSlice ⊑□) , ≡subst (λ z → z ⊑t □) (≡sym p) ⊑□
  ...   | no  _
        = s , prf
        where
          prf : s .↓ ⊑t [ m ⇑ s .↓ ] ⟨ m ⟩
          prf with m ≟ℕ m
          ... | yes _ = ⊑t-refl
          ... | no ¬p = ⊥-elim (¬p ≡refl)
  tyapp-var k m s | no neq with s .↓ ≟t □
  ...   | yes p
        = (□ isSlice ⊑□) , ≡subst (λ z → z ⊑t □) (≡sym p) ⊑□
  ...   | no  _
        = (□ isSlice ⊑□) , prf
        where
          prf : s .↓ ⊑t [ k ⇑ □ ] ⟨ m ⟩
          prf with m ≟ℕ k
          ... | yes p = ⊥-elim (neq p)
          ... | no _ = s .proof

  tyapp-aux :
      ∀ (k : ℕ) {σ : Typ} (τ' : Typ) (s : ⌊ [ k ↦ σ ] τ' ⌋)
    → Σ[ M ∈ ⌊ σ ⌋ ] s .↓ ⊑t [ k ⇑ M .↓ ] (match-α-aux k τ' s) .↓
  tyapp-aux k *  (□ isSlice ⊑□) = (□ isSlice ⊑□) , ⊑□
  tyapp-aux k *  (* isSlice ⊑*) = (□ isSlice ⊑□) , ⊑*
  tyapp-aux k □  (□ isSlice ⊑□) = (□ isSlice ⊑□) , ⊑□
  tyapp-aux k ⟨ m ⟩ s = tyapp-var k m s
  tyapp-aux k (τ₁ + τ₂) (□ isSlice ⊑□) = (□ isSlice ⊑□) , ⊑□
  tyapp-aux k (τ₁ + τ₂) ((s₁ + s₂) isSlice ⊑+ p₁ p₂) =
    let M₁ , v₁ = tyapp-aux k τ₁ (s₁ isSlice p₁)
        M₂ , v₂ = tyapp-aux k τ₂ (s₂ isSlice p₂)
        c       = ⊑-consistent (M₁ .proof) (M₂ .proof)
        r₁      = match-α-aux k τ₁ (s₁ isSlice p₁)
        r₂      = match-α-aux k τ₂ (s₂ isSlice p₂)
    in (M₁ ⊔ₛ M₂)
    , ⊑+ (⊑t-trans v₁ (sub-⊑ k (~.⊔-ub₁ c) (⊑t-refl {x = r₁ .↓})))
         (⊑t-trans v₂ (sub-⊑ k (~.⊔-ub₂ c) (⊑t-refl {x = r₂ .↓})))
  tyapp-aux k (τ₁ × τ₂) (□ isSlice ⊑□) = (□ isSlice ⊑□) , ⊑□
  tyapp-aux k (τ₁ × τ₂) ((s₁ × s₂) isSlice ⊑× p₁ p₂) =
    let M₁ , v₁ = tyapp-aux k τ₁ (s₁ isSlice p₁)
        M₂ , v₂ = tyapp-aux k τ₂ (s₂ isSlice p₂)
        c       = ⊑-consistent (M₁ .proof) (M₂ .proof)
        r₁      = match-α-aux k τ₁ (s₁ isSlice p₁)
        r₂      = match-α-aux k τ₂ (s₂ isSlice p₂)
    in (M₁ ⊔ₛ M₂)
    , ⊑× (⊑t-trans v₁ (sub-⊑ k (~.⊔-ub₁ c) (⊑t-refl {x = r₁ .↓})))
         (⊑t-trans v₂ (sub-⊑ k (~.⊔-ub₂ c) (⊑t-refl {x = r₂ .↓})))
  tyapp-aux k (τ₁ ⇒ τ₂) (□ isSlice ⊑□) = (□ isSlice ⊑□) , ⊑□
  tyapp-aux k (τ₁ ⇒ τ₂) ((s₁ ⇒ s₂) isSlice ⊑⇒ p₁ p₂) =
    let M₁ , v₁ = tyapp-aux k τ₁ (s₁ isSlice p₁)
        M₂ , v₂ = tyapp-aux k τ₂ (s₂ isSlice p₂)
        c       = ⊑-consistent (M₁ .proof) (M₂ .proof)
        r₁      = match-α-aux k τ₁ (s₁ isSlice p₁)
        r₂      = match-α-aux k τ₂ (s₂ isSlice p₂)
    in (M₁ ⊔ₛ M₂)
    , ⊑⇒ (⊑t-trans v₁ (sub-⊑ k (~.⊔-ub₁ c) (⊑t-refl {x = r₁ .↓})))
         (⊑t-trans v₂ (sub-⊑ k (~.⊔-ub₂ c) (⊑t-refl {x = r₂ .↓})))
  tyapp-aux k (∀· τ) (□ isSlice ⊑□) = (□ isSlice ⊑□) , ⊑□
  tyapp-aux k (∀· τ) ((∀· s₀) isSlice ⊑∀ p) =
    let M , v = tyapp-aux (suc k) τ (s₀ isSlice p)
    in M , ⊑∀ v

tyarg : ∀ {τ' σ : Typ} → ⌊ [ zero ↦ σ ] τ' ⌋ → ⌊ σ ⌋
tyarg {τ'} {σ} υ = tyapp-aux zero {σ} τ' υ .proj₁

tyapp-decomp : ∀ {τ' σ : Typ} (υ : ⌊ [ zero ↦ σ ] τ' ⌋)
  → υ ⊑ₛ subₛ {τ' = τ'} {σ = σ} (tyarg {τ'} {σ} υ) (match-α {τ'} {σ} υ)
tyapp-decomp {τ'} {σ} υ = tyapp-aux zero {σ} τ' υ .proj₂

match-tyapp : ∀ {τ' σ : Typ} (υ : ⌊ [ zero ↦ σ ] τ' ⌋) → TyAppMatch τ' σ υ
match-tyapp {τ'} {σ} υ =
  record { tyarg = tyarg {τ'} {σ} υ ; decomp = tyapp-decomp {τ'} {σ} υ }

private
  tyarg-min-var :
      ∀ (k : ℕ) {σ : Typ} (m : ℕ) (s : ⌊ [ k ↦ σ ] ⟨ m ⟩ ⌋)
        (ϕ : ⌊ σ ⌋) (υ' : ⌊ ⟨ m ⟩ ⌋)
      → s .↓ ⊑t [ k ⇑ ϕ .↓ ] υ' .↓
      → (tyapp-var k m s) .proj₁ .↓ ⊑t ϕ .↓
  tyarg-min-var k m s ϕ (□ isSlice ⊑□) h with m ≟ℕ k
  ... | yes ≡refl with s .↓ ≟t □
  ...   | yes _   = ⊑□
  ...   | no s≠□ = ⊥-elim (s≠□ (⊑.antisym {Typ} h ⊑□))
  tyarg-min-var k m s ϕ (□ isSlice ⊑□) h | no _ with s .↓ ≟t □
  ...   | yes _ = ⊑□
  ...   | no  _ = ⊑□
  tyarg-min-var k m s ϕ (⟨ _ ⟩ isSlice ⊑Var) h with m ≟ℕ m
  ... | no ¬p = ⊥-elim (¬p ≡refl)
  ... | yes _ with m ≟ℕ k
  ...   | yes ≡refl with s .↓ ≟t □
  ...     | yes _ = ⊑□
  ...     | no _  = h
  tyarg-min-var k m s ϕ (⟨ _ ⟩ isSlice ⊑Var) h | yes _ | no _ with s .↓ ≟t □
  ...     | yes _ = ⊑□
  ...     | no _  = ⊑□

  tyarg-min-aux :
      ∀ (k : ℕ) {σ : Typ} (τ' : Typ) (s : ⌊ [ k ↦ σ ] τ' ⌋)
        (ϕ : ⌊ σ ⌋) (υ' : ⌊ τ' ⌋)
      → s .↓ ⊑t [ k ⇑ ϕ .↓ ] υ' .↓
      → (tyapp-aux k τ' s) .proj₁ .↓ ⊑t ϕ .↓
  tyarg-min-aux k * (□ isSlice ⊑□) ϕ υ' h = ⊑□
  tyarg-min-aux k * (* isSlice ⊑*) ϕ υ' h = ⊑□
  tyarg-min-aux k □ (□ isSlice ⊑□) ϕ υ' h = ⊑□
  tyarg-min-aux k ⟨ m ⟩ s ϕ υ' h = tyarg-min-var k m s ϕ υ' h
  tyarg-min-aux k (τ₁ + τ₂) (□ isSlice ⊑□) ϕ υ' h = ⊑□
  tyarg-min-aux k (τ₁ + τ₂) ((s₁ + s₂) isSlice ⊑+ p₁ p₂) ϕ υ' h
    with υ' .proof | h
  ... | ⊑+ q₁ q₂ | ⊑+ h₁ h₂
        = ~.⊔-lub (⊑-consistent (tyapp-aux k τ₁ (s₁ isSlice p₁) .proj₁ .proof)
                                 (tyapp-aux k τ₂ (s₂ isSlice p₂) .proj₁ .proof))
            (tyarg-min-aux k τ₁ (s₁ isSlice p₁) ϕ (_ isSlice q₁) h₁)
            (tyarg-min-aux k τ₂ (s₂ isSlice p₂) ϕ (_ isSlice q₂) h₂)
  tyarg-min-aux k (τ₁ × τ₂) (□ isSlice ⊑□) ϕ υ' h = ⊑□
  tyarg-min-aux k (τ₁ × τ₂) ((s₁ × s₂) isSlice ⊑× p₁ p₂) ϕ υ' h
    with υ' .proof | h
  ... | ⊑× q₁ q₂ | ⊑× h₁ h₂
        = ~.⊔-lub (⊑-consistent (tyapp-aux k τ₁ (s₁ isSlice p₁) .proj₁ .proof)
                                 (tyapp-aux k τ₂ (s₂ isSlice p₂) .proj₁ .proof))
            (tyarg-min-aux k τ₁ (s₁ isSlice p₁) ϕ (_ isSlice q₁) h₁)
            (tyarg-min-aux k τ₂ (s₂ isSlice p₂) ϕ (_ isSlice q₂) h₂)
  tyarg-min-aux k (τ₁ ⇒ τ₂) (□ isSlice ⊑□) ϕ υ' h = ⊑□
  tyarg-min-aux k (τ₁ ⇒ τ₂) ((s₁ ⇒ s₂) isSlice ⊑⇒ p₁ p₂) ϕ υ' h
    with υ' .proof | h
  ... | ⊑⇒ q₁ q₂ | ⊑⇒ h₁ h₂
        = ~.⊔-lub (⊑-consistent (tyapp-aux k τ₁ (s₁ isSlice p₁) .proj₁ .proof)
                                 (tyapp-aux k τ₂ (s₂ isSlice p₂) .proj₁ .proof))
            (tyarg-min-aux k τ₁ (s₁ isSlice p₁) ϕ (_ isSlice q₁) h₁)
            (tyarg-min-aux k τ₂ (s₂ isSlice p₂) ϕ (_ isSlice q₂) h₂)
  tyarg-min-aux k (∀· τ) (□ isSlice ⊑□) ϕ υ' h = ⊑□
  tyarg-min-aux k (∀· τ) ((∀· s₀) isSlice ⊑∀ p) ϕ υ' h
    with υ' .proof | h
  ... | ⊑∀ q  | ⊑∀ h₀
        = tyarg-min-aux (suc k) τ (s₀ isSlice p) ϕ (_ isSlice q) h₀

tyarg-min : ∀ {τ' σ : Typ} (υ : ⌊ [ zero ↦ σ ] τ' ⌋)
  (ϕ : ⌊ σ ⌋) (υ' : ⌊ τ' ⌋)
  → υ ⊑ₛ subₛ {τ' = τ'} {σ = σ} ϕ υ'
  → tyarg {τ'} {σ} υ ⊑ₛ ϕ
tyarg-min {τ'} {σ} υ ϕ υ' h = tyarg-min-aux zero {σ} τ' υ ϕ υ' h

private
  match-α-min-var :
      ∀ (k : ℕ) {σ : Typ} (m : ℕ) (s : ⌊ [ k ↦ σ ] ⟨ m ⟩ ⌋)
      → (ϕ : ⌊ σ ⌋) (υ' : ⌊ ⟨ m ⟩ ⌋)
      → s .↓ ⊑t [ k ⇑ ϕ .↓ ] υ' .↓
      → (match-α-aux k ⟨ m ⟩ s) .↓ ⊑t υ' .↓
  match-α-min-var k m s ϕ (□ isSlice ⊑□) h with m ≟ℕ k
  ... | yes ≡refl with s .↓ ≟t □
  ...   | yes _   = ⊑□
  ...   | no  s≢□ = ⊥-elim (s≢□ (⊑.antisym {Typ} h ⊑□))
  match-α-min-var k m s ϕ (□ isSlice ⊑□) h | no _ with s .↓ ≟t □
  ...   | yes _   = ⊑□
  ...   | no  s≢□ = ⊥-elim (s≢□ (⊑.antisym {Typ} h ⊑□))
  match-α-min-var k m s ϕ (⟨ _ ⟩ isSlice ⊑Var) h with m ≟ℕ k
  ... | yes ≡refl with s .↓ ≟t □
  ...   | yes _ = ⊑□
  ...   | no  _ = ⊑Var
  match-α-min-var k m s ϕ (⟨ _ ⟩ isSlice ⊑Var) h | no _ with s .↓ ≟t □
  ...   | yes _ = ⊑□
  ...   | no  _ = ⊑Var

  match-α-min-aux :
      ∀ (k : ℕ) {σ : Typ} (τ' : Typ) (s : ⌊ [ k ↦ σ ] τ' ⌋)
      → (ϕ : ⌊ σ ⌋) (υ' : ⌊ τ' ⌋)
      → s .↓ ⊑t [ k ⇑ ϕ .↓ ] υ' .↓
      → (match-α-aux k τ' s) .↓ ⊑t υ' .↓
  match-α-min-aux k * (□ isSlice ⊑□) ϕ υ' h = ⊑□
  match-α-min-aux k * (* isSlice ⊑*) ϕ (□ isSlice ⊑□) ()
  match-α-min-aux k * (* isSlice ⊑*) ϕ (* isSlice ⊑*) h = ⊑*
  match-α-min-aux k □ (□ isSlice ⊑□) ϕ υ' h = ⊑□
  match-α-min-aux k ⟨ m ⟩ s ϕ υ' h = match-α-min-var k m s ϕ υ' h
  match-α-min-aux k (τ₁ + τ₂) (□ isSlice ⊑□) ϕ υ' h = ⊑□
  match-α-min-aux k (τ₁ + τ₂) ((s₁ + s₂) isSlice ⊑+ p₁ p₂) ϕ (□ isSlice ⊑□) ()
  match-α-min-aux k (τ₁ + τ₂) ((s₁ + s₂) isSlice ⊑+ p₁ p₂) ϕ
                  ((u₁ + u₂) isSlice ⊑+ q₁ q₂) (⊑+ h₁ h₂) = ⊑+
    (match-α-min-aux k τ₁ (s₁ isSlice p₁) ϕ (u₁ isSlice q₁) h₁)
    (match-α-min-aux k τ₂ (s₂ isSlice p₂) ϕ (u₂ isSlice q₂) h₂)
  match-α-min-aux k (τ₁ × τ₂) (□ isSlice ⊑□) ϕ υ' h = ⊑□
  match-α-min-aux k (τ₁ × τ₂) ((s₁ × s₂) isSlice ⊑× p₁ p₂) ϕ (□ isSlice ⊑□) ()
  match-α-min-aux k (τ₁ × τ₂) ((s₁ × s₂) isSlice ⊑× p₁ p₂) ϕ
                  ((u₁ × u₂) isSlice ⊑× q₁ q₂) (⊑× h₁ h₂) = ⊑×
    (match-α-min-aux k τ₁ (s₁ isSlice p₁) ϕ (u₁ isSlice q₁) h₁)
    (match-α-min-aux k τ₂ (s₂ isSlice p₂) ϕ (u₂ isSlice q₂) h₂)
  match-α-min-aux k (τ₁ ⇒ τ₂) (□ isSlice ⊑□) ϕ υ' h = ⊑□
  match-α-min-aux k (τ₁ ⇒ τ₂) ((s₁ ⇒ s₂) isSlice ⊑⇒ p₁ p₂) ϕ (□ isSlice ⊑□) ()
  match-α-min-aux k (τ₁ ⇒ τ₂) ((s₁ ⇒ s₂) isSlice ⊑⇒ p₁ p₂) ϕ
                  ((u₁ ⇒ u₂) isSlice ⊑⇒ q₁ q₂) (⊑⇒ h₁ h₂) = ⊑⇒
    (match-α-min-aux k τ₁ (s₁ isSlice p₁) ϕ (u₁ isSlice q₁) h₁)
    (match-α-min-aux k τ₂ (s₂ isSlice p₂) ϕ (u₂ isSlice q₂) h₂)
  match-α-min-aux k (∀· τ) (□ isSlice ⊑□) ϕ υ' h = ⊑□
  match-α-min-aux k (∀· τ) ((∀· s₀) isSlice ⊑∀ p) ϕ (□ isSlice ⊑□) ()
  match-α-min-aux k (∀· τ) ((∀· s₀) isSlice ⊑∀ p) ϕ ((∀· u₀) isSlice ⊑∀ q) (⊑∀ h₀) =
    ⊑∀ (match-α-min-aux (suc k) τ (s₀ isSlice p) ϕ (u₀ isSlice q) h₀)

match-α-⊑-body : ∀ {τ' σ : Typ} (υ : ⌊ [ zero ↦ σ ] τ' ⌋)
  → ∀ {τ-d-body} → τ-d-body ⊑ τ'
  → ∀ {σ'} → σ' ⊑ σ
  → υ .↓ ⊑ [ zero ↦ σ' ] τ-d-body
  → (match-α {τ'} {σ} υ) .↓ ⊑ τ-d-body
match-α-⊑-body {τ'} {σ} υ {τ-d-body} τd⊑τ' {σ'} σ'⊑σ v =
  match-α-min-aux zero {σ} τ' υ (σ' isSlice σ'⊑σ) (τ-d-body isSlice τd⊑τ') v

match-α-non□ : ∀ {τ' σ : Typ} (υ : ⌊ [ zero ↦ σ ] τ' ⌋) → υ .↓ ≢ □
  → (match-α {τ'} {σ} υ) .↓ ≢ □
match-α-non□ {τ'} {σ} υ υ≢□ = aux zero τ' υ υ≢□
  where
    aux : ∀ (k : ℕ) {σ} τ' (s : ⌊ [ k ↦ σ ] τ' ⌋)
        → s .↓ ≢ □ → (match-α-aux k τ' s) .↓ ≢ □
    aux k * (□ isSlice ⊑□) s≢□ = s≢□
    aux k * (* isSlice ⊑*) _ = λ ()
    aux k □ (□ isSlice ⊑□) s≢□ = s≢□
    aux k ⟨ m ⟩ s s≢□ with m ≟ℕ k
    ... | yes ≡refl with s .↓ ≟t □
    ...   | yes p = ⊥-elim (s≢□ p)
    ...   | no _  = λ ()
    aux k ⟨ m ⟩ s s≢□ | no _ with s .↓ ≟t □
    ...   | yes p = ⊥-elim (s≢□ p)
    ...   | no _  = λ ()
    aux k (τ₁ + τ₂) (□ isSlice ⊑□) s≢□ = s≢□
    aux k (τ₁ + τ₂) ((s₁ + s₂) isSlice ⊑+ p₁ p₂) s≢□ = λ ()
    aux k (τ₁ × τ₂) (□ isSlice ⊑□) s≢□ = s≢□
    aux k (τ₁ × τ₂) ((s₁ × s₂) isSlice ⊑× p₁ p₂) s≢□ = λ ()
    aux k (τ₁ ⇒ τ₂) (□ isSlice ⊑□) s≢□ = s≢□
    aux k (τ₁ ⇒ τ₂) ((s₁ ⇒ s₂) isSlice ⊑⇒ p₁ p₂) s≢□ = λ ()
    aux k (∀· τ) (□ isSlice ⊑□) s≢□ = s≢□
    aux k (∀· τ) ((∀· s₀) isSlice ⊑∀ p) s≢□ = λ ()

match-α-∀-mono : ∀ {τ τ' σ τ-d : Typ}
  → (m : τ ⊔ ∀· □ ≡ ∀· τ')
  → (υ : ⌊ [ zero ↦ σ ] τ' ⌋) → υ .↓ ≢ □
  → τ-d ⊑ τ
  → ∀ {τ-d-body} → (md : τ-d ⊔ ∀· □ ≡ ∀· τ-d-body)
  → ∀ {σ'} → σ' ⊑ σ
  → υ .↓ ⊑ [ zero ↦ σ' ] τ-d-body
  → (unmatch∀ {τ} m (match-α {τ'} {σ} υ)) .↓ ⊑ τ-d
match-α-∀-mono {τ} {τ'} {σ} m υ υ≢□ τd⊑τ {τ-d-body} md {σ'} σ'⊑σ v
  with ⊔-∀-⊑ τd⊑τ m
... | τx , mx , τx⊑τ'
  with ≡trans (≡sym mx) md
... | ≡refl
  = unmatch∀-mono m (match-α {τ'} {σ} υ) (match-α-non□ {τ'} {σ} υ υ≢□) τd⊑τ md
      (match-α-⊑-body {τ'} {σ} υ τx⊑τ' σ'⊑σ v)
