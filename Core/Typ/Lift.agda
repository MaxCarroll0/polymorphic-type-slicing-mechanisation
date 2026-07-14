-- Lifts type-level operations (constructors, sum projections, substitution, ∀-matching) to
-- type slices, with monotonicity and precision-inversion lemmas for the unmatch helpers.
-- Dissertation: supports §4.1 Syntax & Relations, §4.2 Lattice Properties, and §8.5 Calculating
-- Term-Minimal Slices (the unmatch / match-α operations).
module Core.Typ.Lift where

open import Data.Nat using (ℕ; zero; suc) renaming (_≟_ to _≟ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; subst; cong; trans; sym)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; ∃-syntax) renaming (_×_ to _∧_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)

open import Core.Typ.Base using (Typ; □; _⇒_; _×_; ∀·; _+_; ⟨_⟩; *; diag; _kind?_; kind□; kind⇒; kind×; kind+; kind∀; diff)
open import Core.Typ.Precision
open import Core.Typ.Lattice -- for instances
open import Core.Typ.Properties using (⊔t-zeroₗ; ⊔t-zeroᵣ; sub-⊑; ⊔-⇒-⊑; ⊔-×-⊑; ⊔-∀-⊑; ⊔-+-⊑; ⊔-mono-⊑)
private ⊔□+□ = Core.Typ.Properties.⊔□+□
open import Core.Typ.Consistency using (_~_)
open import Core.Typ.Substitution using ([_↦_]_)
open import Core.Typ.Equality using (typ-decEq)
open import Core.Instances

open ⊑ {A = Typ} using () renaming (refl to ⊑t-refl; trans to ⊑t-trans)
private _≟t_ = HasDecEq._≟_ typ-decEq

-- Lift type constructors to slices

_⇒ₛ_ : ∀ {τ₁ τ₂ : Typ} → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ₁ ⇒ τ₂ ⌋
s₁ ⇒ₛ s₂ = (s₁ .↓ ⇒ s₂ .↓) isSlice ⊑⇒ (s₁ .proof) (s₂ .proof)

_×ₛ_ : ∀ {τ₁ τ₂ : Typ} → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ₁ × τ₂ ⌋
s₁ ×ₛ s₂ = (s₁ .↓ × s₂ .↓) isSlice ⊑× (s₁ .proof) (s₂ .proof)

∀·ₛ : ∀ {τ : Typ} → ⌊ τ ⌋ → ⌊ ∀· τ ⌋
∀·ₛ s = (∀· (s .↓)) isSlice ⊑∀ (s .proof)

_+ₛ_ : ∀ {τ₁ τ₂ : Typ} → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ₁ + τ₂ ⌋
s₁ +ₛ s₂ = (s₁ .↓ + s₂ .↓) isSlice ⊑+ (s₁ .proof) (s₂ .proof)

-- Projections from sum type slices

fst+ₛ : ∀ {τ₁ τ₂ : Typ} → ⌊ τ₁ + τ₂ ⌋ → ⌊ τ₁ ⌋
fst+ₛ (□ isSlice ⊑□) = ⊥ₛ
fst+ₛ ((_ + _) isSlice ⊑+ p _) = _ isSlice p

snd+ₛ : ∀ {τ₁ τ₂ : Typ} → ⌊ τ₁ + τ₂ ⌋ → ⌊ τ₂ ⌋
snd+ₛ (□ isSlice ⊑□) = ⊥ₛ
snd+ₛ ((_ + _) isSlice ⊑+ _ q) = _ isSlice q

diag+ₛ : ∀ {τ₁ τ₂ : Typ} → (ψ : ⌊ τ₁ + τ₂ ⌋)
        → ψ .↓ ⊔ □ + □ ≡ fst+ₛ ψ .↓ + snd+ₛ ψ .↓
diag+ₛ (□ isSlice ⊑□) = refl
diag+ₛ ((a + b) isSlice ⊑+ _ _) = ⊔□+□ {a} {b}

-- fst+ₛ/snd+ₛ monotone w.r.t. slice precision
fst+ₛ-⊑ : ∀ {τ₁ τ₂} {s₁ s₂ : ⌊ τ₁ + τ₂ ⌋} → s₁ ⊑ₛ s₂ → fst+ₛ s₁ ⊑ₛ fst+ₛ s₂
fst+ₛ-⊑ {s₁ = □ isSlice ⊑□} _ = ⊑□
fst+ₛ-⊑ {s₁ = (_ + _) isSlice ⊑+ _ _} {□ isSlice ⊑□} ()
fst+ₛ-⊑ {s₁ = (_ + _) isSlice ⊑+ _ _} {(_ + _) isSlice ⊑+ _ _} (⊑+ p _) = p

snd+ₛ-⊑ : ∀ {τ₁ τ₂} {s₁ s₂ : ⌊ τ₁ + τ₂ ⌋} → s₁ ⊑ₛ s₂ → snd+ₛ s₁ ⊑ₛ snd+ₛ s₂
snd+ₛ-⊑ {s₁ = □ isSlice ⊑□} _ = ⊑□
snd+ₛ-⊑ {s₁ = (_ + _) isSlice ⊑+ _ _} {□ isSlice ⊑□} ()
snd+ₛ-⊑ {s₁ = (_ + _) isSlice ⊑+ _ _} {(_ + _) isSlice ⊑+ _ _} (⊑+ _ q) = q

-- Like +ₛ, but returns ⊥ₛ when both components are ⊥ₛ.
+ₛ-min : ∀ {τ₁ τ₂ : Typ} → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ₁ + τ₂ ⌋
+ₛ-min (□ isSlice ⊑□) (□ isSlice ⊑□) = ⊥ₛ
+ₛ-min s₁ s₂ = s₁ +ₛ s₂

+ₛ-min⊑+ₛ : ∀ {τ₁ τ₂ : Typ} (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋) → +ₛ-min s₁ s₂ ⊑ₛ (s₁ +ₛ s₂)
+ₛ-min⊑+ₛ (□ isSlice ⊑□) (□ isSlice ⊑□) = ⊑□
+ₛ-min⊑+ₛ ((_ + _) isSlice ⊑+ _ _) s₂ = ⊑.refl {Typ}
+ₛ-min⊑+ₛ (□ isSlice ⊑□) ((_ + _) isSlice ⊑+ _ _) = ⊑.refl {Typ}
+ₛ-min⊑+ₛ (Typ.* isSlice ⊑*) s₂ = ⊑.refl {Typ}
+ₛ-min⊑+ₛ ((_ ⇒ _) isSlice ⊑⇒ _ _) s₂ = ⊑.refl {Typ}
+ₛ-min⊑+ₛ ((_ × _) isSlice ⊑× _ _) s₂ = ⊑.refl {Typ}
+ₛ-min⊑+ₛ ((∀· _) isSlice ⊑∀ _) s₂ = ⊑.refl {Typ}
+ₛ-min⊑+ₛ (Typ.⟨ _ ⟩ isSlice ⊑Var) s₂ = ⊑.refl {Typ}
+ₛ-min⊑+ₛ (□ isSlice ⊑□) (Typ.* isSlice ⊑*) = ⊑.refl {Typ}
+ₛ-min⊑+ₛ (□ isSlice ⊑□) ((_ ⇒ _) isSlice ⊑⇒ _ _) = ⊑.refl {Typ}
+ₛ-min⊑+ₛ (□ isSlice ⊑□) ((_ × _) isSlice ⊑× _ _) = ⊑.refl {Typ}
+ₛ-min⊑+ₛ (□ isSlice ⊑□) ((∀· _) isSlice ⊑∀ _) = ⊑.refl {Typ}
+ₛ-min⊑+ₛ (□ isSlice ⊑□) (Typ.⟨ _ ⟩ isSlice ⊑Var) = ⊑.refl {Typ}

+ₛ-min-⊑ : ∀ {τ₁ τ₂ τ τ₃' τ₄'} (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
  → τ ⊑t τ₁ + τ₂ → τ ⊔ (□ + □) ≡ τ₃' + τ₄'
  → s₁ .↓ ⊑t τ₃' → s₂ .↓ ⊑t τ₄'
  → (+ₛ-min s₁ s₂) .↓ ⊑t τ
+ₛ-min-⊑ s₁ s₂ (⊑+ {τ₁ = a} {τ₂ = b} _ _) m-eq p q
  rewrite ⊔t-zeroᵣ {a} | ⊔t-zeroᵣ {b}
  with refl ← m-eq = ⊑t-trans (+ₛ-min⊑+ₛ s₁ s₂) (⊑+ p q)
+ₛ-min-⊑ s₁ s₂ ⊑□ m-eq p q
  rewrite ⊔t-zeroₗ {□ + □}
  with refl ← m-eq
  with refl ← ⊑.antisym p ⊑□
  with refl ← ⊑.antisym q ⊑□
  with s₁ .proof | s₂ .proof
... | ⊑□ | ⊑□ = ⊑□

fst-+ₛ-min : ∀ {τ₁ τ₂ : Typ} {s₁ : ⌊ τ₁ ⌋} {s₂ : ⌊ τ₂ ⌋} {t : ⌊ τ₁ + τ₂ ⌋}
  → +ₛ-min s₁ s₂ ⊑ₛ t → s₁ ⊑ₛ fst+ₛ t
fst-+ₛ-min {s₁ = □ isSlice ⊑□} {s₂ = □ isSlice ⊑□} _ = ⊑□
fst-+ₛ-min {s₁ = s₁@(□ isSlice ⊑□)} {s₂ = s₂@(Typ.* isSlice ⊑*)} v = fst+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
fst-+ₛ-min {s₁ = s₁@(□ isSlice ⊑□)} {s₂ = s₂@((_ ⇒ _) isSlice ⊑⇒ _ _)} v = fst+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
fst-+ₛ-min {s₁ = s₁@(□ isSlice ⊑□)} {s₂ = s₂@((_ × _) isSlice ⊑× _ _)} v = fst+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
fst-+ₛ-min {s₁ = s₁@(□ isSlice ⊑□)} {s₂ = s₂@((_ + _) isSlice ⊑+ _ _)} v = fst+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
fst-+ₛ-min {s₁ = s₁@(□ isSlice ⊑□)} {s₂ = s₂@((∀· _) isSlice ⊑∀ _)} v = fst+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
fst-+ₛ-min {s₁ = s₁@(□ isSlice ⊑□)} {s₂ = s₂@(Typ.⟨ _ ⟩ isSlice ⊑Var)} v = fst+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
fst-+ₛ-min {s₁ = s₁@(Typ.* isSlice ⊑*)} {s₂ = s₂} v = fst+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
fst-+ₛ-min {s₁ = s₁@((_ ⇒ _) isSlice ⊑⇒ _ _)} {s₂ = s₂} v = fst+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
fst-+ₛ-min {s₁ = s₁@((_ × _) isSlice ⊑× _ _)} {s₂ = s₂} v = fst+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
fst-+ₛ-min {s₁ = s₁@((_ + _) isSlice ⊑+ _ _)} {s₂ = s₂} v = fst+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
fst-+ₛ-min {s₁ = s₁@((∀· _) isSlice ⊑∀ _)} {s₂ = s₂} v = fst+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
fst-+ₛ-min {s₁ = s₁@(Typ.⟨ _ ⟩ isSlice ⊑Var)} {s₂ = s₂} v = fst+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v

snd-+ₛ-min : ∀ {τ₁ τ₂ : Typ} {s₁ : ⌊ τ₁ ⌋} {s₂ : ⌊ τ₂ ⌋} {t : ⌊ τ₁ + τ₂ ⌋}
  → +ₛ-min s₁ s₂ ⊑ₛ t → s₂ ⊑ₛ snd+ₛ t
snd-+ₛ-min {s₁ = □ isSlice ⊑□} {s₂ = □ isSlice ⊑□} _ = ⊑□
snd-+ₛ-min {s₁ = s₁@(□ isSlice ⊑□)} {s₂ = s₂@(Typ.* isSlice ⊑*)} v = snd+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
snd-+ₛ-min {s₁ = s₁@(□ isSlice ⊑□)} {s₂ = s₂@((_ ⇒ _) isSlice ⊑⇒ _ _)} v = snd+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
snd-+ₛ-min {s₁ = s₁@(□ isSlice ⊑□)} {s₂ = s₂@((_ × _) isSlice ⊑× _ _)} v = snd+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
snd-+ₛ-min {s₁ = s₁@(□ isSlice ⊑□)} {s₂ = s₂@((_ + _) isSlice ⊑+ _ _)} v = snd+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
snd-+ₛ-min {s₁ = s₁@(□ isSlice ⊑□)} {s₂ = s₂@((∀· _) isSlice ⊑∀ _)} v = snd+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
snd-+ₛ-min {s₁ = s₁@(□ isSlice ⊑□)} {s₂ = s₂@(Typ.⟨ _ ⟩ isSlice ⊑Var)} v = snd+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
snd-+ₛ-min {s₁ = s₁@(Typ.* isSlice ⊑*)} {s₂ = s₂} v = snd+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
snd-+ₛ-min {s₁ = s₁@((_ ⇒ _) isSlice ⊑⇒ _ _)} {s₂ = s₂} v = snd+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
snd-+ₛ-min {s₁ = s₁@((_ × _) isSlice ⊑× _ _)} {s₂ = s₂} v = snd+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
snd-+ₛ-min {s₁ = s₁@((_ + _) isSlice ⊑+ _ _)} {s₂ = s₂} v = snd+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
snd-+ₛ-min {s₁ = s₁@((∀· _) isSlice ⊑∀ _)} {s₂ = s₂} v = snd+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v
snd-+ₛ-min {s₁ = s₁@(Typ.⟨ _ ⟩ isSlice ⊑Var)} {s₂ = s₂} v = snd+ₛ-⊑ {s₁ = s₁ +ₛ s₂} v

fst+ₛ-⊔ : ∀ {τ₁ τ₂} (s : ⌊ τ₁ + τ₂ ⌋) {τ τ₁ τ₂}
         → s .↓ ⊑t τ → τ ⊔ □ + □ ≡ τ₁ + τ₂ → fst+ₛ s .↓ ⊑t τ₁
fst+ₛ-⊔ (□ isSlice ⊑□) _ _ = ⊑□
fst+ₛ-⊔ ((_ + _) isSlice ⊑+ _ _) (⊑+ {τ₁' = a'} {τ₂' = b'} p _) eq
  rewrite ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'} with refl ← eq = p

snd+ₛ-⊔ : ∀ {τ₁ τ₂} (s : ⌊ τ₁ + τ₂ ⌋) {τ τ₁ τ₂}
         → s .↓ ⊑t τ → τ ⊔ □ + □ ≡ τ₁ + τ₂ → snd+ₛ s .↓ ⊑t τ₂
snd+ₛ-⊔ (□ isSlice ⊑□) _ _ = ⊑□
snd+ₛ-⊔ ((_ + _) isSlice ⊑+ _ _) (⊑+ {τ₁' = a'} {τ₂' = b'} _ q) eq
  rewrite ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'} with refl ← eq = q

-- §7.5.3 matched query (υ̂); generalised over substitution depth k so it recurses under ∀.
match-α-aux : ∀ (k : ℕ) {σ : Typ} (τ' : Typ) → ⌊ [ k ↦ σ ] τ' ⌋ → ⌊ τ' ⌋
match-α-aux k *         s = s
match-α-aux k □         s = s
match-α-aux k ⟨ m ⟩    s with m ≟ℕ k
... | yes _ with s .↓ ≟t □
...   | yes _ = □ isSlice ⊑□
...   | no  _ = ⟨ m ⟩ isSlice ⊑Var
match-α-aux k ⟨ m ⟩    s | no _ with s .↓ ≟t □
...   | yes _ = □ isSlice ⊑□
...   | no  _ = ⟨ m ⟩ isSlice ⊑Var
match-α-aux k (τ₁ + τ₂) (□        isSlice ⊑□)        = □ isSlice ⊑□
match-α-aux k (τ₁ + τ₂) ((_ + _) isSlice ⊑+ p₁ p₂)  =
  let r₁ = match-α-aux k τ₁ (_ isSlice p₁)
      r₂ = match-α-aux k τ₂ (_ isSlice p₂)
  in (r₁ .↓ + r₂ .↓) isSlice ⊑+ (r₁ .proof) (r₂ .proof)
match-α-aux k (τ₁ × τ₂) (□        isSlice ⊑□)        = □ isSlice ⊑□
match-α-aux k (τ₁ × τ₂) ((_ × _) isSlice ⊑× p₁ p₂)  =
  let r₁ = match-α-aux k τ₁ (_ isSlice p₁)
      r₂ = match-α-aux k τ₂ (_ isSlice p₂)
  in (r₁ .↓ × r₂ .↓) isSlice ⊑× (r₁ .proof) (r₂ .proof)
match-α-aux k (τ₁ ⇒ τ₂) (□        isSlice ⊑□)        = □ isSlice ⊑□
match-α-aux k (τ₁ ⇒ τ₂) ((_ ⇒ _) isSlice ⊑⇒ p₁ p₂)  =
  let r₁ = match-α-aux k τ₁ (_ isSlice p₁)
      r₂ = match-α-aux k τ₂ (_ isSlice p₂)
  in (r₁ .↓ ⇒ r₂ .↓) isSlice ⊑⇒ (r₁ .proof) (r₂ .proof)
match-α-aux k (∀· τ)    (□       isSlice ⊑□)         = □ isSlice ⊑□
match-α-aux k (∀· τ)    ((∀· _) isSlice ⊑∀ p)        =
  let r = match-α-aux (suc k) τ (_ isSlice p)
  in ∀· (r .↓) isSlice ⊑∀ (r .proof)

match-α : ∀ {τ' σ} → ⌊ [ zero ↦ σ ] τ' ⌋ → ⌊ τ' ⌋
match-α {τ'} {σ} = match-α-aux zero {σ} τ'

subₛ : ∀ {τ' σ} → ⌊ σ ⌋ → ⌊ τ' ⌋ → ⌊ [ zero ↦ σ ] τ' ⌋
subₛ σ' υ' = ↑ (sub-⊑ zero (σ' .proof) (υ' .proof))

⊑⇒-fst : ∀ {τ₁ τ₂ τ} → τ₁ ⇒ τ₂ ⊑t τ → ∃[ τ₁' ] ∃[ τ₂' ] (τ ≡ τ₁' ⇒ τ₂' ∧ τ₁ ⊑t τ₁' ∧ τ₂ ⊑t τ₂')
⊑⇒-fst (⊑⇒ p q) = _ , _ , refl , p , q

unmatch⇒ : ∀ {τ τ₁ τ₂} → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂ → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ ⌋
unmatch⇒ {τ} eq s₁ s₂ with diag τ (□ ⇒ □)
unmatch⇒      refl s₁ s₂ | kind⇒ =
  subst ⌊_⌋ ⊔t-zeroᵣ s₁ ⇒ₛ subst ⌊_⌋ ⊔t-zeroᵣ s₂
unmatch⇒ {τ} eq   s₁ s₂ | diff with τ ≟t □
...                                | yes refl = ⊥ₛ
unmatch⇒      ()   _  _  | diff    | no _

unmatch∀ : ∀ {τ τ'} → τ ⊔ ∀· □ ≡ ∀· τ' → ⌊ τ' ⌋ → ⌊ τ ⌋
unmatch∀ {τ} eq s with diag τ (∀· □)
unmatch∀      refl s | kind∀ = ∀·ₛ (subst ⌊_⌋ ⊔t-zeroᵣ s)
unmatch∀ {τ} eq    s | diff with τ ≟t □
...                           | yes refl = ⊥ₛ
unmatch∀      ()   _ | diff    | no _

unmatch× : ∀ {τ τ₁ τ₂} → τ ⊔ □ × □ ≡ τ₁ × τ₂ → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ ⌋
unmatch× {τ} eq s₁ s₂ with diag τ (□ × □)
unmatch×      refl s₁ s₂ | kind× =
  subst ⌊_⌋ ⊔t-zeroᵣ s₁ ×ₛ subst ⌊_⌋ ⊔t-zeroᵣ s₂
unmatch× {τ} eq   s₁ s₂ | diff with τ ≟t □
...                                | yes refl = ⊥ₛ
unmatch×      ()   _  _  | diff    | no _

unmatch+ : ∀ {τ τ₁ τ₂} → τ ⊔ □ + □ ≡ τ₁ + τ₂ → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ ⌋
unmatch+ {τ} eq s₁ s₂ with diag τ (□ + □)
unmatch+      refl s₁ s₂ | kind+ =
  ↑ (⊑+ (subst ⌊_⌋ ⊔t-zeroᵣ s₁ .proof) (subst ⌊_⌋ ⊔t-zeroᵣ s₂ .proof))
unmatch+ {τ} eq   s₁ s₂ | diff with τ ≟t □
...                                | yes refl = ⊥ₛ
unmatch+      ()   _  _  | diff    | no _

-- Like unmatch+, but returns ⊥ₛ when both components are ⊥ₛ.
unmatch+-min : ∀ {τ τ₁ τ₂} → τ ⊔ □ + □ ≡ τ₁ + τ₂ → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ ⌋
unmatch+-min m (□ isSlice ⊑□) (□ isSlice ⊑□) = ⊥ₛ
unmatch+-min m s₁ s₂ = unmatch+ m s₁ s₂

-- unmatch×-min: same pattern for product types
unmatch×-min : ∀ {τ τ₁ τ₂} → τ ⊔ □ × □ ≡ τ₁ × τ₂ → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ ⌋
unmatch×-min m (□ isSlice ⊑□) (□ isSlice ⊑□) = ⊥ₛ
unmatch×-min m s₁ s₂ = unmatch× m s₁ s₂

-- unmatch⇒-min: same pattern for function types
unmatch⇒-min : ∀ {τ τ₁ τ₂} → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂ → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ ⌋
unmatch⇒-min m (□ isSlice ⊑□) (□ isSlice ⊑□) = ⊥ₛ
unmatch⇒-min m s₁ s₂ = unmatch⇒ m s₁ s₂

dom⇒ₛ : ∀ {τ τ₁ τ₂} → ⌊ τ ⌋ → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂ → ⌊ τ₁ ⌋
dom⇒ₛ ψ m = let _ , _ , _ , p , _ = ⊔-⇒-⊑ (ψ .proof) m in ↑ p

cod⇒ₛ : ∀ {τ τ₁ τ₂} → ⌊ τ ⌋ → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂ → ⌊ τ₂ ⌋
cod⇒ₛ ψ m = let _ , _ , _ , _ , q = ⊔-⇒-⊑ (ψ .proof) m in ↑ q

match⇒ₛ : ∀ {τ τ₁ τ₂} → (ψ : ⌊ τ ⌋) → (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂)
         → ψ .↓ ⊔ □ ⇒ □ ≡ (dom⇒ₛ ψ m) .↓ ⇒ (cod⇒ₛ ψ m) .↓
match⇒ₛ ψ m = let _ , _ , m' , _ , _ = ⊔-⇒-⊑ (ψ .proof) m in m'

fst×ₛ' : ∀ {τ τ₁ τ₂} → ⌊ τ ⌋ → τ ⊔ □ × □ ≡ τ₁ × τ₂ → ⌊ τ₁ ⌋
fst×ₛ' ψ m = let _ , _ , _ , p , _ = ⊔-×-⊑ (ψ .proof) m in ↑ p

snd×ₛ : ∀ {τ τ₁ τ₂} → ⌊ τ ⌋ → τ ⊔ □ × □ ≡ τ₁ × τ₂ → ⌊ τ₂ ⌋
snd×ₛ ψ m = let _ , _ , _ , _ , q = ⊔-×-⊑ (ψ .proof) m in ↑ q

match×ₛ : ∀ {τ τ₁ τ₂} → (ψ : ⌊ τ ⌋) → (m : τ ⊔ □ × □ ≡ τ₁ × τ₂)
         → ψ .↓ ⊔ (□ × □) ≡ ((fst×ₛ' ψ m) .↓) × ((snd×ₛ ψ m) .↓)
match×ₛ ψ m = let _ , _ , m' , _ , _ = ⊔-×-⊑ (ψ .proof) m in m'

body∀ₛ : ∀ {τ τ'} → ⌊ τ ⌋ → τ ⊔ ∀· □ ≡ ∀· τ' → ⌊ τ' ⌋
body∀ₛ ψ m = let _ , _ , p = ⊔-∀-⊑ (ψ .proof) m in ↑ p

match∀ₛ : ∀ {τ τ'} → (ψ : ⌊ τ ⌋) → (m : τ ⊔ ∀· □ ≡ ∀· τ')
         → ψ .↓ ⊔ ∀· □ ≡ ∀· ((body∀ₛ ψ m) .↓)
match∀ₛ ψ m = let _ , m' , _ = ⊔-∀-⊑ (ψ .proof) m in m'

fst+ₛ' : ∀ {τ τ₁ τ₂} → ⌊ τ ⌋ → τ ⊔ □ + □ ≡ τ₁ + τ₂ → ⌊ τ₁ ⌋
fst+ₛ' ψ m = let _ , _ , _ , p , _ = ⊔-+-⊑ (ψ .proof) m in ↑ p

snd+ₛ' : ∀ {τ τ₁ τ₂} → ⌊ τ ⌋ → τ ⊔ □ + □ ≡ τ₁ + τ₂ → ⌊ τ₂ ⌋
snd+ₛ' ψ m = let _ , _ , _ , _ , q = ⊔-+-⊑ (ψ .proof) m in ↑ q

match+ₛ : ∀ {τ τ₁ τ₂} → (ψ : ⌊ τ ⌋) → (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
         → ψ .↓ ⊔ □ + □ ≡ (fst+ₛ' ψ m) .↓ + (snd+ₛ' ψ m) .↓
match+ₛ ψ m = let _ , _ , m' , _ , _ = ⊔-+-⊑ (ψ .proof) m in m'

private
  subst-↓-pre : ∀ {x y : Typ} (eq : x ≡ y) (s : ⌊ x ⌋) → (subst ⌊_⌋ eq s) .↓ ≡ s .↓
  subst-↓-pre refl _ = refl

fst+ₛ'-⊔ : ∀ {τ τ₁ τ₂} (s : ⌊ τ ⌋) (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
    {τ' τ₁' τ₂'} → s .↓ ⊑t τ' → τ' ⊔ □ + □ ≡ τ₁' + τ₂'
    → (fst+ₛ' s m) .↓ ⊑t τ₁'
fst+ₛ'-⊔ (□ isSlice ⊑□) _ _ _ = ⊑□
fst+ₛ'-⊔ {τ_a + τ_b} ((x + y) isSlice ⊑+ {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m
    (⊑+ {τ₁' = a'} {τ₂' = b'} p _) m'
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m | refl ← m' = p

snd+ₛ'-⊔ : ∀ {τ τ₁ τ₂} (s : ⌊ τ ⌋) (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
    {τ' τ₁' τ₂'} → s .↓ ⊑t τ' → τ' ⊔ □ + □ ≡ τ₁' + τ₂'
    → (snd+ₛ' s m) .↓ ⊑t τ₂'
snd+ₛ'-⊔ (□ isSlice ⊑□) _ _ _ = ⊑□
snd+ₛ'-⊔ {τ_a + τ_b} ((x + y) isSlice ⊑+ {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m
    (⊑+ {τ₁' = a'} {τ₂' = b'} _ q) m'
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m | refl ← m' = q

+-proj-fst-mono : ∀ {τ τ₁ τ₂ τ₀ τ_a τ_b} (ψ₀ : ⌊ τ ⌋)
    (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) → τ₀ ⊑t ψ₀ .↓ → τ₀ ⊔ □ + □ ≡ τ_a + τ_b
    → τ_a ⊑t (fst+ₛ' ψ₀ m) .↓
+-proj-fst-mono (□ isSlice ⊑□) _ ⊑□ refl = ⊑□
+-proj-fst-mono {τ_a + τ_b} ((x + y) isSlice ⊑+ {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m ⊑□ refl
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
  with refl ← m = ⊑□
+-proj-fst-mono {τ_a + τ_b} ((x + y) isSlice ⊑+ {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m
    (⊑+ {τ₁ = c} {τ₂ = d} p _) τ₀eq
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
        | ⊔t-zeroᵣ {c} | ⊔t-zeroᵣ {d}
  with refl ← m | refl ← τ₀eq = p

+-proj-snd-mono : ∀ {τ τ₁ τ₂ τ₀ τ_a τ_b} (ψ₀ : ⌊ τ ⌋)
    (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) → τ₀ ⊑t ψ₀ .↓ → τ₀ ⊔ □ + □ ≡ τ_a + τ_b
    → τ_b ⊑t (snd+ₛ' ψ₀ m) .↓
+-proj-snd-mono (□ isSlice ⊑□) _ ⊑□ refl = ⊑□
+-proj-snd-mono {τ_a + τ_b} ((x + y) isSlice ⊑+ {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m ⊑□ refl
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
  with refl ← m = ⊑□
+-proj-snd-mono {τ_a + τ_b} ((x + y) isSlice ⊑+ {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m
    (⊑+ {τ₁ = c} {τ₂ = d} _ q) τ₀eq
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
        | ⊔t-zeroᵣ {c} | ⊔t-zeroᵣ {d}
  with refl ← m | refl ← τ₀eq = q

fst-from-unmatch+ : ∀ {τ_a τ_b τ₁ τ₂ a b} (m : (τ_a + τ_b) ⊔ □ + □ ≡ τ₁ + τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
    → (unmatch+ {τ_a + τ_b} m s₁ s₂) .↓ ⊑t a + b → s₁ .↓ ⊑t a
fst-from-unmatch+ {τ_a} {τ_b} refl s₁ s₂ hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
  with hyp
... | ⊑+ p _ = p

snd-from-unmatch+ : ∀ {τ_a τ_b τ₁ τ₂ a b} (m : (τ_a + τ_b) ⊔ □ + □ ≡ τ₁ + τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
    → (unmatch+ {τ_a + τ_b} m s₁ s₂) .↓ ⊑t a + b → s₂ .↓ ⊑t b
snd-from-unmatch+ {τ_a} {τ_b} refl s₁ s₂ hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
  with hyp
... | ⊑+ _ q = q

fst-from-unmatch+min : ∀ {τ_a τ_b τ₁ τ₂ a b} (m : (τ_a + τ_b) ⊔ □ + □ ≡ τ₁ + τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
    → (unmatch+-min {τ_a + τ_b} m s₁ s₂) .↓ ⊑t a + b → s₁ .↓ ⊑t a
fst-from-unmatch+min refl (□ isSlice ⊑□) _ _ = ⊑□
fst-from-unmatch+min {Typ.*} {τ_b}  refl s₁@(_ isSlice ⊑*)      s₂ hyp = fst-from-unmatch+ {Typ.*}  {τ_b} refl s₁ s₂ hyp
fst-from-unmatch+min {⟨ n ⟩} {τ_b}  refl s₁@(_ isSlice ⊑Var)    s₂ hyp = fst-from-unmatch+ {⟨ n ⟩}  {τ_b} refl s₁ s₂ hyp
fst-from-unmatch+min {c + d} {τ_b}  refl s₁@(_ isSlice ⊑+ _ _) s₂ hyp = fst-from-unmatch+ {c + d}  {τ_b} refl s₁ s₂ hyp
fst-from-unmatch+min {c × d} {τ_b}  refl s₁@(_ isSlice ⊑× _ _) s₂ hyp = fst-from-unmatch+ {c × d}  {τ_b} refl s₁ s₂ hyp
fst-from-unmatch+min {c ⇒ d} {τ_b}  refl s₁@(_ isSlice ⊑⇒ _ _) s₂ hyp = fst-from-unmatch+ {c ⇒ d}  {τ_b} refl s₁ s₂ hyp
fst-from-unmatch+min {∀· c}  {τ_b}  refl s₁@(_ isSlice ⊑∀ _)   s₂ hyp = fst-from-unmatch+ {∀· c}   {τ_b} refl s₁ s₂ hyp

snd-from-unmatch+min : ∀ {τ_a τ_b τ₁ τ₂ a b} (m : (τ_a + τ_b) ⊔ □ + □ ≡ τ₁ + τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
    → (unmatch+-min {τ_a + τ_b} m s₁ s₂) .↓ ⊑t a + b → s₂ .↓ ⊑t b
snd-from-unmatch+min refl _ (□ isSlice ⊑□) _ = ⊑□
snd-from-unmatch+min {Typ.*} {τ_b} refl s₁@(_ isSlice ⊑*)      s₂ hyp = snd-from-unmatch+ {Typ.*} {τ_b} refl s₁ s₂ hyp
snd-from-unmatch+min {⟨ n ⟩} {τ_b} refl s₁@(_ isSlice ⊑Var)    s₂ hyp = snd-from-unmatch+ {⟨ n ⟩} {τ_b} refl s₁ s₂ hyp
snd-from-unmatch+min {c + d} {τ_b} refl s₁@(_ isSlice ⊑+ _ _) s₂ hyp = snd-from-unmatch+ {c + d} {τ_b} refl s₁ s₂ hyp
snd-from-unmatch+min {c × d} {τ_b} refl s₁@(_ isSlice ⊑× _ _) s₂ hyp = snd-from-unmatch+ {c × d} {τ_b} refl s₁ s₂ hyp
snd-from-unmatch+min {c ⇒ d} {τ_b} refl s₁@(_ isSlice ⊑⇒ _ _) s₂ hyp = snd-from-unmatch+ {c ⇒ d} {τ_b} refl s₁ s₂ hyp
snd-from-unmatch+min {∀· c}  {τ_b} refl s₁@(_ isSlice ⊑∀ _)   s₂ hyp = snd-from-unmatch+ {∀· c}  {τ_b} refl s₁ s₂ hyp
snd-from-unmatch+min {τ_a} {Typ.*}  refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑*)      hyp = snd-from-unmatch+ {τ_a} {Typ.*}  refl s₁ s₂ hyp
snd-from-unmatch+min {τ_a} {⟨ n ⟩}  refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑Var)    hyp = snd-from-unmatch+ {τ_a} {⟨ n ⟩}  refl s₁ s₂ hyp
snd-from-unmatch+min {τ_a} {c + d}  refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑+ _ _) hyp = snd-from-unmatch+ {τ_a} {c + d}  refl s₁ s₂ hyp
snd-from-unmatch+min {τ_a} {c × d}  refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑× _ _) hyp = snd-from-unmatch+ {τ_a} {c × d}  refl s₁ s₂ hyp
snd-from-unmatch+min {τ_a} {c ⇒ d}  refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑⇒ _ _) hyp = snd-from-unmatch+ {τ_a} {c ⇒ d}  refl s₁ s₂ hyp
snd-from-unmatch+min {τ_a} {∀· c}   refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑∀ _)   hyp = snd-from-unmatch+ {τ_a} {∀· c}   refl s₁ s₂ hyp

fst-unmatch+min-t⊥-absurd : ∀ {τ_a τ_b τ₁ τ₂} (m : (τ_a + τ_b) ⊔ □ + □ ≡ τ₁ + τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
    → (unmatch+ {τ_a + τ_b} m s₁ s₂) .↓ ⊑t □ → ⊥
fst-unmatch+min-t⊥-absurd {τ_a} {τ_b} refl s₁ s₂ hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
  with () ← hyp

fst-from-unmatch+min-t⊥ : ∀ {τ_a τ_b τ₁ τ₂} (m : (τ_a + τ_b) ⊔ □ + □ ≡ τ₁ + τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
    → (unmatch+-min {τ_a + τ_b} m s₁ s₂) .↓ ⊑t □ → s₁ .↓ ⊑t □
fst-from-unmatch+min-t⊥ refl (□ isSlice ⊑□) _ _ = ⊑□
fst-from-unmatch+min-t⊥ {Typ.*} {τ_b} refl s₁@(_ isSlice ⊑*)      s₂ hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {Typ.*} {τ_b} refl s₁ s₂ hyp)
fst-from-unmatch+min-t⊥ {⟨ n ⟩} {τ_b} refl s₁@(_ isSlice ⊑Var)    s₂ hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {⟨ n ⟩} {τ_b} refl s₁ s₂ hyp)
fst-from-unmatch+min-t⊥ {c + d} {τ_b} refl s₁@(_ isSlice ⊑+ _ _) s₂ hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {c + d} {τ_b} refl s₁ s₂ hyp)
fst-from-unmatch+min-t⊥ {c × d} {τ_b} refl s₁@(_ isSlice ⊑× _ _) s₂ hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {c × d} {τ_b} refl s₁ s₂ hyp)
fst-from-unmatch+min-t⊥ {c ⇒ d} {τ_b} refl s₁@(_ isSlice ⊑⇒ _ _) s₂ hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {c ⇒ d} {τ_b} refl s₁ s₂ hyp)
fst-from-unmatch+min-t⊥ {∀· c}  {τ_b} refl s₁@(_ isSlice ⊑∀ _)   s₂ hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {∀· c}  {τ_b} refl s₁ s₂ hyp)

snd-from-unmatch+min-t⊥ : ∀ {τ_a τ_b τ₁ τ₂} (m : (τ_a + τ_b) ⊔ □ + □ ≡ τ₁ + τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
    → (unmatch+-min {τ_a + τ_b} m s₁ s₂) .↓ ⊑t □ → s₂ .↓ ⊑t □
snd-from-unmatch+min-t⊥ refl _ (□ isSlice ⊑□) _ = ⊑□
snd-from-unmatch+min-t⊥ {Typ.*} {τ_b} refl s₁@(_ isSlice ⊑*)      s₂ hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {Typ.*} {τ_b} refl s₁ s₂ hyp)
snd-from-unmatch+min-t⊥ {⟨ n ⟩} {τ_b} refl s₁@(_ isSlice ⊑Var)    s₂ hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {⟨ n ⟩} {τ_b} refl s₁ s₂ hyp)
snd-from-unmatch+min-t⊥ {c + d} {τ_b} refl s₁@(_ isSlice ⊑+ _ _) s₂ hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {c + d} {τ_b} refl s₁ s₂ hyp)
snd-from-unmatch+min-t⊥ {c × d} {τ_b} refl s₁@(_ isSlice ⊑× _ _) s₂ hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {c × d} {τ_b} refl s₁ s₂ hyp)
snd-from-unmatch+min-t⊥ {c ⇒ d} {τ_b} refl s₁@(_ isSlice ⊑⇒ _ _) s₂ hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {c ⇒ d} {τ_b} refl s₁ s₂ hyp)
snd-from-unmatch+min-t⊥ {∀· c}  {τ_b} refl s₁@(_ isSlice ⊑∀ _)   s₂ hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {∀· c}  {τ_b} refl s₁ s₂ hyp)
snd-from-unmatch+min-t⊥ {τ_a} {Typ.*} refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑*)      hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {τ_a} {Typ.*} refl s₁ s₂ hyp)
snd-from-unmatch+min-t⊥ {τ_a} {⟨ n ⟩} refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑Var)    hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {τ_a} {⟨ n ⟩} refl s₁ s₂ hyp)
snd-from-unmatch+min-t⊥ {τ_a} {c + d} refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑+ _ _) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {τ_a} {c + d} refl s₁ s₂ hyp)
snd-from-unmatch+min-t⊥ {τ_a} {c × d} refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑× _ _) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {τ_a} {c × d} refl s₁ s₂ hyp)
snd-from-unmatch+min-t⊥ {τ_a} {c ⇒ d} refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑⇒ _ _) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {τ_a} {c ⇒ d} refl s₁ s₂ hyp)
snd-from-unmatch+min-t⊥ {τ_a} {∀· c}  refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑∀ _)   hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {τ_a} {∀· c}  refl s₁ s₂ hyp)

fst-unmatch+-min : ∀ (τ : Typ) {τ₁ τ₂} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋) (t : ⌊ τ ⌋)
    → (unmatch+-min {τ} m s₁ s₂) .↓ ⊑t t .↓ → s₁ .↓ ⊑t (fst+ₛ' t m) .↓
fst-unmatch+-min □ refl (□ isSlice ⊑□) (□ isSlice ⊑□) (□ isSlice ⊑□) _ = ⊑□
fst-unmatch+-min (_ + _) refl (□ isSlice ⊑□) _ _ _ = ⊑□
fst-unmatch+-min (Typ.* + τ_b) refl s₁@(_ isSlice ⊑*)      s₂ ((x + y) isSlice ⊑+ {τ₁' = .Typ.*} {τ₂' = .τ_b} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {Typ.*}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_b}
  with ⊑+ p _ ← hyp = p
fst-unmatch+-min (⟨ n ⟩ + τ_b) refl s₁@(_ isSlice ⊑Var)    s₂ ((x + y) isSlice ⊑+ {τ₁' = .(⟨ n ⟩)} {τ₂' = .τ_b} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {⟨ n ⟩}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_b}
  with ⊑+ p _ ← hyp = p
fst-unmatch+-min ((c + d) + τ_b) refl s₁@(_ isSlice ⊑+ _ _) s₂ ((x + y) isSlice ⊑+ {τ₁' = .(c + d)} {τ₂' = .τ_b} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {c + d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_b}
  with ⊑+ p _ ← hyp = p
fst-unmatch+-min ((c × d) + τ_b) refl s₁@(_ isSlice ⊑× _ _) s₂ ((x + y) isSlice ⊑+ {τ₁' = .(c × d)} {τ₂' = .τ_b} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {c × d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_b}
  with ⊑+ p _ ← hyp = p
fst-unmatch+-min ((c ⇒ d) + τ_b) refl s₁@(_ isSlice ⊑⇒ _ _) s₂ ((x + y) isSlice ⊑+ {τ₁' = .(c ⇒ d)} {τ₂' = .τ_b} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {c ⇒ d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_b}
  with ⊑+ p _ ← hyp = p
fst-unmatch+-min ((∀· c) + τ_b) refl s₁@(_ isSlice ⊑∀ _)   s₂ ((x + y) isSlice ⊑+ {τ₁' = .(∀· c)} {τ₂' = .τ_b} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {∀· c}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_b}
  with ⊑+ p _ ← hyp = p
fst-unmatch+-min (Typ.* + τ_b) refl s₁@(_ isSlice ⊑*)      s₂ (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {Typ.*} {τ_b} refl s₁ s₂ hyp)
fst-unmatch+-min (⟨ n ⟩ + τ_b) refl s₁@(_ isSlice ⊑Var)    s₂ (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {⟨ n ⟩} {τ_b} refl s₁ s₂ hyp)
fst-unmatch+-min ((c + d) + τ_b) refl s₁@(_ isSlice ⊑+ _ _) s₂ (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {c + d} {τ_b} refl s₁ s₂ hyp)
fst-unmatch+-min ((c × d) + τ_b) refl s₁@(_ isSlice ⊑× _ _) s₂ (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {c × d} {τ_b} refl s₁ s₂ hyp)
fst-unmatch+-min ((c ⇒ d) + τ_b) refl s₁@(_ isSlice ⊑⇒ _ _) s₂ (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {c ⇒ d} {τ_b} refl s₁ s₂ hyp)
fst-unmatch+-min ((∀· c) + τ_b) refl s₁@(_ isSlice ⊑∀ _)   s₂ (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {∀· c} {τ_b} refl s₁ s₂ hyp)

snd-unmatch+-min : ∀ (τ : Typ) {τ₁ τ₂} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋) (t : ⌊ τ ⌋)
    → (unmatch+-min {τ} m s₁ s₂) .↓ ⊑t t .↓ → s₂ .↓ ⊑t (snd+ₛ' t m) .↓
snd-unmatch+-min □ refl (□ isSlice ⊑□) (□ isSlice ⊑□) (□ isSlice ⊑□) _ = ⊑□
snd-unmatch+-min (_ + _) refl _ (□ isSlice ⊑□) _ _ = ⊑□
snd-unmatch+-min (Typ.* + τ_b) refl s₁@(_ isSlice ⊑*)      s₂ ((x + y) isSlice ⊑+ {τ₁' = .Typ.*} {τ₂' = .τ_b} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {Typ.*}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_b}
  with ⊑+ _ q ← hyp = q
snd-unmatch+-min (⟨ n ⟩ + τ_b) refl s₁@(_ isSlice ⊑Var)    s₂ ((x + y) isSlice ⊑+ {τ₁' = .(⟨ n ⟩)} {τ₂' = .τ_b} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {⟨ n ⟩}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_b}
  with ⊑+ _ q ← hyp = q
snd-unmatch+-min ((c + d) + τ_b) refl s₁@(_ isSlice ⊑+ _ _) s₂ ((x + y) isSlice ⊑+ {τ₁' = .(c + d)} {τ₂' = .τ_b} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {c + d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_b}
  with ⊑+ _ q ← hyp = q
snd-unmatch+-min ((c × d) + τ_b) refl s₁@(_ isSlice ⊑× _ _) s₂ ((x + y) isSlice ⊑+ {τ₁' = .(c × d)} {τ₂' = .τ_b} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {c × d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_b}
  with ⊑+ _ q ← hyp = q
snd-unmatch+-min ((c ⇒ d) + τ_b) refl s₁@(_ isSlice ⊑⇒ _ _) s₂ ((x + y) isSlice ⊑+ {τ₁' = .(c ⇒ d)} {τ₂' = .τ_b} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {c ⇒ d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_b}
  with ⊑+ _ q ← hyp = q
snd-unmatch+-min ((∀· c) + τ_b) refl s₁@(_ isSlice ⊑∀ _)   s₂ ((x + y) isSlice ⊑+ {τ₁' = .(∀· c)} {τ₂' = .τ_b} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {∀· c}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_b}
  with ⊑+ _ q ← hyp = q
snd-unmatch+-min (τ_a + Typ.*) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑*)      ((x + y) isSlice ⊑+ {τ₁' = .τ_a} {τ₂' = .Typ.*} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {Typ.*}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a}
  with ⊑+ _ q ← hyp = q
snd-unmatch+-min (τ_a + ⟨ n ⟩) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑Var)    ((x + y) isSlice ⊑+ {τ₁' = .τ_a} {τ₂' = .(⟨ n ⟩)} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {⟨ n ⟩}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a}
  with ⊑+ _ q ← hyp = q
snd-unmatch+-min (τ_a + (c + d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑+ _ _) ((x + y) isSlice ⊑+ {τ₁' = .τ_a} {τ₂' = .(c + d)} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {c + d}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a}
  with ⊑+ _ q ← hyp = q
snd-unmatch+-min (τ_a + (c × d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑× _ _) ((x + y) isSlice ⊑+ {τ₁' = .τ_a} {τ₂' = .(c × d)} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {c × d}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a}
  with ⊑+ _ q ← hyp = q
snd-unmatch+-min (τ_a + (c ⇒ d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑⇒ _ _) ((x + y) isSlice ⊑+ {τ₁' = .τ_a} {τ₂' = .(c ⇒ d)} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {c ⇒ d}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a}
  with ⊑+ _ q ← hyp = q
snd-unmatch+-min (τ_a + (∀· c)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑∀ _)   ((x + y) isSlice ⊑+ {τ₁' = .τ_a} {τ₂' = .(∀· c)} _ _) hyp
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {∀· c}) s₂
        | ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a}
  with ⊑+ _ q ← hyp = q
snd-unmatch+-min (Typ.* + τ_b) refl s₁@(_ isSlice ⊑*)      s₂ (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {Typ.*} {τ_b} refl s₁ s₂ hyp)
snd-unmatch+-min (⟨ n ⟩ + τ_b) refl s₁@(_ isSlice ⊑Var)    s₂ (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {⟨ n ⟩} {τ_b} refl s₁ s₂ hyp)
snd-unmatch+-min ((c + d) + τ_b) refl s₁@(_ isSlice ⊑+ _ _) s₂ (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {c + d} {τ_b} refl s₁ s₂ hyp)
snd-unmatch+-min ((c × d) + τ_b) refl s₁@(_ isSlice ⊑× _ _) s₂ (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {c × d} {τ_b} refl s₁ s₂ hyp)
snd-unmatch+-min ((c ⇒ d) + τ_b) refl s₁@(_ isSlice ⊑⇒ _ _) s₂ (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {c ⇒ d} {τ_b} refl s₁ s₂ hyp)
snd-unmatch+-min ((∀· c) + τ_b) refl s₁@(_ isSlice ⊑∀ _)   s₂ (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {∀· c} {τ_b} refl s₁ s₂ hyp)
snd-unmatch+-min (τ_a + Typ.*) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑*)      (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {τ_a} {Typ.*} refl s₁ s₂ hyp)
snd-unmatch+-min (τ_a + ⟨ n ⟩) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑Var)    (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {τ_a} {⟨ n ⟩} refl s₁ s₂ hyp)
snd-unmatch+-min (τ_a + (c + d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑+ _ _) (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {τ_a} {c + d} refl s₁ s₂ hyp)
snd-unmatch+-min (τ_a + (c × d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑× _ _) (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {τ_a} {c × d} refl s₁ s₂ hyp)
snd-unmatch+-min (τ_a + (c ⇒ d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑⇒ _ _) (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {τ_a} {c ⇒ d} refl s₁ s₂ hyp)
snd-unmatch+-min (τ_a + (∀· c)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑∀ _)   (□ isSlice ⊑□) hyp = ⊥-elim (fst-unmatch+min-t⊥-absurd {τ_a} {∀· c} refl s₁ s₂ hyp)

unmatch+-min-⊑ : ∀ (τ : Typ) {τ₁ τ₂ τ' τ₃' τ₄'} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
    → τ' ⊑t τ → τ' ⊔ (□ + □) ≡ τ₃' + τ₄'
    → s₁ .↓ ⊑t τ₃' → s₂ .↓ ⊑t τ₄'
    → (unmatch+-min {τ} m s₁ s₂) .↓ ⊑t τ'
unmatch+-min-⊑ □ refl (□ isSlice ⊑□) (□ isSlice ⊑□) _ _ _ _ = ⊑□
unmatch+-min-⊑ (_ + _) refl (□ isSlice ⊑□) (□ isSlice ⊑□) _ _ _ _ = ⊑□
unmatch+-min-⊑ (Typ.* + τ_b) refl s₁@(_ isSlice ⊑*) s₂ (⊑+ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {Typ.*}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑+ s₁⊑ s₂⊑
unmatch+-min-⊑ (⟨ n ⟩ + τ_b) refl s₁@(_ isSlice ⊑Var) s₂ (⊑+ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {⟨ n ⟩}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑+ s₁⊑ s₂⊑
unmatch+-min-⊑ ((c + d) + τ_b) refl s₁@(_ isSlice ⊑+ _ _) s₂ (⊑+ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {c + d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑+ s₁⊑ s₂⊑
unmatch+-min-⊑ ((c × d) + τ_b) refl s₁@(_ isSlice ⊑× _ _) s₂ (⊑+ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {c × d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑+ s₁⊑ s₂⊑
unmatch+-min-⊑ ((c ⇒ d) + τ_b) refl s₁@(_ isSlice ⊑⇒ _ _) s₂ (⊑+ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {c ⇒ d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑+ s₁⊑ s₂⊑
unmatch+-min-⊑ ((∀· c) + τ_b) refl s₁@(_ isSlice ⊑∀ _) s₂ (⊑+ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {∀· c}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑+ s₁⊑ s₂⊑
unmatch+-min-⊑ (τ_a + Typ.*) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑*) (⊑+ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {Typ.*}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑+ s₁⊑ s₂⊑
unmatch+-min-⊑ (τ_a + ⟨ n ⟩) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑Var) (⊑+ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {⟨ n ⟩}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑+ s₁⊑ s₂⊑
unmatch+-min-⊑ (τ_a + (c + d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑+ _ _) (⊑+ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {c + d}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑+ s₁⊑ s₂⊑
unmatch+-min-⊑ (τ_a + (c × d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑× _ _) (⊑+ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {c × d}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑+ s₁⊑ s₂⊑
unmatch+-min-⊑ (τ_a + (c ⇒ d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑⇒ _ _) (⊑+ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {c ⇒ d}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑+ s₁⊑ s₂⊑
unmatch+-min-⊑ (τ_a + (∀· c)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑∀ _) (⊑+ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {∀· c}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑+ s₁⊑ s₂⊑
unmatch+-min-⊑ (Typ.* + τ_b) refl s₁@(_ isSlice ⊑*) s₂ ⊑□ refl () _
unmatch+-min-⊑ (⟨ n ⟩ + τ_b) refl s₁@(_ isSlice ⊑Var) s₂ ⊑□ refl () _
unmatch+-min-⊑ ((c + d) + τ_b) refl s₁@(_ isSlice ⊑+ _ _) s₂ ⊑□ refl () _
unmatch+-min-⊑ ((c × d) + τ_b) refl s₁@(_ isSlice ⊑× _ _) s₂ ⊑□ refl () _
unmatch+-min-⊑ ((c ⇒ d) + τ_b) refl s₁@(_ isSlice ⊑⇒ _ _) s₂ ⊑□ refl () _
unmatch+-min-⊑ ((∀· c) + τ_b) refl s₁@(_ isSlice ⊑∀ _) s₂ ⊑□ refl () _
unmatch+-min-⊑ (τ_a + Typ.*) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑*) ⊑□ refl _ ()
unmatch+-min-⊑ (τ_a + ⟨ n ⟩) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑Var) ⊑□ refl _ ()
unmatch+-min-⊑ (τ_a + (c + d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑+ _ _) ⊑□ refl _ ()
unmatch+-min-⊑ (τ_a + (c × d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑× _ _) ⊑□ refl _ ()
unmatch+-min-⊑ (τ_a + (c ⇒ d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑⇒ _ _) ⊑□ refl _ ()
unmatch+-min-⊑ (τ_a + (∀· c)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑∀ _) ⊑□ refl _ ()

unmatch×-min-⊑ : ∀ (τ : Typ) {τ₁ τ₂ τ' τ₃' τ₄'} (m : τ ⊔ □ × □ ≡ τ₁ × τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
    → τ' ⊑t τ → τ' ⊔ (□ × □) ≡ τ₃' × τ₄'
    → s₁ .↓ ⊑t τ₃' → s₂ .↓ ⊑t τ₄'
    → (unmatch×-min {τ} m s₁ s₂) .↓ ⊑t τ'
unmatch×-min-⊑ □ refl (□ isSlice ⊑□) (□ isSlice ⊑□) _ _ _ _ = ⊑□
unmatch×-min-⊑ (_ × _) refl (□ isSlice ⊑□) (□ isSlice ⊑□) _ _ _ _ = ⊑□
unmatch×-min-⊑ (Typ.* × τ_b) refl s₁@(_ isSlice ⊑*) s₂ (⊑× {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {Typ.*}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑× s₁⊑ s₂⊑
unmatch×-min-⊑ (⟨ n ⟩ × τ_b) refl s₁@(_ isSlice ⊑Var) s₂ (⊑× {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {⟨ n ⟩}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑× s₁⊑ s₂⊑
unmatch×-min-⊑ ((c + d) × τ_b) refl s₁@(_ isSlice ⊑+ _ _) s₂ (⊑× {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {c + d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑× s₁⊑ s₂⊑
unmatch×-min-⊑ ((c × d) × τ_b) refl s₁@(_ isSlice ⊑× _ _) s₂ (⊑× {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {c × d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑× s₁⊑ s₂⊑
unmatch×-min-⊑ ((c ⇒ d) × τ_b) refl s₁@(_ isSlice ⊑⇒ _ _) s₂ (⊑× {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {c ⇒ d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑× s₁⊑ s₂⊑
unmatch×-min-⊑ ((∀· c) × τ_b) refl s₁@(_ isSlice ⊑∀ _) s₂ (⊑× {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {∀· c}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑× s₁⊑ s₂⊑
unmatch×-min-⊑ (τ_a × Typ.*) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑*) (⊑× {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {Typ.*}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑× s₁⊑ s₂⊑
unmatch×-min-⊑ (τ_a × ⟨ n ⟩) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑Var) (⊑× {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {⟨ n ⟩}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑× s₁⊑ s₂⊑
unmatch×-min-⊑ (τ_a × (c + d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑+ _ _) (⊑× {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {c + d}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑× s₁⊑ s₂⊑
unmatch×-min-⊑ (τ_a × (c × d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑× _ _) (⊑× {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {c × d}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑× s₁⊑ s₂⊑
unmatch×-min-⊑ (τ_a × (c ⇒ d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑⇒ _ _) (⊑× {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {c ⇒ d}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑× s₁⊑ s₂⊑
unmatch×-min-⊑ (τ_a × (∀· c)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑∀ _) (⊑× {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {∀· c}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑× s₁⊑ s₂⊑
unmatch×-min-⊑ (Typ.* × τ_b) refl s₁@(_ isSlice ⊑*) s₂ ⊑□ refl () _
unmatch×-min-⊑ (⟨ n ⟩ × τ_b) refl s₁@(_ isSlice ⊑Var) s₂ ⊑□ refl () _
unmatch×-min-⊑ ((c + d) × τ_b) refl s₁@(_ isSlice ⊑+ _ _) s₂ ⊑□ refl () _
unmatch×-min-⊑ ((c × d) × τ_b) refl s₁@(_ isSlice ⊑× _ _) s₂ ⊑□ refl () _
unmatch×-min-⊑ ((c ⇒ d) × τ_b) refl s₁@(_ isSlice ⊑⇒ _ _) s₂ ⊑□ refl () _
unmatch×-min-⊑ ((∀· c) × τ_b) refl s₁@(_ isSlice ⊑∀ _) s₂ ⊑□ refl () _
unmatch×-min-⊑ (τ_a × Typ.*) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑*) ⊑□ refl _ ()
unmatch×-min-⊑ (τ_a × ⟨ n ⟩) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑Var) ⊑□ refl _ ()
unmatch×-min-⊑ (τ_a × (c + d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑+ _ _) ⊑□ refl _ ()
unmatch×-min-⊑ (τ_a × (c × d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑× _ _) ⊑□ refl _ ()
unmatch×-min-⊑ (τ_a × (c ⇒ d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑⇒ _ _) ⊑□ refl _ ()
unmatch×-min-⊑ (τ_a × (∀· c)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑∀ _) ⊑□ refl _ ()

unmatch⇒-min-⊑ : ∀ (τ : Typ) {τ₁ τ₂ τ' τ₃' τ₄'} (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
    → τ' ⊑t τ → τ' ⊔ (□ ⇒ □) ≡ τ₃' ⇒ τ₄'
    → s₁ .↓ ⊑t τ₃' → s₂ .↓ ⊑t τ₄'
    → (unmatch⇒-min {τ} m s₁ s₂) .↓ ⊑t τ'
unmatch⇒-min-⊑ □ refl (□ isSlice ⊑□) (□ isSlice ⊑□) _ _ _ _ = ⊑□
unmatch⇒-min-⊑ (_ ⇒ _) refl (□ isSlice ⊑□) (□ isSlice ⊑□) _ _ _ _ = ⊑□
unmatch⇒-min-⊑ (Typ.* ⇒ τ_b) refl s₁@(_ isSlice ⊑*) s₂ (⊑⇒ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {Typ.*}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑⇒ s₁⊑ s₂⊑
unmatch⇒-min-⊑ (⟨ n ⟩ ⇒ τ_b) refl s₁@(_ isSlice ⊑Var) s₂ (⊑⇒ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {⟨ n ⟩}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑⇒ s₁⊑ s₂⊑
unmatch⇒-min-⊑ ((c + d) ⇒ τ_b) refl s₁@(_ isSlice ⊑+ _ _) s₂ (⊑⇒ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {c + d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑⇒ s₁⊑ s₂⊑
unmatch⇒-min-⊑ ((c × d) ⇒ τ_b) refl s₁@(_ isSlice ⊑× _ _) s₂ (⊑⇒ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {c × d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑⇒ s₁⊑ s₂⊑
unmatch⇒-min-⊑ ((c ⇒ d) ⇒ τ_b) refl s₁@(_ isSlice ⊑⇒ _ _) s₂ (⊑⇒ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {c ⇒ d}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑⇒ s₁⊑ s₂⊑
unmatch⇒-min-⊑ ((∀· c) ⇒ τ_b) refl s₁@(_ isSlice ⊑∀ _) s₂ (⊑⇒ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {∀· c}) s₁ | subst-↓-pre (⊔t-zeroᵣ {τ_b}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑⇒ s₁⊑ s₂⊑
unmatch⇒-min-⊑ (τ_a ⇒ Typ.*) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑*) (⊑⇒ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {Typ.*}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑⇒ s₁⊑ s₂⊑
unmatch⇒-min-⊑ (τ_a ⇒ ⟨ n ⟩) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑Var) (⊑⇒ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {⟨ n ⟩}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑⇒ s₁⊑ s₂⊑
unmatch⇒-min-⊑ (τ_a ⇒ (c + d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑+ _ _) (⊑⇒ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {c + d}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑⇒ s₁⊑ s₂⊑
unmatch⇒-min-⊑ (τ_a ⇒ (c × d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑× _ _) (⊑⇒ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {c × d}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑⇒ s₁⊑ s₂⊑
unmatch⇒-min-⊑ (τ_a ⇒ (c ⇒ d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑⇒ _ _) (⊑⇒ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {c ⇒ d}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑⇒ s₁⊑ s₂⊑
unmatch⇒-min-⊑ (τ_a ⇒ (∀· c)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑∀ _) (⊑⇒ {τ₁ = a'} {τ₂ = b'} _ _) m'-eq s₁⊑ s₂⊑
  rewrite subst-↓-pre (⊔t-zeroᵣ {τ_a}) s₁ | subst-↓-pre (⊔t-zeroᵣ {∀· c}) s₂
        | ⊔t-zeroᵣ {a'} | ⊔t-zeroᵣ {b'}
  with refl ← m'-eq = ⊑⇒ s₁⊑ s₂⊑
unmatch⇒-min-⊑ (Typ.* ⇒ τ_b) refl s₁@(_ isSlice ⊑*) s₂ ⊑□ refl () _
unmatch⇒-min-⊑ (⟨ n ⟩ ⇒ τ_b) refl s₁@(_ isSlice ⊑Var) s₂ ⊑□ refl () _
unmatch⇒-min-⊑ ((c + d) ⇒ τ_b) refl s₁@(_ isSlice ⊑+ _ _) s₂ ⊑□ refl () _
unmatch⇒-min-⊑ ((c × d) ⇒ τ_b) refl s₁@(_ isSlice ⊑× _ _) s₂ ⊑□ refl () _
unmatch⇒-min-⊑ ((c ⇒ d) ⇒ τ_b) refl s₁@(_ isSlice ⊑⇒ _ _) s₂ ⊑□ refl () _
unmatch⇒-min-⊑ ((∀· c) ⇒ τ_b) refl s₁@(_ isSlice ⊑∀ _) s₂ ⊑□ refl () _
unmatch⇒-min-⊑ (τ_a ⇒ Typ.*) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑*) ⊑□ refl _ ()
unmatch⇒-min-⊑ (τ_a ⇒ ⟨ n ⟩) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑Var) ⊑□ refl _ ()
unmatch⇒-min-⊑ (τ_a ⇒ (c + d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑+ _ _) ⊑□ refl _ ()
unmatch⇒-min-⊑ (τ_a ⇒ (c × d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑× _ _) ⊑□ refl _ ()
unmatch⇒-min-⊑ (τ_a ⇒ (c ⇒ d)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑⇒ _ _) ⊑□ refl _ ()
unmatch⇒-min-⊑ (τ_a ⇒ (∀· c)) refl s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑∀ _) ⊑□ refl _ ()

×-proj-fst-mono : ∀ {τ τ₁ τ₂ τ₀ τ_a τ_b} (ψ₀ : ⌊ τ ⌋)
    (m : τ ⊔ □ × □ ≡ τ₁ × τ₂) → τ₀ ⊑t ψ₀ .↓ → τ₀ ⊔ □ × □ ≡ τ_a × τ_b
    → τ_a ⊑t (fst×ₛ' ψ₀ m) .↓
×-proj-fst-mono (□ isSlice ⊑□) _ ⊑□ refl = ⊑□
×-proj-fst-mono {τ_a × τ_b} ((x × y) isSlice ⊑× {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m ⊑□ refl
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
  with refl ← m = ⊑□
×-proj-fst-mono {τ_a × τ_b} ((x × y) isSlice ⊑× {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m
    (⊑× {τ₁ = c} {τ₂ = d} p _) τ₀eq
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
        | ⊔t-zeroᵣ {c} | ⊔t-zeroᵣ {d}
  with refl ← m | refl ← τ₀eq = p

×-proj-snd-mono : ∀ {τ τ₁ τ₂ τ₀ τ_a τ_b} (ψ₀ : ⌊ τ ⌋)
    (m : τ ⊔ □ × □ ≡ τ₁ × τ₂) → τ₀ ⊑t ψ₀ .↓ → τ₀ ⊔ □ × □ ≡ τ_a × τ_b
    → τ_b ⊑t (snd×ₛ ψ₀ m) .↓
×-proj-snd-mono (□ isSlice ⊑□) _ ⊑□ refl = ⊑□
×-proj-snd-mono {τ_a × τ_b} ((x × y) isSlice ⊑× {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m ⊑□ refl
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
  with refl ← m = ⊑□
×-proj-snd-mono {τ_a × τ_b} ((x × y) isSlice ⊑× {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m
    (⊑× {τ₁ = c} {τ₂ = d} _ q) τ₀eq
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
        | ⊔t-zeroᵣ {c} | ⊔t-zeroᵣ {d}
  with refl ← m | refl ← τ₀eq = q

⇒-proj-dom-mono : ∀ {τ τ₁ τ₂ τ₀ τ_a τ_b} (ψ₀ : ⌊ τ ⌋)
    (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂) → τ₀ ⊑t ψ₀ .↓ → τ₀ ⊔ □ ⇒ □ ≡ τ_a ⇒ τ_b
    → τ_a ⊑t (dom⇒ₛ ψ₀ m) .↓
⇒-proj-dom-mono (□ isSlice ⊑□) _ ⊑□ refl = ⊑□
⇒-proj-dom-mono {τ_a ⇒ τ_b} ((x ⇒ y) isSlice ⊑⇒ {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m ⊑□ refl
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
  with refl ← m = ⊑□
⇒-proj-dom-mono {τ_a ⇒ τ_b} ((x ⇒ y) isSlice ⊑⇒ {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m
    (⊑⇒ {τ₁ = c} {τ₂ = d} p _) τ₀eq
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
        | ⊔t-zeroᵣ {c} | ⊔t-zeroᵣ {d}
  with refl ← m | refl ← τ₀eq = p

⇒-proj-cod-mono : ∀ {τ τ₁ τ₂ τ₀ τ_a τ_b} (ψ₀ : ⌊ τ ⌋)
    (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂) → τ₀ ⊑t ψ₀ .↓ → τ₀ ⊔ □ ⇒ □ ≡ τ_a ⇒ τ_b
    → τ_b ⊑t (cod⇒ₛ ψ₀ m) .↓
⇒-proj-cod-mono (□ isSlice ⊑□) _ ⊑□ refl = ⊑□
⇒-proj-cod-mono {τ_a ⇒ τ_b} ((x ⇒ y) isSlice ⊑⇒ {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m ⊑□ refl
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
  with refl ← m = ⊑□
⇒-proj-cod-mono {τ_a ⇒ τ_b} ((x ⇒ y) isSlice ⊑⇒ {τ₁' = .τ_a} {τ₂' = .τ_b} _ _) m
    (⊑⇒ {τ₁ = c} {τ₂ = d} _ q) τ₀eq
  rewrite ⊔t-zeroᵣ {x} | ⊔t-zeroᵣ {y} | ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b}
        | ⊔t-zeroᵣ {c} | ⊔t-zeroᵣ {d}
  with refl ← m | refl ← τ₀eq = q

-- Join of slices of consistent types
_⊔~ₛ_ : ∀ {τ₁ τ₂} → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → {c : τ₁ ~ τ₂} → ⌊ τ₁ ⊔ τ₂ ⌋
_⊔~ₛ_ ψ₁ ψ₂ {c} = ↑ (⊔-mono-⊑ c (ψ₁ .proof) (ψ₂ .proof))

-- unmatch precision inversion lemmas:
unmatch⇒-cod : ∀ {τ} → (q : ⌊ τ ⌋) → (ϕ : ⌊ τ ⌋)
             → q ⊑ₛ ϕ
             → ∀ {τ₁' τ₂'} → ϕ .↓ ⊔ □ ⇒ □ ≡ τ₁' ⇒ τ₂'
             → ∀ {τ₁'' τ₂''} → q .↓ ⊔ □ ⇒ □ ≡ τ₁'' ⇒ τ₂''
             → τ₂'' ⊑t τ₂'
unmatch⇒-cod q ϕ v m' m''
  with ⊔-⇒-⊑ v m'
... | _ , _ , eq , _ , p rewrite eq with refl ← m'' = p

unmatch×-fst : ∀ {τ} → (q : ⌊ τ ⌋) → (ϕ : ⌊ τ ⌋)
             → q ⊑ₛ ϕ
             → ∀ {τ₁' τ₂'} → ϕ .↓ ⊔ □ × □ ≡ τ₁' × τ₂'
             → ∀ {τ₁'' τ₂''} → q .↓ ⊔ □ × □ ≡ τ₁'' × τ₂''
             → τ₁'' ⊑t τ₁'
unmatch×-fst q ϕ v m' m''
  with ⊔-×-⊑ v m'
... | _ , _ , eq , p , _ rewrite eq with refl ← m'' = p

unmatch×-snd : ∀ {τ} → (q : ⌊ τ ⌋) → (ϕ : ⌊ τ ⌋)
             → q ⊑ₛ ϕ
             → ∀ {τ₁' τ₂'} → ϕ .↓ ⊔ □ × □ ≡ τ₁' × τ₂'
             → ∀ {τ₁'' τ₂''} → q .↓ ⊔ □ × □ ≡ τ₁'' × τ₂''
             → τ₂'' ⊑t τ₂'
unmatch×-snd q ϕ v m' m''
  with ⊔-×-⊑ v m'
... | _ , _ , eq , _ , p rewrite eq with refl ← m'' = p

private
  subst-↓ : ∀ {x y : Typ} (eq : x ≡ y) (s : ⌊ x ⌋) → (subst ⌊_⌋ eq s) .↓ ≡ s .↓
  subst-↓ refl _ = refl

  ⇒-inj-fst : ∀ {a b c d : Typ} → a ⇒ b ≡ c ⇒ d → a ≡ c
  ⇒-inj-fst refl = refl

  ⇒-inj-snd : ∀ {a b c d : Typ} → a ⇒ b ≡ c ⇒ d → b ≡ d
  ⇒-inj-snd refl = refl

  ×-inj-fst : ∀ {a b c d : Typ} → a × b ≡ c × d → a ≡ c
  ×-inj-fst refl = refl

  ×-inj-snd : ∀ {a b c d : Typ} → a × b ≡ c × d → b ≡ d
  ×-inj-snd refl = refl

  ∀-inj-body : ∀ {a c : Typ} → ∀· a ≡ ∀· c → a ≡ c
  ∀-inj-body refl = refl

-- ⇒-dom monotonicity (parallel to unmatch×-fst): if q ⊑ ϕ then dom of q ⊑ dom of ϕ.
unmatch⇒-dom : ∀ {τ} → (q : ⌊ τ ⌋) → (ϕ : ⌊ τ ⌋)
             → q ⊑ₛ ϕ
             → ∀ {τ₁' τ₂'} → ϕ .↓ ⊔ □ ⇒ □ ≡ τ₁' ⇒ τ₂'
             → ∀ {τ₁'' τ₂''} → q .↓ ⊔ □ ⇒ □ ≡ τ₁'' ⇒ τ₂''
             → τ₁'' ⊑t τ₁'
unmatch⇒-dom q ϕ v m' m''
  with ⊔-⇒-⊑ v m'
... | _ , _ , eq , p , _ rewrite eq with refl ← m'' = p

-- +-fst monotonicity.
unmatch+-fst : ∀ {τ} → (q : ⌊ τ ⌋) → (ϕ : ⌊ τ ⌋)
             → q ⊑ₛ ϕ
             → ∀ {τ₁' τ₂'} → ϕ .↓ ⊔ □ + □ ≡ τ₁' + τ₂'
             → ∀ {τ₁'' τ₂''} → q .↓ ⊔ □ + □ ≡ τ₁'' + τ₂''
             → τ₁'' ⊑t τ₁'
unmatch+-fst q ϕ v m' m''
  with ⊔-+-⊑ v m'
... | _ , _ , eq , p , _ rewrite eq with refl ← m'' = p

-- +-snd monotonicity.
unmatch+-snd : ∀ {τ} → (q : ⌊ τ ⌋) → (ϕ : ⌊ τ ⌋)
             → q ⊑ₛ ϕ
             → ∀ {τ₁' τ₂'} → ϕ .↓ ⊔ □ + □ ≡ τ₁' + τ₂'
             → ∀ {τ₁'' τ₂''} → q .↓ ⊔ □ + □ ≡ τ₁'' + τ₂''
             → τ₂'' ⊑t τ₂'
unmatch+-snd q ϕ v m' m''
  with ⊔-+-⊑ v m'
... | _ , _ , eq , _ , p rewrite eq with refl ← m'' = p

-- Extract component equalities from unmatch⇒/×/∀ match
unmatch⇒-≡-fst : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂)
               (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
               → ∀ {a b} → (unmatch⇒ {τ} m s₁ s₂) .↓ ⊔ □ ⇒ □ ≡ a ⇒ b → s₁ .↓ ≡ a
unmatch⇒-≡-fst {τ} m s₁ s₂ eq with diag τ (□ ⇒ □)
unmatch⇒-≡-fst {τ_a ⇒ τ_b} refl s₁ s₂ eq | kind⇒
  rewrite ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b} | ⊔t-zeroᵣ {s₁ .↓} | ⊔t-zeroᵣ {s₂ .↓} = ⇒-inj-fst eq
unmatch⇒-≡-fst {τ} m s₁ s₂ eq | diff with τ ≟t □
unmatch⇒-≡-fst refl (□ isSlice ⊑□) (□ isSlice ⊑□) refl | diff | yes refl = refl
unmatch⇒-≡-fst () _ _ _ | diff | no _

unmatch⇒-≡-snd : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂)
               (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
               → ∀ {a b} → (unmatch⇒ {τ} m s₁ s₂) .↓ ⊔ □ ⇒ □ ≡ a ⇒ b → s₂ .↓ ≡ b
unmatch⇒-≡-snd {τ} m s₁ s₂ eq with diag τ (□ ⇒ □)
unmatch⇒-≡-snd {τ_a ⇒ τ_b} refl s₁ s₂ eq | kind⇒
  rewrite ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b} | ⊔t-zeroᵣ {s₁ .↓} | ⊔t-zeroᵣ {s₂ .↓} = ⇒-inj-snd eq
unmatch⇒-≡-snd {τ} m s₁ s₂ eq | diff with τ ≟t □
unmatch⇒-≡-snd refl (□ isSlice ⊑□) (□ isSlice ⊑□) refl | diff | yes refl = refl
unmatch⇒-≡-snd () _ _ _ | diff | no _

unmatch×-≡-fst : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ × □ ≡ τ₁ × τ₂)
               (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
               → ∀ {a b} → (unmatch× {τ} m s₁ s₂) .↓ ⊔ □ × □ ≡ a × b → s₁ .↓ ≡ a
unmatch×-≡-fst {τ} m s₁ s₂ eq with diag τ (□ × □)
unmatch×-≡-fst {τ_a × τ_b} refl s₁ s₂ eq | kind×
  rewrite ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b} | ⊔t-zeroᵣ {s₁ .↓} | ⊔t-zeroᵣ {s₂ .↓} = ×-inj-fst eq
unmatch×-≡-fst {τ} m s₁ s₂ eq | diff with τ ≟t □
unmatch×-≡-fst refl (□ isSlice ⊑□) (□ isSlice ⊑□) refl | diff | yes refl = refl
unmatch×-≡-fst () _ _ _ | diff | no _

unmatch×-≡-snd : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ × □ ≡ τ₁ × τ₂)
               (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
               → ∀ {a b} → (unmatch× {τ} m s₁ s₂) .↓ ⊔ □ × □ ≡ a × b → s₂ .↓ ≡ b
unmatch×-≡-snd {τ} m s₁ s₂ eq with diag τ (□ × □)
unmatch×-≡-snd {τ_a × τ_b} refl s₁ s₂ eq | kind×
  rewrite ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b} | ⊔t-zeroᵣ {s₁ .↓} | ⊔t-zeroᵣ {s₂ .↓} = ×-inj-snd eq
unmatch×-≡-snd {τ} m s₁ s₂ eq | diff with τ ≟t □
unmatch×-≡-snd refl (□ isSlice ⊑□) (□ isSlice ⊑□) refl | diff | yes refl = refl
unmatch×-≡-snd () _ _ _ | diff | no _

unmatch∀-≡ : ∀ {τ τ'} (m : τ ⊔ ∀· □ ≡ ∀· τ')
             (s : ⌊ τ' ⌋)
             → ∀ {a} → (unmatch∀ {τ} m s) .↓ ⊔ ∀· □ ≡ ∀· a → s .↓ ≡ a
unmatch∀-≡ {τ} m s eq with diag τ (∀· □)
unmatch∀-≡ {∀· τ_a} refl s eq | kind∀
  rewrite ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {s .↓} = ∀-inj-body eq
unmatch∀-≡ {τ} m s eq | diff with τ ≟t □
unmatch∀-≡ refl (□ isSlice ⊑□) refl | diff | yes refl = refl
unmatch∀-≡ () _ _ | diff | no _

unmatch+-≡-fst : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
               (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
               → ∀ {a b} → (unmatch+ {τ} m s₁ s₂) .↓ ⊔ □ + □ ≡ a + b → s₁ .↓ ≡ a
unmatch+-≡-fst {τ} m s₁ s₂ eq with diag τ (□ + □)
unmatch+-≡-fst {τ_a + τ_b} refl s₁ s₂ eq | kind+
  rewrite ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b} | ⊔t-zeroᵣ {s₁ .↓} | ⊔t-zeroᵣ {s₂ .↓} = +-inj-fst eq
  where +-inj-fst : ∀ {a b c d : Typ} → a + b ≡ c + d → a ≡ c
        +-inj-fst refl = refl
unmatch+-≡-fst {τ} m s₁ s₂ eq | diff with τ ≟t □
unmatch+-≡-fst refl (□ isSlice ⊑□) (□ isSlice ⊑□) refl | diff | yes refl = refl
unmatch+-≡-fst () _ _ _ | diff | no _

unmatch+-≡-snd : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
               (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
               → ∀ {a b} → (unmatch+ {τ} m s₁ s₂) .↓ ⊔ □ + □ ≡ a + b → s₂ .↓ ≡ b
unmatch+-≡-snd {τ} m s₁ s₂ eq with diag τ (□ + □)
unmatch+-≡-snd {τ_a + τ_b} refl s₁ s₂ eq | kind+
  rewrite ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b} | ⊔t-zeroᵣ {s₁ .↓} | ⊔t-zeroᵣ {s₂ .↓} = +-inj-snd eq
  where +-inj-snd : ∀ {a b c d : Typ} → a + b ≡ c + d → b ≡ d
        +-inj-snd refl = refl
unmatch+-≡-snd {τ} m s₁ s₂ eq | diff with τ ≟t □
unmatch+-≡-snd refl (□ isSlice ⊑□) (□ isSlice ⊑□) refl | diff | yes refl = refl
unmatch+-≡-snd () _ _ _ | diff | no _

unmatch+-min-≡-fst : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
                     (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
                   → ∀ {a b} → (unmatch+-min {τ} m s₁ s₂) .↓ ⊔ □ + □ ≡ a + b → s₁ .↓ ≡ a
unmatch+-min-≡-fst m (□ isSlice ⊑□) (□ isSlice ⊑□) refl = refl
unmatch+-min-≡-fst {τ} m s₁@(_ isSlice ⊑*)     s₂ eq = unmatch+-≡-fst {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-fst {τ} m s₁@(_ isSlice ⊑Var)   s₂ eq = unmatch+-≡-fst {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-fst {τ} m s₁@(_ isSlice ⊑⇒ _ _) s₂ eq = unmatch+-≡-fst {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-fst {τ} m s₁@(_ isSlice ⊑× _ _) s₂ eq = unmatch+-≡-fst {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-fst {τ} m s₁@(_ isSlice ⊑+ _ _) s₂ eq = unmatch+-≡-fst {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-fst {τ} m s₁@(_ isSlice ⊑∀ _)   s₂ eq = unmatch+-≡-fst {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-fst {τ} m s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑*)     eq = unmatch+-≡-fst {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-fst {τ} m s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑Var)   eq = unmatch+-≡-fst {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-fst {τ} m s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑⇒ _ _) eq = unmatch+-≡-fst {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-fst {τ} m s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑× _ _) eq = unmatch+-≡-fst {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-fst {τ} m s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑+ _ _) eq = unmatch+-≡-fst {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-fst {τ} m s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑∀ _)   eq = unmatch+-≡-fst {τ = τ} m s₁ s₂ eq

unmatch+-min-≡-snd : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
                     (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
                   → ∀ {a b} → (unmatch+-min {τ} m s₁ s₂) .↓ ⊔ □ + □ ≡ a + b → s₂ .↓ ≡ b
unmatch+-min-≡-snd m (□ isSlice ⊑□) (□ isSlice ⊑□) refl = refl
unmatch+-min-≡-snd {τ} m s₁@(_ isSlice ⊑*)     s₂ eq = unmatch+-≡-snd {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-snd {τ} m s₁@(_ isSlice ⊑Var)   s₂ eq = unmatch+-≡-snd {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-snd {τ} m s₁@(_ isSlice ⊑⇒ _ _) s₂ eq = unmatch+-≡-snd {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-snd {τ} m s₁@(_ isSlice ⊑× _ _) s₂ eq = unmatch+-≡-snd {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-snd {τ} m s₁@(_ isSlice ⊑+ _ _) s₂ eq = unmatch+-≡-snd {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-snd {τ} m s₁@(_ isSlice ⊑∀ _)   s₂ eq = unmatch+-≡-snd {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-snd {τ} m s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑*)     eq = unmatch+-≡-snd {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-snd {τ} m s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑Var)   eq = unmatch+-≡-snd {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-snd {τ} m s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑⇒ _ _) eq = unmatch+-≡-snd {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-snd {τ} m s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑× _ _) eq = unmatch+-≡-snd {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-snd {τ} m s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑+ _ _) eq = unmatch+-≡-snd {τ = τ} m s₁ s₂ eq
unmatch+-min-≡-snd {τ} m s₁@(_ isSlice ⊑□) s₂@(_ isSlice ⊑∀ _)   eq = unmatch+-≡-snd {τ = τ} m s₁ s₂ eq

-- unmatch monotonicity lemmas
unmatch×-mono-fst : ∀ {τ τ₁ τ₂ τ'}
  → (m : τ ⊔ □ × □ ≡ τ₁ × τ₂)
  → (υ : ⌊ τ₁ ⌋)
  → υ .↓ ≢ □
  → τ' ⊑ τ
  → ∀ {τ₁' τ₂'} → τ' ⊔ □ × □ ≡ τ₁' × τ₂'
  → υ .↓ ⊑ τ₁'
  → (unmatch× {τ} m υ (⊥ₛ {a = τ₂})) .↓ ⊑t τ'
unmatch×-mono-fst _ _ υ≢□ ⊑□ refl ⊑□ = ⊥-elim (υ≢□ refl)
unmatch×-mono-fst {τ₁' × τ₂'} refl υ _ (⊑× {τ₁ = a} {τ₂ = b} _ _) m' υ⊑
  rewrite ⊔t-zeroᵣ {τ₁'} | ⊔t-zeroᵣ {τ₂'} | ⊔t-zeroᵣ {a} | ⊔t-zeroᵣ {b}
  with refl ← m' = ⊑× υ⊑ ⊑□

unmatch×-mono-snd : ∀ {τ τ₁ τ₂ τ'}
  → (m : τ ⊔ □ × □ ≡ τ₁ × τ₂)
  → (υ : ⌊ τ₂ ⌋)
  → υ .↓ ≢ □
  → τ' ⊑ τ
  → ∀ {τ₁' τ₂'} → τ' ⊔ □ × □ ≡ τ₁' × τ₂'
  → υ .↓ ⊑ τ₂'
  → (unmatch× {τ} m (⊥ₛ {a = τ₁}) υ) .↓ ⊑t τ'
unmatch×-mono-snd _ _ υ≢□ ⊑□ refl ⊑□ = ⊥-elim (υ≢□ refl)
unmatch×-mono-snd {τ₁' × τ₂'} refl υ _ (⊑× {τ₁ = a} {τ₂ = b} _ _) m' υ⊑
  rewrite ⊔t-zeroᵣ {τ₁'} | ⊔t-zeroᵣ {τ₂'} | ⊔t-zeroᵣ {a} | ⊔t-zeroᵣ {b}
  with refl ← m' = ⊑× ⊑□ υ⊑

unmatch⇒-mono-cod : ∀ {τ τ₁ τ₂ τ'}
  → (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂)
  → (υ : ⌊ τ₂ ⌋)
  → υ .↓ ≢ □
  → τ' ⊑ τ
  → ∀ {τ₁' τ₂'} → τ' ⊔ □ ⇒ □ ≡ τ₁' ⇒ τ₂'
  → υ .↓ ⊑ τ₂'
  → (unmatch⇒ {τ} m (⊥ₛ {a = τ₁}) υ) .↓ ⊑t τ'
unmatch⇒-mono-cod _ _ υ≢□ ⊑□ refl ⊑□ = ⊥-elim (υ≢□ refl)
unmatch⇒-mono-cod {τ₁' ⇒ τ₂'} refl υ _ (⊑⇒ {τ₁ = a} {τ₂ = b} _ _) m' υ⊑
  rewrite ⊔t-zeroᵣ {τ₁'} | ⊔t-zeroᵣ {τ₂'} | ⊔t-zeroᵣ {a} | ⊔t-zeroᵣ {b}
  with refl ← m' = ⊑⇒ ⊑□ υ⊑

unmatch∀-mono : ∀ {τ τ' τ''}
  → (m : τ ⊔ ∀· □ ≡ ∀· τ')
  → (υ' : ⌊ τ' ⌋)
  → υ' .↓ ≢ □
  → τ'' ⊑ τ
  → ∀ {τ₁'} → τ'' ⊔ ∀· □ ≡ ∀· τ₁'
  → υ' .↓ ⊑ τ₁'
  → (unmatch∀ {τ} m υ') .↓ ⊑t τ''
unmatch∀-mono _ _ υ≢□ ⊑□ refl ⊑□ = ⊥-elim (υ≢□ refl)
unmatch∀-mono {∀· τ₁'} refl υ' _ (⊑∀ {τ = a} _) m' υ⊑
  rewrite ⊔t-zeroᵣ {τ₁'} | ⊔t-zeroᵣ {a}
  with refl ← m' = ⊑∀ υ⊑

-- Cov-inversion lemmas: given (unmatch{+,×,⇒} m υ₁ υ₂).↓ ⊑t τ' and a lifted
-- match equation τ' ⊔ □K ≡ τ_a K τ_b, conclude υᵢ.↓ ⊑t τ_a (or τ_b).
-- These are needed in lift-{pos,syn}-cov for inductive cases where
-- ana-υ_outer-of-m is given by an unmatch+/×/⇒, and we need the inner
-- precondition on the inner-υ.

unmatch+-cov-fst : ∀ (τ : Typ) {τ₁ τ₂ τ' τ_a τ_b}
  → (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
  → (υ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
  → (unmatch+ {τ} m υ s₂) .↓ ⊑t τ'
  → τ' ⊔ □ + □ ≡ τ_a + τ_b
  → υ .↓ ⊑t τ_a
unmatch+-cov-fst (τ_a' + τ_b') refl υ s₂ (⊑+ {τ₁' = α} {τ₂' = β} p _) m'
  rewrite ⊔t-zeroᵣ {τ_a'} | ⊔t-zeroᵣ {τ_b'} | ⊔t-zeroᵣ {α} | ⊔t-zeroᵣ {β}
  with refl ← m' = p
unmatch+-cov-fst □ refl υ _ _ _
  with υ .proof
... | ⊑□ = ⊑□

unmatch+-cov-snd : ∀ (τ : Typ) {τ₁ τ₂ τ' τ_a τ_b}
  → (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
  → (s₁ : ⌊ τ₁ ⌋) (υ : ⌊ τ₂ ⌋)
  → (unmatch+ {τ} m s₁ υ) .↓ ⊑t τ'
  → τ' ⊔ □ + □ ≡ τ_a + τ_b
  → υ .↓ ⊑t τ_b
unmatch+-cov-snd (τ_a' + τ_b') refl s₁ υ (⊑+ {τ₁' = α} {τ₂' = β} _ q) m'
  rewrite ⊔t-zeroᵣ {τ_a'} | ⊔t-zeroᵣ {τ_b'} | ⊔t-zeroᵣ {α} | ⊔t-zeroᵣ {β}
  with refl ← m' = q
unmatch+-cov-snd □ refl _ υ _ _
  with υ .proof
... | ⊑□ = ⊑□

unmatch×-cov-fst : ∀ (τ : Typ) {τ₁ τ₂ τ' τ_a τ_b}
  → (m : τ ⊔ □ × □ ≡ τ₁ × τ₂)
  → (υ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
  → (unmatch× {τ} m υ s₂) .↓ ⊑t τ'
  → τ' ⊔ □ × □ ≡ τ_a × τ_b
  → υ .↓ ⊑t τ_a
unmatch×-cov-fst (τ_a' × τ_b') refl υ s₂ (⊑× {τ₁' = α} {τ₂' = β} p _) m'
  rewrite ⊔t-zeroᵣ {τ_a'} | ⊔t-zeroᵣ {τ_b'} | ⊔t-zeroᵣ {α} | ⊔t-zeroᵣ {β}
  with refl ← m' = p
unmatch×-cov-fst □ refl υ _ _ _
  with υ .proof
... | ⊑□ = ⊑□

unmatch×-cov-snd : ∀ (τ : Typ) {τ₁ τ₂ τ' τ_a τ_b}
  → (m : τ ⊔ □ × □ ≡ τ₁ × τ₂)
  → (s₁ : ⌊ τ₁ ⌋) (υ : ⌊ τ₂ ⌋)
  → (unmatch× {τ} m s₁ υ) .↓ ⊑t τ'
  → τ' ⊔ □ × □ ≡ τ_a × τ_b
  → υ .↓ ⊑t τ_b
unmatch×-cov-snd (τ_a' × τ_b') refl s₁ υ (⊑× {τ₁' = α} {τ₂' = β} _ q) m'
  rewrite ⊔t-zeroᵣ {τ_a'} | ⊔t-zeroᵣ {τ_b'} | ⊔t-zeroᵣ {α} | ⊔t-zeroᵣ {β}
  with refl ← m' = q
unmatch×-cov-snd □ refl _ υ _ _
  with υ .proof
... | ⊑□ = ⊑□

unmatch⇒-cov-cod : ∀ (τ : Typ) {τ₁ τ₂ τ' τ_a τ_b}
  → (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂)
  → (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → (unmatch⇒ {τ} m υ₁ υ₂) .↓ ⊑t τ'
  → τ' ⊔ □ ⇒ □ ≡ τ_a ⇒ τ_b
  → υ₂ .↓ ⊑t τ_b
unmatch⇒-cov-cod (τ_a' ⇒ τ_b') refl υ₁ υ₂ (⊑⇒ {τ₁' = α} {τ₂' = β} _ q) m'
  rewrite ⊔t-zeroᵣ {τ_a'} | ⊔t-zeroᵣ {τ_b'} | ⊔t-zeroᵣ {α} | ⊔t-zeroᵣ {β}
  with refl ← m' = q
unmatch⇒-cov-cod □ refl υ₁ υ₂ _ _
  with υ₁ .proof | υ₂ .proof
... | ⊑□ | ⊑□ = ⊑□

unmatch⇒-cov-dom : ∀ (τ : Typ) {τ₁ τ₂ τ' τ_a τ_b}
  → (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂)
  → (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → (unmatch⇒ {τ} m υ₁ υ₂) .↓ ⊑t τ'
  → τ' ⊔ □ ⇒ □ ≡ τ_a ⇒ τ_b
  → υ₁ .↓ ⊑t τ_a
unmatch⇒-cov-dom (τ_a' ⇒ τ_b') refl υ₁ υ₂ (⊑⇒ {τ₁' = α} {τ₂' = β} p _) m'
  rewrite ⊔t-zeroᵣ {τ_a'} | ⊔t-zeroᵣ {τ_b'} | ⊔t-zeroᵣ {α} | ⊔t-zeroᵣ {β}
  with refl ← m' = p
unmatch⇒-cov-dom □ refl υ₁ υ₂ _ _
  with υ₁ .proof | υ₂ .proof
... | ⊑□ | ⊑□ = ⊑□

-- unmatch⋆-min analysis kit: split, covering, projection, least, and
-- □-collapse lemmas for the -min unmatch variants (Dissertation §8.6).

private
  ⊑□-inv : ∀ {x : Typ} → x ⊑t □ → x ≡ □
  ⊑□-inv ⊑□ = refl

  ⊑t-reflexive : ∀ {x y : Typ} → x ≡ y → x ⊑t y
  ⊑t-reflexive refl = ⊑t-refl

unmatch⇒-min-split : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂) (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
  → ((s₁ .↓ ≡ □) ∧ (s₂ .↓ ≡ □) ∧ (unmatch⇒-min {τ} m s₁ s₂ ≡ ⊥ₛ))
  ⊎ ((unmatch⇒-min {τ} m s₁ s₂ ≡ unmatch⇒ {τ} m s₁ s₂) ∧ ((s₁ .↓ ≢ □) ⊎ (s₂ .↓ ≢ □)))
unmatch⇒-min-split m (□ isSlice ⊑□) (□ isSlice ⊑□)            = inj₁ (refl , refl , refl)
unmatch⇒-min-split m (Typ.* isSlice ⊑*) s₂                    = inj₂ (refl , inj₁ λ ())
unmatch⇒-min-split m (Typ.⟨ _ ⟩ isSlice ⊑Var) s₂              = inj₂ (refl , inj₁ λ ())
unmatch⇒-min-split m ((_ ⇒ _) isSlice ⊑⇒ _ _) s₂              = inj₂ (refl , inj₁ λ ())
unmatch⇒-min-split m ((_ × _) isSlice ⊑× _ _) s₂              = inj₂ (refl , inj₁ λ ())
unmatch⇒-min-split m ((_ + _) isSlice ⊑+ _ _) s₂              = inj₂ (refl , inj₁ λ ())
unmatch⇒-min-split m ((∀· _) isSlice ⊑∀ _) s₂                 = inj₂ (refl , inj₁ λ ())
unmatch⇒-min-split m (□ isSlice ⊑□) (Typ.* isSlice ⊑*)        = inj₂ (refl , inj₂ λ ())
unmatch⇒-min-split m (□ isSlice ⊑□) (Typ.⟨ _ ⟩ isSlice ⊑Var)  = inj₂ (refl , inj₂ λ ())
unmatch⇒-min-split m (□ isSlice ⊑□) ((_ ⇒ _) isSlice ⊑⇒ _ _)  = inj₂ (refl , inj₂ λ ())
unmatch⇒-min-split m (□ isSlice ⊑□) ((_ × _) isSlice ⊑× _ _)  = inj₂ (refl , inj₂ λ ())
unmatch⇒-min-split m (□ isSlice ⊑□) ((_ + _) isSlice ⊑+ _ _)  = inj₂ (refl , inj₂ λ ())
unmatch⇒-min-split m (□ isSlice ⊑□) ((∀· _) isSlice ⊑∀ _)     = inj₂ (refl , inj₂ λ ())

unmatch×-min-split : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ × □ ≡ τ₁ × τ₂) (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
  → ((s₁ .↓ ≡ □) ∧ (s₂ .↓ ≡ □) ∧ (unmatch×-min {τ} m s₁ s₂ ≡ ⊥ₛ))
  ⊎ ((unmatch×-min {τ} m s₁ s₂ ≡ unmatch× {τ} m s₁ s₂) ∧ ((s₁ .↓ ≢ □) ⊎ (s₂ .↓ ≢ □)))
unmatch×-min-split m (□ isSlice ⊑□) (□ isSlice ⊑□)            = inj₁ (refl , refl , refl)
unmatch×-min-split m (Typ.* isSlice ⊑*) s₂                    = inj₂ (refl , inj₁ λ ())
unmatch×-min-split m (Typ.⟨ _ ⟩ isSlice ⊑Var) s₂              = inj₂ (refl , inj₁ λ ())
unmatch×-min-split m ((_ ⇒ _) isSlice ⊑⇒ _ _) s₂              = inj₂ (refl , inj₁ λ ())
unmatch×-min-split m ((_ × _) isSlice ⊑× _ _) s₂              = inj₂ (refl , inj₁ λ ())
unmatch×-min-split m ((_ + _) isSlice ⊑+ _ _) s₂              = inj₂ (refl , inj₁ λ ())
unmatch×-min-split m ((∀· _) isSlice ⊑∀ _) s₂                 = inj₂ (refl , inj₁ λ ())
unmatch×-min-split m (□ isSlice ⊑□) (Typ.* isSlice ⊑*)        = inj₂ (refl , inj₂ λ ())
unmatch×-min-split m (□ isSlice ⊑□) (Typ.⟨ _ ⟩ isSlice ⊑Var)  = inj₂ (refl , inj₂ λ ())
unmatch×-min-split m (□ isSlice ⊑□) ((_ ⇒ _) isSlice ⊑⇒ _ _)  = inj₂ (refl , inj₂ λ ())
unmatch×-min-split m (□ isSlice ⊑□) ((_ × _) isSlice ⊑× _ _)  = inj₂ (refl , inj₂ λ ())
unmatch×-min-split m (□ isSlice ⊑□) ((_ + _) isSlice ⊑+ _ _)  = inj₂ (refl , inj₂ λ ())
unmatch×-min-split m (□ isSlice ⊑□) ((∀· _) isSlice ⊑∀ _)     = inj₂ (refl , inj₂ λ ())

unmatch+-min-split : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
  → ((s₁ .↓ ≡ □) ∧ (s₂ .↓ ≡ □) ∧ (unmatch+-min {τ} m s₁ s₂ ≡ ⊥ₛ))
  ⊎ ((unmatch+-min {τ} m s₁ s₂ ≡ unmatch+ {τ} m s₁ s₂) ∧ ((s₁ .↓ ≢ □) ⊎ (s₂ .↓ ≢ □)))
unmatch+-min-split m (□ isSlice ⊑□) (□ isSlice ⊑□)            = inj₁ (refl , refl , refl)
unmatch+-min-split m (Typ.* isSlice ⊑*) s₂                    = inj₂ (refl , inj₁ λ ())
unmatch+-min-split m (Typ.⟨ _ ⟩ isSlice ⊑Var) s₂              = inj₂ (refl , inj₁ λ ())
unmatch+-min-split m ((_ ⇒ _) isSlice ⊑⇒ _ _) s₂              = inj₂ (refl , inj₁ λ ())
unmatch+-min-split m ((_ × _) isSlice ⊑× _ _) s₂              = inj₂ (refl , inj₁ λ ())
unmatch+-min-split m ((_ + _) isSlice ⊑+ _ _) s₂              = inj₂ (refl , inj₁ λ ())
unmatch+-min-split m ((∀· _) isSlice ⊑∀ _) s₂                 = inj₂ (refl , inj₁ λ ())
unmatch+-min-split m (□ isSlice ⊑□) (Typ.* isSlice ⊑*)        = inj₂ (refl , inj₂ λ ())
unmatch+-min-split m (□ isSlice ⊑□) (Typ.⟨ _ ⟩ isSlice ⊑Var)  = inj₂ (refl , inj₂ λ ())
unmatch+-min-split m (□ isSlice ⊑□) ((_ ⇒ _) isSlice ⊑⇒ _ _)  = inj₂ (refl , inj₂ λ ())
unmatch+-min-split m (□ isSlice ⊑□) ((_ × _) isSlice ⊑× _ _)  = inj₂ (refl , inj₂ λ ())
unmatch+-min-split m (□ isSlice ⊑□) ((_ + _) isSlice ⊑+ _ _)  = inj₂ (refl , inj₂ λ ())
unmatch+-min-split m (□ isSlice ⊑□) ((∀· _) isSlice ⊑∀ _)     = inj₂ (refl , inj₂ λ ())

unmatch⇒-min-cov : ∀ (τ : Typ) {τ₁ τ₂ τ' τ_a τ_b}
  → (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → (unmatch⇒-min {τ} m υ₁ υ₂) .↓ ⊑t τ'
  → τ' ⊔ □ ⇒ □ ≡ τ_a ⇒ τ_b
  → (υ₁ .↓ ⊑t τ_a) ∧ (υ₂ .↓ ⊑t τ_b)
unmatch⇒-min-cov τ {τ' = τ'} m υ₁ υ₂ prec m' with unmatch⇒-min-split m υ₁ υ₂
... | inj₁ (e₁ , e₂ , _) rewrite e₁ | e₂ = ⊑□ , ⊑□
... | inj₂ (e , _) =
      unmatch⇒-cov-dom τ m υ₁ υ₂ prec' m' , unmatch⇒-cov-cod τ m υ₁ υ₂ prec' m'
  where prec' : (unmatch⇒ {τ} m υ₁ υ₂) .↓ ⊑t τ'
        prec' = subst (λ x → x .↓ ⊑t τ') e prec

unmatch×-min-cov : ∀ (τ : Typ) {τ₁ τ₂ τ' τ_a τ_b}
  → (m : τ ⊔ □ × □ ≡ τ₁ × τ₂) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → (unmatch×-min {τ} m υ₁ υ₂) .↓ ⊑t τ'
  → τ' ⊔ □ × □ ≡ τ_a × τ_b
  → (υ₁ .↓ ⊑t τ_a) ∧ (υ₂ .↓ ⊑t τ_b)
unmatch×-min-cov τ {τ' = τ'} m υ₁ υ₂ prec m' with unmatch×-min-split m υ₁ υ₂
... | inj₁ (e₁ , e₂ , _) rewrite e₁ | e₂ = ⊑□ , ⊑□
... | inj₂ (e , _) =
      unmatch×-cov-fst τ m υ₁ υ₂ prec' m' , unmatch×-cov-snd τ m υ₁ υ₂ prec' m'
  where prec' : (unmatch× {τ} m υ₁ υ₂) .↓ ⊑t τ'
        prec' = subst (λ x → x .↓ ⊑t τ') e prec

unmatch+-min-cov : ∀ (τ : Typ) {τ₁ τ₂ τ' τ_a τ_b}
  → (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → (unmatch+-min {τ} m υ₁ υ₂) .↓ ⊑t τ'
  → τ' ⊔ □ + □ ≡ τ_a + τ_b
  → (υ₁ .↓ ⊑t τ_a) ∧ (υ₂ .↓ ⊑t τ_b)
unmatch+-min-cov τ {τ' = τ'} m υ₁ υ₂ prec m' with unmatch+-min-split m υ₁ υ₂
... | inj₁ (e₁ , e₂ , _) rewrite e₁ | e₂ = ⊑□ , ⊑□
... | inj₂ (e , _) =
      unmatch+-cov-fst τ m υ₁ υ₂ prec' m' , unmatch+-cov-snd τ m υ₁ υ₂ prec' m'
  where prec' : (unmatch+ {τ} m υ₁ υ₂) .↓ ⊑t τ'
        prec' = subst (λ x → x .↓ ⊑t τ') e prec

unmatch⇒-min-mono : ∀ (τ : Typ) {τ₁ τ₂ τ₀ τ_a τ_b}
  → (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → τ₀ ⊑t (unmatch⇒-min {τ} m υ₁ υ₂) .↓
  → τ₀ ⊔ □ ⇒ □ ≡ τ_a ⇒ τ_b
  → (τ_a ⊑t υ₁ .↓) ∧ (τ_b ⊑t υ₂ .↓)
unmatch⇒-min-mono □ refl (□ isSlice ⊑□) (□ isSlice ⊑□) h m'
  with refl ← ⊑□-inv h with refl ← m' = ⊑□ , ⊑□
unmatch⇒-min-mono (τa ⇒ τb) {τ₀ = τ₀} refl υ₁ υ₂ h m'
  with unmatch⇒-min-split {τ = τa ⇒ τb} refl υ₁ υ₂
... | inj₁ (_ , _ , e⊥)
  with refl ← ⊑□-inv (subst (τ₀ ⊑t_) (cong (λ x → x .↓) e⊥) h)
  with refl ← m' = ⊑□ , ⊑□
... | inj₂ (e , _) = fin h'' m'
  where
    h'' : τ₀ ⊑t (υ₁ .↓ ⇒ υ₂ .↓)
    h'' = subst (τ₀ ⊑t_)
            (trans (cong (λ x → x .↓) e)
                   (Eq.cong₂ _⇒_ (subst-↓-pre (⊔t-zeroᵣ {τa}) υ₁)
                              (subst-↓-pre (⊔t-zeroᵣ {τb}) υ₂)))
            h
    fin : ∀ {τ₀' τ_a τ_b} → τ₀' ⊑t (υ₁ .↓ ⇒ υ₂ .↓) → τ₀' ⊔ □ ⇒ □ ≡ τ_a ⇒ τ_b
        → (τ_a ⊑t υ₁ .↓) ∧ (τ_b ⊑t υ₂ .↓)
    fin ⊑□ refl = ⊑□ , ⊑□
    fin (⊑⇒ {τ₁ = c} {τ₂ = d} pa pb) refl =
      subst (_⊑t υ₁ .↓) (sym (⊔t-zeroᵣ {c})) pa ,
      subst (_⊑t υ₂ .↓) (sym (⊔t-zeroᵣ {d})) pb

unmatch×-min-mono : ∀ (τ : Typ) {τ₁ τ₂ τ₀ τ_a τ_b}
  → (m : τ ⊔ □ × □ ≡ τ₁ × τ₂) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → τ₀ ⊑t (unmatch×-min {τ} m υ₁ υ₂) .↓
  → τ₀ ⊔ □ × □ ≡ τ_a × τ_b
  → (τ_a ⊑t υ₁ .↓) ∧ (τ_b ⊑t υ₂ .↓)
unmatch×-min-mono □ refl (□ isSlice ⊑□) (□ isSlice ⊑□) h m'
  with refl ← ⊑□-inv h with refl ← m' = ⊑□ , ⊑□
unmatch×-min-mono (τa × τb) {τ₀ = τ₀} refl υ₁ υ₂ h m'
  with unmatch×-min-split {τ = τa × τb} refl υ₁ υ₂
... | inj₁ (_ , _ , e⊥)
  with refl ← ⊑□-inv (subst (τ₀ ⊑t_) (cong (λ x → x .↓) e⊥) h)
  with refl ← m' = ⊑□ , ⊑□
... | inj₂ (e , _) = fin h'' m'
  where
    h'' : τ₀ ⊑t (υ₁ .↓ × υ₂ .↓)
    h'' = subst (τ₀ ⊑t_)
            (trans (cong (λ x → x .↓) e)
                   (Eq.cong₂ _×_ (subst-↓-pre (⊔t-zeroᵣ {τa}) υ₁)
                              (subst-↓-pre (⊔t-zeroᵣ {τb}) υ₂)))
            h
    fin : ∀ {τ₀' τ_a τ_b} → τ₀' ⊑t (υ₁ .↓ × υ₂ .↓) → τ₀' ⊔ □ × □ ≡ τ_a × τ_b
        → (τ_a ⊑t υ₁ .↓) ∧ (τ_b ⊑t υ₂ .↓)
    fin ⊑□ refl = ⊑□ , ⊑□
    fin (⊑× {τ₁ = c} {τ₂ = d} pa pb) refl =
      subst (_⊑t υ₁ .↓) (sym (⊔t-zeroᵣ {c})) pa ,
      subst (_⊑t υ₂ .↓) (sym (⊔t-zeroᵣ {d})) pb

unmatch+-min-mono : ∀ (τ : Typ) {τ₁ τ₂ τ₀ τ_a τ_b}
  → (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → τ₀ ⊑t (unmatch+-min {τ} m υ₁ υ₂) .↓
  → τ₀ ⊔ □ + □ ≡ τ_a + τ_b
  → (τ_a ⊑t υ₁ .↓) ∧ (τ_b ⊑t υ₂ .↓)
unmatch+-min-mono □ refl (□ isSlice ⊑□) (□ isSlice ⊑□) h m'
  with refl ← ⊑□-inv h with refl ← m' = ⊑□ , ⊑□
unmatch+-min-mono (τa + τb) {τ₀ = τ₀} refl υ₁ υ₂ h m'
  with unmatch+-min-split {τ = τa + τb} refl υ₁ υ₂
... | inj₁ (_ , _ , e⊥)
  with refl ← ⊑□-inv (subst (τ₀ ⊑t_) (cong (λ x → x .↓) e⊥) h)
  with refl ← m' = ⊑□ , ⊑□
... | inj₂ (e , _) = fin h'' m'
  where
    h'' : τ₀ ⊑t (υ₁ .↓ + υ₂ .↓)
    h'' = subst (τ₀ ⊑t_)
            (trans (cong (λ x → x .↓) e)
                   (Eq.cong₂ _+_ (subst-↓-pre (⊔t-zeroᵣ {τa}) υ₁)
                              (subst-↓-pre (⊔t-zeroᵣ {τb}) υ₂)))
            h
    fin : ∀ {τ₀' τ_a τ_b} → τ₀' ⊑t (υ₁ .↓ + υ₂ .↓) → τ₀' ⊔ □ + □ ≡ τ_a + τ_b
        → (τ_a ⊑t υ₁ .↓) ∧ (τ_b ⊑t υ₂ .↓)
    fin ⊑□ refl = ⊑□ , ⊑□
    fin (⊑+ {τ₁ = c} {τ₂ = d} pa pb) refl =
      subst (_⊑t υ₁ .↓) (sym (⊔t-zeroᵣ {c})) pa ,
      subst (_⊑t υ₂ .↓) (sym (⊔t-zeroᵣ {d})) pb

unmatch⇒-min-□ : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → υ₁ .↓ ≡ □ → υ₂ .↓ ≡ □ → (unmatch⇒-min {τ} m υ₁ υ₂) .↓ ≡ □
unmatch⇒-min-□ m (□ isSlice ⊑□) (□ isSlice ⊑□) _ _ = refl

unmatch×-min-□ : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ × □ ≡ τ₁ × τ₂) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → υ₁ .↓ ≡ □ → υ₂ .↓ ≡ □ → (unmatch×-min {τ} m υ₁ υ₂) .↓ ≡ □
unmatch×-min-□ m (□ isSlice ⊑□) (□ isSlice ⊑□) _ _ = refl

unmatch+-min-□ : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → υ₁ .↓ ≡ □ → υ₂ .↓ ≡ □ → (unmatch+-min {τ} m υ₁ υ₂) .↓ ≡ □
unmatch+-min-□ m (□ isSlice ⊑□) (□ isSlice ⊑□) _ _ = refl

unmatch⇒-min-least : ∀ (τ : Typ) {τ₁ τ₂ τ' τ_a τ_b}
  → (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → τ' ⊑t τ → τ' ⊔ □ ⇒ □ ≡ τ_a ⇒ τ_b
  → υ₁ .↓ ⊑t τ_a → υ₂ .↓ ⊑t τ_b
  → (unmatch⇒-min {τ} m υ₁ υ₂) .↓ ⊑t τ'
unmatch⇒-min-least □ refl (□ isSlice ⊑□) (□ isSlice ⊑□) _ _ _ _ = ⊑□
unmatch⇒-min-least (τa ⇒ τb) {τ' = τ'} refl υ₁ υ₂ p' m' q₁ q₂
  with unmatch⇒-min-split {τ = τa ⇒ τb} refl υ₁ υ₂
... | inj₁ (_ , _ , e⊥) rewrite e⊥ = ⊑□
... | inj₂ (e , ne) =
      subst (_⊑t τ')
        (sym (trans (cong (λ x → x .↓) e)
                    (Eq.cong₂ _⇒_ (subst-↓-pre (⊔t-zeroᵣ {τa}) υ₁)
                                  (subst-↓-pre (⊔t-zeroᵣ {τb}) υ₂))))
        (fin p' m' q₁ q₂ ne)
  where
    fin : ∀ {τ' τ_a τ_b}
        → τ' ⊑t (τa ⇒ τb) → τ' ⊔ □ ⇒ □ ≡ τ_a ⇒ τ_b
        → υ₁ .↓ ⊑t τ_a → υ₂ .↓ ⊑t τ_b
        → (υ₁ .↓ ≢ □) ⊎ (υ₂ .↓ ≢ □)
        → (υ₁ .↓ ⇒ υ₂ .↓) ⊑t τ'
    fin ⊑□ refl r₁ r₂ (inj₁ ¬e) = ⊥-elim (¬e (⊑□-inv r₁))
    fin ⊑□ refl r₁ r₂ (inj₂ ¬e) = ⊥-elim (¬e (⊑□-inv r₂))
    fin (⊑⇒ {τ₁ = c} {τ₂ = d} pa pb) refl r₁ r₂ _ =
      ⊑⇒ (subst (υ₁ .↓ ⊑t_) (⊔t-zeroᵣ {c}) r₁) (subst (υ₂ .↓ ⊑t_) (⊔t-zeroᵣ {d}) r₂)

unmatch×-min-least : ∀ (τ : Typ) {τ₁ τ₂ τ' τ_a τ_b}
  → (m : τ ⊔ □ × □ ≡ τ₁ × τ₂) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → τ' ⊑t τ → τ' ⊔ □ × □ ≡ τ_a × τ_b
  → υ₁ .↓ ⊑t τ_a → υ₂ .↓ ⊑t τ_b
  → (unmatch×-min {τ} m υ₁ υ₂) .↓ ⊑t τ'
unmatch×-min-least □ refl (□ isSlice ⊑□) (□ isSlice ⊑□) _ _ _ _ = ⊑□
unmatch×-min-least (τa × τb) {τ' = τ'} refl υ₁ υ₂ p' m' q₁ q₂
  with unmatch×-min-split {τ = τa × τb} refl υ₁ υ₂
... | inj₁ (_ , _ , e⊥) rewrite e⊥ = ⊑□
... | inj₂ (e , ne) =
      subst (_⊑t τ')
        (sym (trans (cong (λ x → x .↓) e)
                    (Eq.cong₂ _×_ (subst-↓-pre (⊔t-zeroᵣ {τa}) υ₁)
                                  (subst-↓-pre (⊔t-zeroᵣ {τb}) υ₂))))
        (fin p' m' q₁ q₂ ne)
  where
    fin : ∀ {τ' τ_a τ_b}
        → τ' ⊑t (τa × τb) → τ' ⊔ □ × □ ≡ τ_a × τ_b
        → υ₁ .↓ ⊑t τ_a → υ₂ .↓ ⊑t τ_b
        → (υ₁ .↓ ≢ □) ⊎ (υ₂ .↓ ≢ □)
        → (υ₁ .↓ × υ₂ .↓) ⊑t τ'
    fin ⊑□ refl r₁ r₂ (inj₁ ¬e) = ⊥-elim (¬e (⊑□-inv r₁))
    fin ⊑□ refl r₁ r₂ (inj₂ ¬e) = ⊥-elim (¬e (⊑□-inv r₂))
    fin (⊑× {τ₁ = c} {τ₂ = d} pa pb) refl r₁ r₂ _ =
      ⊑× (subst (υ₁ .↓ ⊑t_) (⊔t-zeroᵣ {c}) r₁) (subst (υ₂ .↓ ⊑t_) (⊔t-zeroᵣ {d}) r₂)

unmatch+-min-least : ∀ (τ : Typ) {τ₁ τ₂ τ' τ_a τ_b}
  → (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) (υ₁ : ⌊ τ₁ ⌋) (υ₂ : ⌊ τ₂ ⌋)
  → τ' ⊑t τ → τ' ⊔ □ + □ ≡ τ_a + τ_b
  → υ₁ .↓ ⊑t τ_a → υ₂ .↓ ⊑t τ_b
  → (unmatch+-min {τ} m υ₁ υ₂) .↓ ⊑t τ'
unmatch+-min-least □ refl (□ isSlice ⊑□) (□ isSlice ⊑□) _ _ _ _ = ⊑□
unmatch+-min-least (τa + τb) {τ' = τ'} refl υ₁ υ₂ p' m' q₁ q₂
  with unmatch+-min-split {τ = τa + τb} refl υ₁ υ₂
... | inj₁ (_ , _ , e⊥) rewrite e⊥ = ⊑□
... | inj₂ (e , ne) =
      subst (_⊑t τ')
        (sym (trans (cong (λ x → x .↓) e)
                    (Eq.cong₂ _+_ (subst-↓-pre (⊔t-zeroᵣ {τa}) υ₁)
                                  (subst-↓-pre (⊔t-zeroᵣ {τb}) υ₂))))
        (fin p' m' q₁ q₂ ne)
  where
    fin : ∀ {τ' τ_a τ_b}
        → τ' ⊑t (τa + τb) → τ' ⊔ □ + □ ≡ τ_a + τ_b
        → υ₁ .↓ ⊑t τ_a → υ₂ .↓ ⊑t τ_b
        → (υ₁ .↓ ≢ □) ⊎ (υ₂ .↓ ≢ □)
        → (υ₁ .↓ + υ₂ .↓) ⊑t τ'
    fin ⊑□ refl r₁ r₂ (inj₁ ¬e) = ⊥-elim (¬e (⊑□-inv r₁))
    fin ⊑□ refl r₁ r₂ (inj₂ ¬e) = ⊥-elim (¬e (⊑□-inv r₂))
    fin (⊑+ {τ₁ = c} {τ₂ = d} pa pb) refl r₁ r₂ _ =
      ⊑+ (subst (υ₁ .↓ ⊑t_) (⊔t-zeroᵣ {c}) r₁) (subst (υ₂ .↓ ⊑t_) (⊔t-zeroᵣ {d}) r₂)

-- An annotation-joined arrow equation determines a □-joined one with the
-- same codomain (aλ: outer-type slicing, §8.6).
ann-⇒-plain : ∀ {τ τ_h τ_a τ₂} → τ ⊔ τ_h ⇒ □ ≡ τ_a ⇒ τ₂ → ∃[ τd ] (τ ⊔ □ ⇒ □ ≡ τd ⇒ τ₂)
ann-⇒-plain {□} refl = _ , refl
ann-⇒-plain {τl ⇒ τr} refl = _ , refl
