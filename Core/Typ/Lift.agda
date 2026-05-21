module Core.Typ.Lift where

open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no)

open import Core.Typ.Base using (Typ; □; _⇒_; _×_; ∀·; _+_; diag; _kind?_; kind□; kind⇒; kind×; kind+; kind∀; diff)
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

-- +ₛ-min: sum except use ? instead of ? + ?.
-- For use in minimising scrutinee of case statements
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

-- +ₛ-min validity: scrutinee precision through match equation
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

-- delegate most cases to fst+ₛ
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

-- fst+ₛ/snd+ₛ precision through ⊔-+-⊑ decomposition
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

-- Type substitution on slices
unsub : ∀ {τ' σ} → ⌊ [ zero ↦ σ ] τ' ⌋ → ⌊ τ' ⌋
unsub {τ'} s = ↑ (⊑Lat.x⊓y⊑y (s .↓) τ')

subₛ : ∀ {τ' σ} → ⌊ σ ⌋ → ⌊ τ' ⌋ → ⌊ [ zero ↦ σ ] τ' ⌋
subₛ σ' υ' = ↑ (sub-⊑ zero (σ' .proof) (υ' .proof))

-- Precision inversion helpers
⊑⇒-fst : ∀ {τ₁ τ₂ τ} → τ₁ ⇒ τ₂ ⊑t τ → ∃[ τ₁' ] ∃[ τ₂' ] (τ ≡ τ₁' ⇒ τ₂' ∧ τ₁ ⊑t τ₁' ∧ τ₂ ⊑t τ₂')
⊑⇒-fst (⊑⇒ p q) = _ , _ , refl , p , q

-- Unmatch helpers for join decomposition
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

-- unmatch+-min: like +ₛ-min but works with general match equation τ ⊔ □+□ ≡ τ₁+τ₂
-- Returns ⊥ₛ when both components are ⊥ₛ (minimality), otherwise unmatch+
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

-- unmatch+-min lemmas (analogues of +ₛ-min lemmas, adapted for match equation)
postulate
  fst-unmatch+-min : ∀ (τ : Typ) {τ₁ τ₂} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋) (t : ⌊ τ ⌋)
    → (unmatch+-min {τ} m s₁ s₂) .↓ ⊑t t .↓ → s₁ .↓ ⊑t (fst+ₛ' t m) .↓
  snd-unmatch+-min : ∀ (τ : Typ) {τ₁ τ₂} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋) (t : ⌊ τ ⌋)
    → (unmatch+-min {τ} m s₁ s₂) .↓ ⊑t t .↓ → s₂ .↓ ⊑t (snd+ₛ' t m) .↓
  unmatch+-min-⊑ : ∀ (τ : Typ) {τ₁ τ₂ τ' τ₃' τ₄'} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
    → τ' ⊑t τ → τ' ⊔ (□ + □) ≡ τ₃' + τ₄'
    → s₁ .↓ ⊑t τ₃' → s₂ .↓ ⊑t τ₄'
    → (unmatch+-min {τ} m s₁ s₂) .↓ ⊑t τ'
  fst+ₛ'-⊔ : ∀ {τ τ₁ τ₂} (s : ⌊ τ ⌋) (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
    {τ' τ₁' τ₂'} → s .↓ ⊑t τ' → τ' ⊔ □ + □ ≡ τ₁' + τ₂'
    → (fst+ₛ' s m) .↓ ⊑t τ₁'
  snd+ₛ'-⊔ : ∀ {τ τ₁ τ₂} (s : ⌊ τ ⌋) (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
    {τ' τ₁' τ₂'} → s .↓ ⊑t τ' → τ' ⊔ □ + □ ≡ τ₁' + τ₂'
    → (snd+ₛ' s m) .↓ ⊑t τ₂'

  +-proj-fst-mono : ∀ {τ τ₁ τ₂ τ₀ τ_a τ_b} (ψ₀ : ⌊ τ ⌋)
    (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) → τ₀ ⊑t ψ₀ .↓ → τ₀ ⊔ □ + □ ≡ τ_a + τ_b
    → τ_a ⊑t (fst+ₛ' ψ₀ m) .↓
  +-proj-snd-mono : ∀ {τ τ₁ τ₂ τ₀ τ_a τ_b} (ψ₀ : ⌊ τ ⌋)
    (m : τ ⊔ □ + □ ≡ τ₁ + τ₂) → τ₀ ⊑t ψ₀ .↓ → τ₀ ⊔ □ + □ ≡ τ_a + τ_b
    → τ_b ⊑t (snd+ₛ' ψ₀ m) .↓

  -- unmatch×-min lemmas (analogues of unmatch+-min)
  unmatch×-min-⊑ : ∀ (τ : Typ) {τ₁ τ₂ τ' τ₃' τ₄'} (m : τ ⊔ □ × □ ≡ τ₁ × τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
    → τ' ⊑t τ → τ' ⊔ (□ × □) ≡ τ₃' × τ₄'
    → s₁ .↓ ⊑t τ₃' → s₂ .↓ ⊑t τ₄'
    → (unmatch×-min {τ} m s₁ s₂) .↓ ⊑t τ'
  ×-proj-fst-mono : ∀ {τ τ₁ τ₂ τ₀ τ_a τ_b} (ψ₀ : ⌊ τ ⌋)
    (m : τ ⊔ □ × □ ≡ τ₁ × τ₂) → τ₀ ⊑t ψ₀ .↓ → τ₀ ⊔ □ × □ ≡ τ_a × τ_b
    → τ_a ⊑t (fst×ₛ' ψ₀ m) .↓
  ×-proj-snd-mono : ∀ {τ τ₁ τ₂ τ₀ τ_a τ_b} (ψ₀ : ⌊ τ ⌋)
    (m : τ ⊔ □ × □ ≡ τ₁ × τ₂) → τ₀ ⊑t ψ₀ .↓ → τ₀ ⊔ □ × □ ≡ τ_a × τ_b
    → τ_b ⊑t (snd×ₛ ψ₀ m) .↓

  -- unmatch⇒-min lemmas (analogues of unmatch+-min)
  unmatch⇒-min-⊑ : ∀ (τ : Typ) {τ₁ τ₂ τ' τ₃' τ₄'} (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂)
    (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
    → τ' ⊑t τ → τ' ⊔ (□ ⇒ □) ≡ τ₃' ⇒ τ₄'
    → s₁ .↓ ⊑t τ₃' → s₂ .↓ ⊑t τ₄'
    → (unmatch⇒-min {τ} m s₁ s₂) .↓ ⊑t τ'
  ⇒-proj-dom-mono : ∀ {τ τ₁ τ₂ τ₀ τ_a τ_b} (ψ₀ : ⌊ τ ⌋)
    (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂) → τ₀ ⊑t ψ₀ .↓ → τ₀ ⊔ □ ⇒ □ ≡ τ_a ⇒ τ_b
    → τ_a ⊑t (dom⇒ₛ ψ₀ m) .↓
  ⇒-proj-cod-mono : ∀ {τ τ₁ τ₂ τ₀ τ_a τ_b} (ψ₀ : ⌊ τ ⌋)
    (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂) → τ₀ ⊑t ψ₀ .↓ → τ₀ ⊔ □ ⇒ □ ≡ τ_a ⇒ τ_b
    → τ_b ⊑t (cod⇒ₛ ψ₀ m) .↓

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

-- Auxiliary: subst on ⌊_⌋ does not change the .↓ field
subst-↓ : ∀ {a b : Typ} (p : a ≡ b) (s : ⌊ a ⌋) → (subst ⌊_⌋ p s) .↓ ≡ s .↓
subst-↓ refl _ = refl

-- Extract component equalities from unmatch operators. These follow from
-- the structure of unmatch{⇒,×,+,∀}: either τ matches the kind (giving a
-- slice with the obvious shape, so its components agree with s₁/s₂), or
-- τ = □ (forcing ⊥ₛ, and both s components also have .↓ = □).
unmatch⇒-≡-fst : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂)
                 (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
               → ∀ {a b} → (unmatch⇒ {τ} m s₁ s₂) .↓ ⊔ □ ⇒ □ ≡ a ⇒ b → s₁ .↓ ≡ a
unmatch⇒-≡-fst {α ⇒ β} refl s₁ s₂ m'
  rewrite ⊔t-zeroᵣ {α} | ⊔t-zeroᵣ {β}
  with refl ← m' = sym (⊔t-zeroᵣ {s₁ .↓})
  where open import Relation.Binary.PropositionalEquality using (sym)
unmatch⇒-≡-fst {□} refl s₁ s₂ m'
  with s₁ .proof | s₂ .proof
... | ⊑□ | ⊑□ with refl ← m' = refl

unmatch⇒-≡-snd : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂)
                 (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
               → ∀ {a b} → (unmatch⇒ {τ} m s₁ s₂) .↓ ⊔ □ ⇒ □ ≡ a ⇒ b → s₂ .↓ ≡ b
unmatch⇒-≡-snd {α ⇒ β} refl s₁ s₂ m'
  rewrite ⊔t-zeroᵣ {α} | ⊔t-zeroᵣ {β}
  with refl ← m' = sym (⊔t-zeroᵣ {s₂ .↓})
  where open import Relation.Binary.PropositionalEquality using (sym)
unmatch⇒-≡-snd {□} refl s₁ s₂ m'
  with s₁ .proof | s₂ .proof
... | ⊑□ | ⊑□ with refl ← m' = refl

unmatch×-≡-fst : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ × □ ≡ τ₁ × τ₂)
                 (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
               → ∀ {a b} → (unmatch× {τ} m s₁ s₂) .↓ ⊔ □ × □ ≡ a × b → s₁ .↓ ≡ a
unmatch×-≡-fst {α × β} refl s₁ s₂ m'
  rewrite ⊔t-zeroᵣ {α} | ⊔t-zeroᵣ {β}
  with refl ← m' = sym (⊔t-zeroᵣ {s₁ .↓})
  where open import Relation.Binary.PropositionalEquality using (sym)
unmatch×-≡-fst {□} refl s₁ s₂ m'
  with s₁ .proof | s₂ .proof
... | ⊑□ | ⊑□ with refl ← m' = refl

unmatch×-≡-snd : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ × □ ≡ τ₁ × τ₂)
                 (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
               → ∀ {a b} → (unmatch× {τ} m s₁ s₂) .↓ ⊔ □ × □ ≡ a × b → s₂ .↓ ≡ b
unmatch×-≡-snd {α × β} refl s₁ s₂ m'
  rewrite ⊔t-zeroᵣ {α} | ⊔t-zeroᵣ {β}
  with refl ← m' = sym (⊔t-zeroᵣ {s₂ .↓})
  where open import Relation.Binary.PropositionalEquality using (sym)
unmatch×-≡-snd {□} refl s₁ s₂ m'
  with s₁ .proof | s₂ .proof
... | ⊑□ | ⊑□ with refl ← m' = refl

unmatch∀-≡ : ∀ {τ τ'} (m : τ ⊔ ∀· □ ≡ ∀· τ')
             (s : ⌊ τ' ⌋)
             → ∀ {a} → (unmatch∀ {τ} m s) .↓ ⊔ ∀· □ ≡ ∀· a → s .↓ ≡ a
unmatch∀-≡ {∀· τ₁} refl s m'
  rewrite ⊔t-zeroᵣ {τ₁}
  with refl ← m' = sym (⊔t-zeroᵣ {s .↓})
  where open import Relation.Binary.PropositionalEquality using (sym)
unmatch∀-≡ {□} refl s m' with s .proof
... | ⊑□ with refl ← m' = refl

unmatch+-≡-fst : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
                 (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
               → ∀ {a b} → (unmatch+ {τ} m s₁ s₂) .↓ ⊔ □ + □ ≡ a + b → s₁ .↓ ≡ a
unmatch+-≡-fst {α + β} refl s₁ s₂ m'
  rewrite ⊔t-zeroᵣ {α} | ⊔t-zeroᵣ {β}
  with refl ← m' = sym (⊔t-zeroᵣ {s₁ .↓})
  where open import Relation.Binary.PropositionalEquality using (sym)
unmatch+-≡-fst {□} refl s₁ s₂ m'
  with s₁ .proof | s₂ .proof
... | ⊑□ | ⊑□ with refl ← m' = refl

unmatch+-≡-snd : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ + □ ≡ τ₁ + τ₂)
                 (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
               → ∀ {a b} → (unmatch+ {τ} m s₁ s₂) .↓ ⊔ □ + □ ≡ a + b → s₂ .↓ ≡ b
unmatch+-≡-snd {α + β} refl s₁ s₂ m'
  rewrite ⊔t-zeroᵣ {α} | ⊔t-zeroᵣ {β}
  with refl ← m' = sym (⊔t-zeroᵣ {s₂ .↓})
  where open import Relation.Binary.PropositionalEquality using (sym)
unmatch+-≡-snd {□} refl s₁ s₂ m'
  with s₁ .proof | s₂ .proof
... | ⊑□ | ⊑□ with refl ← m' = refl

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
