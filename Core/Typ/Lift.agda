module Core.Typ.Lift where

open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no)

open import Core.Typ.Base using (Typ; □; _⇒_; _×_; ∀·; _+_; diag; _kind?_; kind□; kind⇒; kind×; kind+; kind∀; diff)
open import Core.Typ.Precision
open import Core.Typ.Lattice -- for instances
open import Core.Typ.Properties using (⊔t-zeroₗ; ⊔t-zeroᵣ; sub-⊑; ⊔-⇒-⊑; ⊔-×-⊑; ⊔-∀-⊑; ⊔-+-⊑; ⊔-mono-⊑; ⊔□+□)
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

-- Extract component equalities from unmatch⇒ match
postulate
  unmatch⇒-≡-fst : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂)
                 (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
                 → ∀ {a b} → (unmatch⇒ {τ} m s₁ s₂) .↓ ⊔ □ ⇒ □ ≡ a ⇒ b → s₁ .↓ ≡ a

  unmatch⇒-≡-snd : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂)
                 (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
                 → ∀ {a b} → (unmatch⇒ {τ} m s₁ s₂) .↓ ⊔ □ ⇒ □ ≡ a ⇒ b → s₂ .↓ ≡ b

  unmatch×-≡-fst : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ × □ ≡ τ₁ × τ₂)
                 (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
                 → ∀ {a b} → (unmatch× {τ} m s₁ s₂) .↓ ⊔ □ × □ ≡ a × b → s₁ .↓ ≡ a

  unmatch×-≡-snd : ∀ {τ τ₁ τ₂} (m : τ ⊔ □ × □ ≡ τ₁ × τ₂)
                 (s₁ : ⌊ τ₁ ⌋) (s₂ : ⌊ τ₂ ⌋)
                 → ∀ {a b} → (unmatch× {τ} m s₁ s₂) .↓ ⊔ □ × □ ≡ a × b → s₂ .↓ ≡ b

  unmatch∀-≡ : ∀ {τ τ'} (m : τ ⊔ ∀· □ ≡ ∀· τ')
               (s : ⌊ τ' ⌋)
               → ∀ {a} → (unmatch∀ {τ} m s) .↓ ⊔ ∀· □ ≡ ∀· a → s .↓ ≡ a
