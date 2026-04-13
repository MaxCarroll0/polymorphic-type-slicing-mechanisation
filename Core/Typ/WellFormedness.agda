module Core.Typ.WellFormedness where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n; _<ᵇ_; _∸_)
  renaming (_+_ to _ℕ+_; _≟_ to _≟ℕ_)
open import Data.Nat.Properties using (m≤n⇒m≤1+n; +-monoˡ-<; m≤m+n; ≤-trans; <-≤-trans; <ᵇ⇒<; ≤-pred)
open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (yes; no)

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

-- Weakening: adding a type variable preserves well-formedness
wf-weaken : ∀ {n τ} → n ⊢wf τ → suc n ⊢wf τ
wf-weaken wf*         = wf*
wf-weaken wf□         = wf□
wf-weaken (wfVar k<n) = wfVar (m≤n⇒m≤1+n k<n)
wf-weaken (wf+ p q)   = wf+ (wf-weaken p) (wf-weaken q)
wf-weaken (wf× p q)   = wf× (wf-weaken p) (wf-weaken q)
wf-weaken (wf⇒ p q)   = wf⇒ (wf-weaken p) (wf-weaken q)
wf-weaken (wf∀ p)     = wf∀ (wf-weaken p)

wfΓ-weaken : ∀ {n Γ} → n ⊢wfΓ Γ → suc n ⊢wfΓ Γ
wfΓ-weaken wfΓ[]      = wfΓ[]
wfΓ-weaken (wfΓ∷ p q) = wfΓ∷ (wf-weaken p) (wfΓ-weaken q)

-- Shifting preserves well-formedness
shift-preserves-wf : ∀ {n c a τ} → n ⊢wf τ → (n ℕ+ a) ⊢wf shift c a τ
shift-preserves-wf wf*         = wf*
shift-preserves-wf wf□         = wf□
shift-preserves-wf {c = c} {a = a} (wfVar {k = k} k<n) with k <ᵇ c
... | true  = wfVar (≤-trans k<n (m≤m+n _ a))
... | false = wfVar (+-monoˡ-< a k<n)
shift-preserves-wf (wf+ p q)   = wf+ (shift-preserves-wf p) (shift-preserves-wf q)
shift-preserves-wf (wf× p q)   = wf× (shift-preserves-wf p) (shift-preserves-wf q)
shift-preserves-wf (wf⇒ p q)   = wf⇒ (shift-preserves-wf p) (shift-preserves-wf q)
shift-preserves-wf (wf∀ p)     = wf∀ (shift-preserves-wf p)

shiftΓ-preserves-wf : ∀ {n a Γ} → n ⊢wfΓ Γ → (n ℕ+ a) ⊢wfΓ map (shift 0 a) Γ
shiftΓ-preserves-wf wfΓ[]      = wfΓ[]
shiftΓ-preserves-wf (wfΓ∷ p q) = wfΓ∷ (shift-preserves-wf p) (shiftΓ-preserves-wf q)

-- Substitution preserves well-formedness
private
  -- Extract m < k from m <ᵇ k ≡ true
  <ᵇ-true : ∀ m k → (m <ᵇ k) ≡ true → m < k
  <ᵇ-true m k eq = <ᵇ⇒< m k (subst T (sym eq) tt)

  sub-wf : ∀ (k : ℕ) {n σ τ}
          → k ≤ n → n ⊢wf σ → suc n ⊢wf τ → n ⊢wf [ k ↦ σ ] τ
  sub-wf k k≤n wfσ wf*         = wf*
  sub-wf k k≤n wfσ wf□         = wf□
  -- m = zero case
  sub-wf k k≤n wfσ (wfVar {k = zero} m<sn) with zero ≟ℕ k
  ... | yes _ = wfσ
  ... | no 0≠k with k
  ...   | zero   = ⊥-elim (0≠k refl)
  ...   | suc k' = wfVar (<-≤-trans (s≤s z≤n) k≤n)
  -- m = suc m' case
  sub-wf k k≤n wfσ (wfVar {k = suc m} m<sn) with suc m ≟ℕ k
  ... | yes _ = wfσ
  ... | no _ with suc m <ᵇ k in eq
  ...   | true  = wfVar (<-≤-trans (<ᵇ-true (suc m) k eq) k≤n)
  ...   | false = wfVar (≤-pred m<sn)
  -- Structural cases
  sub-wf k k≤n wfσ (wf+ p q)   = wf+ (sub-wf k k≤n wfσ p) (sub-wf k k≤n wfσ q)
  sub-wf k k≤n wfσ (wf× p q)   = wf× (sub-wf k k≤n wfσ p) (sub-wf k k≤n wfσ q)
  sub-wf k k≤n wfσ (wf⇒ p q)   = wf⇒ (sub-wf k k≤n wfσ p) (sub-wf k k≤n wfσ q)
  sub-wf k k≤n wfσ (wf∀ p)     = wf∀ (sub-wf (suc k) (s≤s k≤n) (wf-weaken wfσ) p)

sub-preserves-wf : ∀ {n σ τ} → n ⊢wf σ → suc n ⊢wf τ → n ⊢wf [ zero ↦ σ ] τ
sub-preserves-wf = sub-wf zero z≤n

-- Well-formedness is closed under precision
open import Core.Typ.Precision using (_⊑t_; ⊑□; ⊑*; ⊑Var; ⊑+; ⊑×; ⊑⇒; ⊑∀)
wf-⊑ : ∀ {n τ₁ τ₂} → n ⊢wf τ₂ → τ₁ ⊑t τ₂ → n ⊢wf τ₁
wf-⊑ _           ⊑□         = wf□
wf-⊑ wf*         ⊑*         = wf*
wf-⊑ (wfVar k<n) ⊑Var       = wfVar k<n
wf-⊑ (wf+ p q)   (⊑+ r s)   = wf+ (wf-⊑ p r) (wf-⊑ q s)
wf-⊑ (wf× p q)   (⊑× r s)   = wf× (wf-⊑ p r) (wf-⊑ q s)
wf-⊑ (wf⇒ p q)   (⊑⇒ r s)   = wf⇒ (wf-⊑ p r) (wf-⊑ q s)
wf-⊑ (wf∀ p)     (⊑∀ r)     = wf∀ (wf-⊑ p r)
