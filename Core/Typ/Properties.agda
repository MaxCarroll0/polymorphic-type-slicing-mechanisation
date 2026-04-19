module Core.Typ.Properties where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong₂; cong)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _∸_; _≤_; z≤n; s≤s) renaming (_+_ to _ℕ+_; _≟_ to _≟ℕ_)
open import Data.Nat.Properties using (m+n∸n≡m; m≤m+n; ≤-trans; <-trans; _<?_; <⇒≢; ≮⇒≥)
open import Data.Product using (∃; _,_; ∃-syntax)
open import Data.Product using () renaming (_×_ to _∧_)


open import Core.Typ.Base
open import Core.Typ.Equality
open import Core.Typ.Consistency
open import Core.Typ.Precision
open import Core.Typ.Lattice
open import Core.Instances
open import Core.Typ.Substitution
open import Core.Typ.WellFormedness
open import Core.Instances

-- □ is a zero object
⊔t-zeroₗ : ∀ {τ} → □ ⊔ τ ≡ τ
⊔t-zeroₗ {τ} with diag □ τ
...             | kind□ = refl
...             | diff  = refl

⊔t-zeroᵣ : ∀ {τ} → τ ⊔ □ ≡ τ
⊔t-zeroᵣ {τ} with diag τ □
...             | kind□ = refl
...             | diff with τ ≟ □
...                    | yes refl = refl
...                    | no  _    = refl

⊓t-zeroₗ : ∀ {τ} → □ ⊓ τ ≡ □
⊓t-zeroₗ {τ} with diag □ τ
...             | kind□ = refl
...             | diff  = refl

⊓t-zeroᵣ : ∀ {τ} → τ ⊓ □ ≡ □
⊓t-zeroᵣ {τ} with diag τ □
...             | kind□ = refl
...             | diff  = refl

-- Join idempotency
⊔t-idem : ∀ (τ : Typ) → τ ⊔ τ ≡ τ
⊔t-idem τ with diag τ τ in eq
... | kind□ = refl
... | kind* = refl
... | kindVar = refl
... | kind+ {τ₁} {τ₂} = cong₂ _+_ (⊔t-idem τ₁) (⊔t-idem τ₂)
... | kind× {τ₁} {τ₂} = cong₂ _×_ (⊔t-idem τ₁) (⊔t-idem τ₂)
... | kind⇒ {τ₁} {τ₂} = cong₂ _⇒_ (⊔t-idem τ₁) (⊔t-idem τ₂)
... | kind∀ {τ'} = cong ∀· (⊔t-idem τ')
... | diff = ⊥-elim (shallow-disequality eq)

-- Non-trivial join implies consistency with least specific compound type
-- i.e. such a join must be a valid LUB
⊔-⇒-~ : ∀ {τ τ₁ τ₂} → τ ⊔ (□ ⇒ □) ≡ τ₁ ⇒ τ₂ → τ ~ □ ⇒ □
⊔-⇒-~ {τ} eq with diag τ (□ ⇒ □)
...             | kind⇒ = ~⇒ ~?₁ ~?₁
⊔-⇒-~ {τ} eq    | diff with τ ≟ □
...                       | yes refl = ~?₂
⊔-⇒-~     ()    | diff    | no  _


⊔-+-~ : ∀ {τ τ₁ τ₂} → τ ⊔ (□ + □) ≡ τ₁ + τ₂ → τ ~ □ + □
⊔-+-~ {τ} eq with diag τ (□ + □)
...             | kind+ = ~+ ~?₁ ~?₁
⊔-+-~ {τ} eq    | diff with τ ≟ □
...                       | yes refl = ~?₂
⊔-+-~     ()    | diff    | no _

⊔-×-~ : ∀ {τ τ₁ τ₂} → τ ⊔ (□ × □) ≡ τ₁ × τ₂ → τ ~ □ × □
⊔-×-~ {τ} eq with diag τ (□ × □)
...             | kind× = ~× ~?₁ ~?₁
⊔-×-~ {τ} eq    | diff with τ ≟ □
...                       | yes refl = ~?₂
⊔-×-~     ()    | diff    | no _

⊔-∀-~ : ∀ {τ τ'} → τ ⊔ (∀· □) ≡ ∀· τ' → τ ~ ∀· □
⊔-∀-~ {τ} eq with diag τ (∀· □)
...             | kind∀ = ~∀ ~?₁
⊔-∀-~ {τ} eq    | diff with τ ≟ □
...                       | yes refl = ~?₂
⊔-∀-~     ()    | diff    | no _

-- Consistency with join result: if τ ~ σ and τ ⊔ σ ≡ ρ then τ ~ ρ
⊔-~-result : ∀ {τ σ ρ} → τ ~ σ → τ ⊔ σ ≡ ρ → τ ~ ρ
⊔-~-result c eq = subst (_ ~_) eq (⊑to~ (~.⊔-ub₁ c))


-- Matching monotonicity: precision preserved by type matching (via join)
⊔-⇒-⊑ : ∀ {τ₁ τ₂ τ₂a τ₂b}
        → τ₁ ⊑t τ₂ → τ₂ ⊔ □ ⇒ □ ≡ τ₂a ⇒ τ₂b →
        ∃[ τ₁a ] ∃[ τ₁b ] τ₁ ⊔ □ ⇒ □ ≡ τ₁a ⇒ τ₁b
                          ∧ τ₁a ⊑t τ₂a ∧ τ₁b ⊑t τ₂b
⊔-⇒-⊑ ⊑□ _ = _ , _ , refl , ⊑□ , ⊑□
⊔-⇒-⊑ (⊑⇒ {τ₁ = a₁} {τ₂ = b₁} {τ₁' = a₂} {τ₂' = b₂} p q) eq
  rewrite ⊔t-zeroᵣ {a₁} | ⊔t-zeroᵣ {b₁} | ⊔t-zeroᵣ {a₂} | ⊔t-zeroᵣ {b₂}
  with refl ← eq = _ , _ , refl , p , q

⊔-+-⊑ : ∀ {τ₁ τ₂ τ₂a τ₂b}
        → τ₁ ⊑t τ₂ → τ₂ ⊔ □ + □ ≡ τ₂a + τ₂b →
        ∃[ τ₁a ] ∃[ τ₁b ] τ₁ ⊔ □ + □ ≡ τ₁a + τ₁b
                          ∧ τ₁a ⊑t τ₂a ∧ τ₁b ⊑t τ₂b
⊔-+-⊑ ⊑□ _ = _ , _ , refl , ⊑□ , ⊑□
⊔-+-⊑ (⊑+ {τ₁ = a₁} {τ₂ = b₁} {τ₁' = a₂} {τ₂' = b₂} p q) eq
  rewrite ⊔t-zeroᵣ {a₁} | ⊔t-zeroᵣ {b₁} | ⊔t-zeroᵣ {a₂} | ⊔t-zeroᵣ {b₂}
  with refl ← eq = _ , _ , refl , p , q

⊔-×-⊑ : ∀ {τ₁ τ₂ τ₂a τ₂b}
      → τ₁ ⊑t τ₂ → τ₂ ⊔ □ × □ ≡ τ₂a × τ₂b →
      ∃[ τ₁a ] ∃[ τ₁b ] τ₁ ⊔ □ × □ ≡ τ₁a × τ₁b
                        ∧ τ₁a ⊑t τ₂a ∧ τ₁b ⊑t τ₂b
⊔-×-⊑ ⊑□ _ = _ , _ , refl , ⊑□ , ⊑□
⊔-×-⊑ (⊑× {τ₁ = a₁} {τ₂ = b₁} {τ₁' = a₂} {τ₂' = b₂} p q) eq
  rewrite ⊔t-zeroᵣ {a₁} | ⊔t-zeroᵣ {b₁} | ⊔t-zeroᵣ {a₂} | ⊔t-zeroᵣ {b₂}
  with refl ← eq = _ , _ , refl , p , q

⊔-∀-⊑ : ∀ {τ₁ τ₂ τ₂'}
        → τ₁ ⊑t τ₂ → τ₂ ⊔ ∀· □ ≡ ∀· τ₂' →
        ∃[ τ₁' ] τ₁ ⊔ ∀· □ ≡ ∀· τ₁'
                 ∧ τ₁' ⊑t τ₂'
⊔-∀-⊑ ⊑□ _ = _ , refl , ⊑□
⊔-∀-⊑ (⊑∀ {τ = a₁} {τ' = a₂} p) eq
  rewrite ⊔t-zeroᵣ {a₁} | ⊔t-zeroᵣ {a₂}
  with refl ← eq = _ , refl , p

-- (Annotated functions)
⊔-ann-⇒-⊑ : ∀ {τ₁ τ₂ τ₁a τ₂a τ₂a' τ₂b}
            → τ₁ ⊑t τ₂ → τ₁a ⊑t τ₂a
            → τ₂ ⊔ τ₂a ⇒ □ ≡ τ₂a' ⇒ τ₂b →
            ∃[ τ₁a' ] ∃[ τ₁b ] τ₁ ⊔ τ₁a ⇒ □ ≡ τ₁a' ⇒ τ₁b
                               ∧ τ₁b ⊑t τ₂b
⊔-ann-⇒-⊑ ⊑□ _ _ = _ , _ , refl , ⊑□
⊔-ann-⇒-⊑ (⊑⇒ {τ₂ = b₁} {τ₂' = b₂} p q) r eq
  rewrite ⊔t-zeroᵣ {b₁} | ⊔t-zeroᵣ {b₂}
  with refl ← eq = _ , _ , refl , q


-- Shifting preserves precision
shift-⊑ : ∀ {τ₁ τ₂} (c a : ℕ) → τ₁ ⊑t τ₂ → shift c a τ₁ ⊑t shift c a τ₂
shift-⊑ c a ⊑□         = ⊑□
shift-⊑ c a ⊑*         = ⊑*
shift-⊑ c a (⊑Var {n = k}) with k <? c
...                           | yes _ = ⊑Var
...                           | no  _ = ⊑Var
shift-⊑ c a (⊑⇒ p q)   = ⊑⇒ (shift-⊑ c a p) (shift-⊑ c a q)
shift-⊑ c a (⊑+ p q)   = ⊑+ (shift-⊑ c a p) (shift-⊑ c a q)
shift-⊑ c a (⊑× p q)   = ⊑× (shift-⊑ c a p) (shift-⊑ c a q)
shift-⊑ c a (⊑∀ p)     = ⊑∀ (shift-⊑ (suc c) a p)

-- Unshifting preserves precision (analogous to shift-⊑).
unshift-⊑ : ∀ {τ₁ τ₂} (c a : ℕ) → τ₁ ⊑t τ₂ → unshift c a τ₁ ⊑t unshift c a τ₂
unshift-⊑ c a ⊑□         = ⊑□
unshift-⊑ c a ⊑*         = ⊑*
unshift-⊑ c a (⊑Var {n = k}) with k <? c
...                             | yes _ = ⊑Var
...                             | no  _ = ⊑Var
unshift-⊑ c a (⊑⇒ p q)   = ⊑⇒ (unshift-⊑ c a p) (unshift-⊑ c a q)
unshift-⊑ c a (⊑+ p q)   = ⊑+ (unshift-⊑ c a p) (unshift-⊑ c a q)
unshift-⊑ c a (⊑× p q)   = ⊑× (unshift-⊑ c a p) (unshift-⊑ c a q)
unshift-⊑ c a (⊑∀ p)     = ⊑∀ (unshift-⊑ (suc c) a p)

-- unshift is a left inverse of shift.
unshift-shift : ∀ {c a} (τ : Typ) → unshift c a (shift c a τ) ≡ τ
unshift-shift {c} {a} ⟨ k ⟩ with k <? c
... | yes k<c with (k <? c)
...   | yes _ = refl
...   | no k≮c = ⊥-elim (k≮c k<c)
unshift-shift {c} {a} ⟨ k ⟩ | no k≮c with (k ℕ+ a) <? c
...   | yes k+a<c = ⊥-elim (k≮c (≤-trans (s≤s (m≤m+n k a)) k+a<c))
...   | no  _     = cong ⟨_⟩ (m+n∸n≡m k a)
unshift-shift *         = refl
unshift-shift □         = refl
unshift-shift (τ₁ + τ₂) = cong₂ _+_ (unshift-shift τ₁) (unshift-shift τ₂)
unshift-shift (τ₁ × τ₂) = cong₂ _×_ (unshift-shift τ₁) (unshift-shift τ₂)
unshift-shift (τ₁ ⇒ τ₂) = cong₂ _⇒_ (unshift-shift τ₁) (unshift-shift τ₂)
unshift-shift (∀· τ)    = cong ∀· (unshift-shift τ)

-- unshift is (half) left adjoint to shift.
unshift-shift-⊑ : ∀ {c a τ τ'} → τ' ⊑t shift c a τ → unshift c a τ' ⊑t τ
unshift-shift-⊑ {c} {a} {τ} {τ'} p =
  subst (λ x → unshift c a τ' ⊑t x) (unshift-shift τ) (unshift-⊑ c a p)

-- shift is a right inverse of unshift (when τ ⊑ shift τ').
postulate
  shift-unshift : ∀ {c a} (τ : Typ) {τ' : Typ} → τ ⊑t shift c a τ' → shift c a (unshift c a τ) ≡ τ

-- Substitution preserves precision
sub-⊑ : ∀ (k : ℕ) {σ₁ σ₂ τ₁ τ₂} → σ₁ ⊑t σ₂ → τ₁ ⊑t τ₂ → [ k ↦ σ₁ ] τ₁ ⊑t [ k ↦ σ₂ ] τ₂
sub-⊑ k σ⊑ ⊑□         = ⊑□
sub-⊑ k σ⊑ ⊑*         = ⊑*
sub-⊑ k σ⊑ (⊑Var {n = m}) with m ≟ℕ k
... | yes _ = σ⊑
... | no  _ with m <? k
...            | yes _ = ⊑Var
...            | no  _ = ⊑Var
sub-⊑ k σ⊑ (⊑⇒ p q)    = ⊑⇒ (sub-⊑ k σ⊑ p) (sub-⊑ k σ⊑ q)
sub-⊑ k σ⊑ (⊑+ p q)    = ⊑+ (sub-⊑ k σ⊑ p) (sub-⊑ k σ⊑ q)
sub-⊑ k σ⊑ (⊑× p q)    = ⊑× (sub-⊑ k σ⊑ p) (sub-⊑ k σ⊑ q)
sub-⊑ k σ⊑ (⊑∀ p)      = ⊑∀ (sub-⊑ (suc k) σ⊑ p)

-- Join monotonicity
⊔-mono-⊑ : ∀ {τ₁ τ₂ τ₁' τ₂'}
           → τ₁' ~ τ₂' → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂'
           → τ₁ ⊔ τ₂ ⊑t τ₁' ⊔ τ₂'
⊔-mono-⊑ c p q =
  let p' = ⊑.trans p (~.⊔-ub₁ c)
      q' = ⊑.trans q (~.⊔-ub₂ c)
  in ~.⊔-lub (⊑-consistent p' q') p' q'

-- Well-formedness of inner type components
⊔-⇒-wf₁ : ∀ {n τ τ₁ τ₂} → n ⊢wf τ → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂ → n ⊢wf τ₁
⊔-⇒-wf₁ wf□ refl = wf□
⊔-⇒-wf₁ (wf⇒ {τ₁ = a} {τ₂ = b} p q) eq
  rewrite ⊔t-zeroᵣ {a} | ⊔t-zeroᵣ {b}
  with refl ← eq = p

⊔-+-wf₁ : ∀ {n τ τ₁ τ₂} → n ⊢wf τ → τ ⊔ □ + □ ≡ τ₁ + τ₂ → n ⊢wf τ₁
⊔-+-wf₁ wf□ refl = wf□
⊔-+-wf₁ (wf+ {τ₁ = a} {τ₂ = b} p q) eq
  rewrite ⊔t-zeroᵣ {a} | ⊔t-zeroᵣ {b}
  with refl ← eq = p

⊔-+-wf₂ : ∀ {n τ τ₁ τ₂} → n ⊢wf τ → τ ⊔ □ + □ ≡ τ₁ + τ₂ → n ⊢wf τ₂
⊔-+-wf₂ wf□ refl = wf□
⊔-+-wf₂ (wf+ {τ₁ = a} {τ₂ = b} p q) eq
  rewrite ⊔t-zeroᵣ {a} | ⊔t-zeroᵣ {b}
  with refl ← eq = q

⊔-⇒-wf₂ : ∀ {n τ τ₁ τ₂} → n ⊢wf τ → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂ → n ⊢wf τ₂
⊔-⇒-wf₂ wf□ refl = wf□
⊔-⇒-wf₂ (wf⇒ {τ₁ = a} {τ₂ = b} p q) eq
  rewrite ⊔t-zeroᵣ {a} | ⊔t-zeroᵣ {b}
  with refl ← eq = q

⊔-×-wf₁ : ∀ {n τ τ₁ τ₂} → n ⊢wf τ → τ ⊔ □ × □ ≡ τ₁ × τ₂ → n ⊢wf τ₁
⊔-×-wf₁ wf□ refl = wf□
⊔-×-wf₁ (wf× {τ₁ = a} {τ₂ = b} p q) eq
  rewrite ⊔t-zeroᵣ {a} | ⊔t-zeroᵣ {b}
  with refl ← eq = p

⊔-×-wf₂ : ∀ {n τ τ₁ τ₂} → n ⊢wf τ → τ ⊔ □ × □ ≡ τ₁ × τ₂ → n ⊢wf τ₂
⊔-×-wf₂ wf□ refl = wf□
⊔-×-wf₂ (wf× {τ₁ = a} {τ₂ = b} p q) eq
  rewrite ⊔t-zeroᵣ {a} | ⊔t-zeroᵣ {b}
  with refl ← eq = q

⊔-∀-wf : ∀ {n τ τ'} → n ⊢wf τ → τ ⊔ ∀· □ ≡ ∀· τ' → suc n ⊢wf τ'
⊔-∀-wf wf□ refl = wf□
⊔-∀-wf (wf∀ {τ = a} p) eq
  rewrite ⊔t-zeroᵣ {a}
  with refl ← eq = p

⊔-ann-⇒-~λ : ∀ {τ σ τ₁ τ₂} → τ ~ σ ⇒ □ → τ ⊔ σ ⇒ □ ≡ τ₁ ⇒ τ₂ → σ ⇒ τ₂ ~ τ₁ ⇒ τ₂
⊔-ann-⇒-~λ ~?₂ refl = ⊑to~ ⊑.refl
⊔-ann-⇒-~λ (~⇒ {τ₂ = b} ca _) eq
  rewrite ⊔t-zeroᵣ {b}
  with refl ← eq = ~⇒ (⊑to~ (~.⊔-ub₂ ca)) (⊑to~ ⊑.refl)

⊔-ann-⇒-wf₂ : ∀ {n τ σ τ₁ τ₂} → n ⊢wf τ → n ⊢wf σ → τ ⊔ σ ⇒ □ ≡ τ₁ ⇒ τ₂ → n ⊢wf τ₂
⊔-ann-⇒-wf₂ wf□ _ refl = wf□
⊔-ann-⇒-wf₂ (wf⇒ {τ₂ = b} _ q) _ eq
  rewrite ⊔t-zeroᵣ {b}
  with refl ← eq = q

-- Join preserves well-formedness (under consistency)
⊔-wf : ∀ {n τ₁ τ₂} → n ⊢wf τ₁ → n ⊢wf τ₂ → τ₁ ~ τ₂ → n ⊢wf (τ₁ ⊔ τ₂)
⊔-wf wf₁ wf₂ ~*                     = wf*
⊔-wf wf₁ wf₂ ~Var                   = wf₁
⊔-wf {τ₁ = τ₁} wf₁ _ ~?₁           rewrite ⊔t-zeroᵣ {τ₁} = wf₁
⊔-wf {τ₂ = τ₂} _ wf₂ ~?₂           rewrite ⊔t-zeroₗ {τ₂} = wf₂
⊔-wf (wf+ p₁ p₂) (wf+ q₁ q₂) (~+ c₁ c₂) = wf+ (⊔-wf p₁ q₁ c₁) (⊔-wf p₂ q₂ c₂)
⊔-wf (wf× p₁ p₂) (wf× q₁ q₂) (~× c₁ c₂) = wf× (⊔-wf p₁ q₁ c₁) (⊔-wf p₂ q₂ c₂)
⊔-wf (wf⇒ p₁ p₂) (wf⇒ q₁ q₂) (~⇒ c₁ c₂) = wf⇒ (⊔-wf p₁ q₁ c₁) (⊔-wf p₂ q₂ c₂)
⊔-wf (wf∀ p) (wf∀ q) (~∀ c)         = wf∀ (⊔-wf p q c)

⊔□×□ : ∀ {τ₁ τ₂ : Typ} → τ₁ × τ₂ ⊔ □ × □ ≡ τ₁ × τ₂
⊔□×□ {τ₁} {τ₂} rewrite ⊔t-zeroᵣ {τ₁} | ⊔t-zeroᵣ {τ₂} = refl

⊔□⇒□ : ∀ {τ₁ τ₂ : Typ} → τ₁ ⇒ τ₂ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂
⊔□⇒□ {τ₁} {τ₂} rewrite ⊔t-zeroᵣ {τ₁} | ⊔t-zeroᵣ {τ₂} = refl

⊔□∀□ : ∀ {τ : Typ} → ∀· τ ⊔ ∀· □ ≡ ∀· τ
⊔□∀□ {τ} rewrite ⊔t-zeroᵣ {τ} = refl

⊔□+□ : ∀ {τ₁ τ₂ : Typ} → τ₁ + τ₂ ⊔ □ + □ ≡ τ₁ + τ₂
⊔□+□ {τ₁} {τ₂} rewrite ⊔t-zeroᵣ {τ₁} | ⊔t-zeroᵣ {τ₂} = refl
