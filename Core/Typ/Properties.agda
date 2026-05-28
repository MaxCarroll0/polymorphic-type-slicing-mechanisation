-- Algebraic properties of types and their slices: lattice identities (□ as zero, idempotency),
-- monotonicity of join/match decompositions, substitution and shifting compatibility, and
-- well-formedness preservation.
-- Dissertation: supports §4.1 Syntax & Relations and §4.2 Lattice Properties.
module Core.Typ.Properties where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong₂; cong; sym; trans)
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

-- Specialised to the value produced by ⊔-ann-⇒-⊑-intro-tight: outputs of
-- shape (□ ⇒ τ_b) for some τ_b. Such a value is consistent with τ_h ⇒ □ via
-- ~⇒ ~?₂ ~?₁ regardless of τ_h.
□⇒-~-ann-⇒ : ∀ {τ_h τ_b} → (□ ⇒ τ_b) ~ (τ_h ⇒ □)
□⇒-~-ann-⇒ = ~⇒ ~?₂ ~?₁

-- Full intro lemma: extends ⊔-ann-⇒-⊑-intro-tight to also return the
-- consistency τ' ~ τ_h₁⇒□. The output τ' is either □ or □⇒τ_b; both are
-- consistent with τ_h₁⇒□.
⊔-ann-⇒-⊑-intro-full : ∀ {τ τ_h τ_a τ₂ τ_h₁ τ_b} → τ ⊔ τ_h ⇒ □ ≡ τ_a ⇒ τ₂
           → τ_h₁ ⊑t τ_h → τ_b ⊑t τ₂
           → ∃[ τ' ] (τ' ⊑t τ) ∧ (τ' ⊔ τ_h₁ ⇒ □ ≡ τ_h₁ ⇒ τ_b) ∧ (τ' ~ τ_h₁ ⇒ □)
⊔-ann-⇒-⊑-intro-full {τ} {τ_h} eq τ_h₁⊑ τ_b⊑ with diag τ (τ_h ⇒ □)
⊔-ann-⇒-⊑-intro-full {τ_l ⇒ τ_r} {τ_h₁ = τ_h₁} {τ_b = τ_b} eq τ_h₁⊑ τ_b⊑ | kind⇒
  rewrite ⊔t-zeroᵣ {τ_r}
  with refl ← eq = (□ ⇒ τ_b) , ⊑⇒ ⊑□ τ_b⊑ , out-eq , ~⇒ ~?₂ ~?₁
  where
    out-eq : (□ ⇒ τ_b) ⊔ (τ_h₁ ⇒ □) ≡ τ_h₁ ⇒ τ_b
    out-eq rewrite ⊔t-zeroᵣ {τ_b} | ⊔t-zeroₗ {τ_h₁} = refl
⊔-ann-⇒-⊑-intro-full {τ} eq τ_h₁⊑ τ_b⊑ | diff with τ ≟ □
⊔-ann-⇒-⊑-intro-full {τ_h₁ = τ_h₁} refl τ_h₁⊑ ⊑□ | diff | yes refl
  = □ , ⊑□ , refl , ~?₂
⊔-ann-⇒-⊑-intro-full () _ _ | diff | no _


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

private
  ⇒-inj-snd : ∀ {a b c d : Typ} → a ⇒ b ≡ c ⇒ d → b ≡ d
  ⇒-inj-snd refl = refl

⊔-ann-⇒-cov-cod : ∀ {τ τ' τ_h τ_h' cod τ_a' τ_b'}
  → τ ⊑t τ'
  → τ ⊔ τ_h ⇒ □ ≡ τ_h ⇒ cod
  → τ' ⊔ τ_h' ⇒ □ ≡ τ_a' ⇒ τ_b'
  → cod ⊑t τ_b'
⊔-ann-⇒-cov-cod ⊑□ eq-1 _
  with refl ← eq-1 = ⊑□
⊔-ann-⇒-cov-cod {τ_h = τ_h} {τ_h' = τ_h'}
                (⊑⇒ {τ₁ = τ_l} {τ₂ = τ_r} {τ₁' = τ_l'} {τ₂' = τ_r'} p q) eq-1 eq-2
  rewrite ⊔t-zeroᵣ {τ_r} | ⊔t-zeroᵣ {τ_r'}
  with refl ← ⇒-inj-snd eq-1 | refl ← ⇒-inj-snd eq-2 = q

-- Introduction rules dual to the matching monotonicity lemmas above.
-- Where ⊔-+-⊑ etc. *eliminate* a precision proof (decomposing it into
-- component precisions via the match equation), the -intro variants
-- *introduce* a precision proof from component precisions plus the
-- outer match equation, choosing a τ' ⊑ τ that carries the matching
-- equation.
⊔-+-⊑-intro : ∀ {τ τ₁ τ₂ τ_a τ_b} → τ ⊔ □ + □ ≡ τ₁ + τ₂
       → τ_a ⊑t τ₁ → τ_b ⊑t τ₂
       → ∃[ τ' ] τ' ⊑t τ ∧ τ' ⊔ □ + □ ≡ τ_a + τ_b
⊔-+-⊑-intro {τ} eq τ_a⊑ τ_b⊑ with diag τ (□ + □)
⊔-+-⊑-intro {τ_l + τ_r} {τ_a = τ_a} {τ_b = τ_b} eq τ_a⊑ τ_b⊑ | kind+
  rewrite ⊔t-zeroᵣ {τ_l} | ⊔t-zeroᵣ {τ_r}
  with refl ← eq = (τ_a + τ_b) , ⊑+ τ_a⊑ τ_b⊑ , out-eq
  where
    out-eq : (τ_a + τ_b) ⊔ (□ + □) ≡ τ_a + τ_b
    out-eq rewrite ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b} = refl
⊔-+-⊑-intro {τ} eq τ_a⊑ τ_b⊑ | diff with τ ≟ □
⊔-+-⊑-intro refl ⊑□ ⊑□ | diff | yes refl = □ , ⊑□ , refl
⊔-+-⊑-intro () _ _ | diff | no _

⊔-×-⊑-intro : ∀ {τ τ₁ τ₂ τ_a τ_b} → τ ⊔ □ × □ ≡ τ₁ × τ₂
       → τ_a ⊑t τ₁ → τ_b ⊑t τ₂
       → ∃[ τ' ] τ' ⊑t τ ∧ τ' ⊔ □ × □ ≡ τ_a × τ_b
⊔-×-⊑-intro {τ} eq τ_a⊑ τ_b⊑ with diag τ (□ × □)
⊔-×-⊑-intro {τ_l × τ_r} {τ_a = τ_a} {τ_b = τ_b} eq τ_a⊑ τ_b⊑ | kind×
  rewrite ⊔t-zeroᵣ {τ_l} | ⊔t-zeroᵣ {τ_r}
  with refl ← eq = (τ_a × τ_b) , ⊑× τ_a⊑ τ_b⊑ , out-eq
  where
    out-eq : (τ_a × τ_b) ⊔ (□ × □) ≡ τ_a × τ_b
    out-eq rewrite ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b} = refl
⊔-×-⊑-intro {τ} eq τ_a⊑ τ_b⊑ | diff with τ ≟ □
⊔-×-⊑-intro refl ⊑□ ⊑□ | diff | yes refl = □ , ⊑□ , refl
⊔-×-⊑-intro () _ _ | diff | no _

⊔-⇒-⊑-intro : ∀ {τ τ₁ τ₂ τ_a τ_b} → τ ⊔ □ ⇒ □ ≡ τ₁ ⇒ τ₂
       → τ_a ⊑t τ₁ → τ_b ⊑t τ₂
       → ∃[ τ' ] τ' ⊑t τ ∧ τ' ⊔ □ ⇒ □ ≡ τ_a ⇒ τ_b
⊔-⇒-⊑-intro {τ} eq τ_a⊑ τ_b⊑ with diag τ (□ ⇒ □)
⊔-⇒-⊑-intro {τ_l ⇒ τ_r} {τ_a = τ_a} {τ_b = τ_b} eq τ_a⊑ τ_b⊑ | kind⇒
  rewrite ⊔t-zeroᵣ {τ_l} | ⊔t-zeroᵣ {τ_r}
  with refl ← eq = (τ_a ⇒ τ_b) , ⊑⇒ τ_a⊑ τ_b⊑ , out-eq
  where
    out-eq : (τ_a ⇒ τ_b) ⊔ (□ ⇒ □) ≡ τ_a ⇒ τ_b
    out-eq rewrite ⊔t-zeroᵣ {τ_a} | ⊔t-zeroᵣ {τ_b} = refl
⊔-⇒-⊑-intro {τ} eq τ_a⊑ τ_b⊑ | diff with τ ≟ □
⊔-⇒-⊑-intro refl ⊑□ ⊑□ | diff | yes refl = □ , ⊑□ , refl
⊔-⇒-⊑-intro () _ _ | diff | no _

⊔-ann-⇒-⊑-intro : ∀ {τ τ_h τ_a τ₂ τ_h₁ τ_b} → τ ⊔ τ_h ⇒ □ ≡ τ_a ⇒ τ₂
           → τ_h₁ ⊑t τ_h → τ_b ⊑t τ₂
           → ∃[ τ' ] (τ' ⊑t τ) ∧ ∃[ τ_a₁ ] (τ' ⊔ τ_h₁ ⇒ □ ≡ τ_a₁ ⇒ τ_b)
⊔-ann-⇒-⊑-intro {τ} {τ_h} eq τ_h₁⊑ τ_b⊑ with diag τ (τ_h ⇒ □)
⊔-ann-⇒-⊑-intro {τ_l ⇒ τ_r} {τ_h₁ = τ_h₁} {τ_b = τ_b} eq τ_h₁⊑ τ_b⊑ | kind⇒
  rewrite ⊔t-zeroᵣ {τ_r}
  with refl ← eq = (□ ⇒ τ_b) , ⊑⇒ ⊑□ τ_b⊑ , τ_h₁ , out-eq
  where
    out-eq : (□ ⇒ τ_b) ⊔ (τ_h₁ ⇒ □) ≡ τ_h₁ ⇒ τ_b
    out-eq rewrite ⊔t-zeroᵣ {τ_b} | ⊔t-zeroₗ {τ_h₁} = refl
⊔-ann-⇒-⊑-intro {τ} eq τ_h₁⊑ τ_b⊑ | diff with τ ≟ □
⊔-ann-⇒-⊑-intro {τ_h₁ = τ_h₁} refl τ_h₁⊑ ⊑□ | diff | yes refl
  = □ , ⊑□ , τ_h₁ , refl
⊔-ann-⇒-⊑-intro () _ _ | diff | no _

-- Tight variant: τ_a₁ is concretely τ_h₁ (the input precision's level-1 type).
-- Same as ⊔-ann-⇒-⊑-intro but with the dom-component pinned to τ_h₁ directly.
⊔-ann-⇒-⊑-intro-tight : ∀ {τ τ_h τ_a τ₂ τ_h₁ τ_b} → τ ⊔ τ_h ⇒ □ ≡ τ_a ⇒ τ₂
           → τ_h₁ ⊑t τ_h → τ_b ⊑t τ₂
           → ∃[ τ' ] (τ' ⊑t τ) ∧ (τ' ⊔ τ_h₁ ⇒ □ ≡ τ_h₁ ⇒ τ_b)
⊔-ann-⇒-⊑-intro-tight {τ} {τ_h} eq τ_h₁⊑ τ_b⊑ with diag τ (τ_h ⇒ □)
⊔-ann-⇒-⊑-intro-tight {τ_l ⇒ τ_r} {τ_h₁ = τ_h₁} {τ_b = τ_b} eq τ_h₁⊑ τ_b⊑ | kind⇒
  rewrite ⊔t-zeroᵣ {τ_r}
  with refl ← eq = (□ ⇒ τ_b) , ⊑⇒ ⊑□ τ_b⊑ , out-eq
  where
    out-eq : (□ ⇒ τ_b) ⊔ (τ_h₁ ⇒ □) ≡ τ_h₁ ⇒ τ_b
    out-eq rewrite ⊔t-zeroᵣ {τ_b} | ⊔t-zeroₗ {τ_h₁} = refl
⊔-ann-⇒-⊑-intro-tight {τ} eq τ_h₁⊑ τ_b⊑ | diff with τ ≟ □
⊔-ann-⇒-⊑-intro-tight {τ_h₁ = τ_h₁} refl τ_h₁⊑ ⊑□ | diff | yes refl
  = □ , ⊑□ , refl
⊔-ann-⇒-⊑-intro-tight () _ _ | diff | no _


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
shift-unshift : ∀ {c a} (τ : Typ) {τ' : Typ} → τ ⊑t shift c a τ' → shift c a (unshift c a τ) ≡ τ
shift-unshift □ _ = refl
shift-unshift * _ = refl
shift-unshift {c} {a} ⟨ k ⟩ {⟨ k' ⟩} p with k' <? c
shift-unshift {c} {a} ⟨ k ⟩ {⟨ k' ⟩} ⊑Var | yes k'<c with k' <? c
shift-unshift {c} {a} ⟨ k ⟩ {⟨ k' ⟩} ⊑Var | yes k'<c | yes _ with k' <? c
shift-unshift {c} {a} ⟨ k ⟩ {⟨ k' ⟩} ⊑Var | yes k'<c | yes _ | yes _ = refl
shift-unshift {c} {a} ⟨ k ⟩ {⟨ k' ⟩} ⊑Var | yes k'<c | yes _ | no nk = ⊥-elim (nk k'<c)
shift-unshift {c} {a} ⟨ k ⟩ {⟨ k' ⟩} ⊑Var | yes k'<c | no nk = ⊥-elim (nk k'<c)
shift-unshift {c} {a} ⟨ .(k' ℕ+ a) ⟩ {⟨ k' ⟩} ⊑Var | no k'≮c with (k' ℕ+ a) <? c
shift-unshift {c} {a} ⟨ .(k' ℕ+ a) ⟩ {⟨ k' ⟩} ⊑Var | no k'≮c | yes p<c =
  ⊥-elim (k'≮c (≤-trans (s≤s (m≤m+n k' a)) p<c))
shift-unshift {c} {a} ⟨ .(k' ℕ+ a) ⟩ {⟨ k' ⟩} ⊑Var | no k'≮c | no _ with ((k' ℕ+ a) ∸ a) <? c
shift-unshift {c} {a} ⟨ .(k' ℕ+ a) ⟩ {⟨ k' ⟩} ⊑Var | no k'≮c | no _ | yes p<c =
  ⊥-elim (k'≮c (subst (_< c) (m+n∸n≡m k' a) p<c))
shift-unshift {c} {a} ⟨ .(k' ℕ+ a) ⟩ {⟨ k' ⟩} ⊑Var | no k'≮c | no _ | no _ =
  cong ⟨_⟩ (cong (_ℕ+ a) (m+n∸n≡m k' a))
shift-unshift {c} {a} (τ₁ ⇒ τ₂) {τ₁' ⇒ τ₂'} (⊑⇒ p q) =
  cong₂ _⇒_ (shift-unshift τ₁ {τ₁'} p) (shift-unshift τ₂ {τ₂'} q)
shift-unshift {c} {a} (τ₁ + τ₂) {τ₁' + τ₂'} (⊑+ p q) =
  cong₂ _+_ (shift-unshift τ₁ {τ₁'} p) (shift-unshift τ₂ {τ₂'} q)
shift-unshift {c} {a} (τ₁ × τ₂) {τ₁' × τ₂'} (⊑× p q) =
  cong₂ _×_ (shift-unshift τ₁ {τ₁'} p) (shift-unshift τ₂ {τ₂'} q)
shift-unshift {c} {a} (∀· τ) {∀· τ'} (⊑∀ p) = cong ∀· (shift-unshift τ {τ'} p)
-- Absurd cases: compound τ with variable τ' has no precision proof
shift-unshift {c} {a} (τ + τ₁) {⟨ k' ⟩} p with k' <? c
... | yes _ with () ← p
... | no _ with () ← p
shift-unshift {c} {a} (τ × τ₁) {⟨ k' ⟩} p with k' <? c
... | yes _ with () ← p
... | no _ with () ← p
shift-unshift {c} {a} (τ ⇒ τ₁) {⟨ k' ⟩} p with k' <? c
... | yes _ with () ← p
... | no _ with () ← p
shift-unshift {c} {a} (∀· τ) {⟨ k' ⟩} p with k' <? c
... | yes _ with () ← p
... | no _ with () ← p

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
