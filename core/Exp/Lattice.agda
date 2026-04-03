module core.Exp.Lattice where

open import Data.Nat using (ℕ; _≟_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Relation.Binary using (IsPartialOrder)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Maximum; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Binary.Lattice.Structures using (IsMeetSemilattice; IsJoinSemilattice; IsLattice; IsBoundedLattice)
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum)
open import Relation.Nullary using (yes; no)
open import Function using (_on_)

open import core.Typ using (Typ; _≟t_; _⊑t_; ⊑?; ⊑t-refl; ⊑t-trans; ⊑t-antisym;
                            _⊓t_; ⊓t-lb₁; ⊓t-lb₂; ⊓t-glb;
                            _⊔t_; ⊔t-ub₁; ⊔t-ub₂; ⊔t-preserves-⊑; ⊑t-consistent)
open import core.Exp.Base
open import core.Exp.Equality
open import core.Exp.Precision

-- Instantiate generic Slice module for expressions
open import Slice _⊑e_ (λ _ → □e) (λ _ → ⊑□) (λ _ → ⊑□) ⊑e-refl ⊑e-trans public
  renaming (SliceOf to SliceOfExp; _⊑ₛ_ to _⊑eₛ_; ⊤ₛ to ⊤eₛ; ⊥ₛ to ⊥eₛ; weaken to ⊑eₛ-weaken; weaken-identity to ⊑eₛ-weaken-identity; ⊥ₛ-min to ⊥eₛ-min')

-- Lifted partial order on slices of an expression
⊑eₛ-refl : ∀ {e} → Reflexive (_⊑eₛ_ {e})
⊑eₛ-refl = ⊑e-refl

⊑eₛ-trans : ∀ {e} → Transitive (_⊑eₛ_ {e})
⊑eₛ-trans = ⊑e-trans

⊑eₛ-antisym : ∀ {e} → Antisymmetric (_≡_ on ↓) (_⊑eₛ_ {e})
⊑eₛ-antisym = ⊑e-antisym

⊑eₛ-isPartialOrder : ∀ {e} → IsPartialOrder (_≡_ on ↓) (_⊑eₛ_ {e})
⊑eₛ-isPartialOrder = record
  { isPreorder = record
    { isEquivalence = record
      { refl = refl ; sym = sym ; trans = trans }
    ; reflexive = λ where refl → ⊑e-refl
    ; trans = λ {e''} {e'} {e} → ⊑e-trans
    }
  ; antisym = λ {e'} {e} → ⊑e-antisym
  }

-- Meets. Note: order theoretic.
_⊓e_ : Exp → Exp → Exp
e ⊓e e' with diag e e'
...        | diff  = □e
...        | kind□ = □e
...        | kind* = *e
...        | kindVar {m} {n} with m ≟ n
...                          | yes _ = < m >
...                          | no  _ = □e
(λ· τ ⇒ e₁) ⊓e (λ· τ' ⇒ e₁') | kindλ = λ· (τ ⊓t τ') ⇒ (e₁ ⊓e e₁')
(e₁ ∘ e₂)   ⊓e (e₁' ∘ e₂')   | kind∘ = (e₁ ⊓e e₁') ∘ (e₂ ⊓e e₂')
(e₁ & e₂)   ⊓e (e₁' & e₂')   | kind& = (e₁ ⊓e e₁') & (e₂ ⊓e e₂')
(ιₗ e₁)     ⊓e (ιₗ e₁')      | kindιₗ = ιₗ (e₁ ⊓e e₁')
(ιᵣ e₁)     ⊓e (ιᵣ e₁')      | kindιᵣ = ιᵣ (e₁ ⊓e e₁')
(Λ e₁)      ⊓e (Λ e₁')       | kindΛ = Λ (e₁ ⊓e e₁')
(def e₁ ⊢ e₂) ⊓e (def e₁' ⊢ e₂') | kinddef = def (e₁ ⊓e e₁') ⊢ (e₂ ⊓e e₂')

infixl 6 _⊓e_

-- Meets form a bounded semi-lattice (GLB property)
⊓e-lb₁ : ∀ e₁ e₂ → e₁ ⊓e e₂ ⊑e e₁
⊓e-lb₁ e         e'            with diag e e'
⊓e-lb₁ □e        □e               | kind□   = ⊑□
⊓e-lb₁ *e        *e               | kind*   = ⊑*
⊓e-lb₁ < m >     < n >            | kindVar with m ≟ n
...                                         | yes _ = ⊑Var
...                                         | no  _ = ⊑□
⊓e-lb₁ (λ· τ ⇒ e₁) (λ· τ' ⇒ e₁')  | kindλ   = ⊑λ (⊓t-lb₁ τ τ') (⊓e-lb₁ e₁ e₁')
⊓e-lb₁ (e₁ ∘ e₂) (e₁' ∘ e₂')      | kind∘   = ⊑∘ (⊓e-lb₁ e₁ e₁') (⊓e-lb₁ e₂ e₂')
⊓e-lb₁ (e₁ & e₂) (e₁' & e₂')      | kind&   = ⊑& (⊓e-lb₁ e₁ e₁') (⊓e-lb₁ e₂ e₂')
⊓e-lb₁ (ιₗ e₁)   (ιₗ e₁')         | kindιₗ  = ⊑ιₗ (⊓e-lb₁ e₁ e₁')
⊓e-lb₁ (ιᵣ e₁)   (ιᵣ e₁')         | kindιᵣ  = ⊑ιᵣ (⊓e-lb₁ e₁ e₁')
⊓e-lb₁ (Λ e₁)    (Λ e₁')          | kindΛ   = ⊑Λ (⊓e-lb₁ e₁ e₁')
⊓e-lb₁ (def e₁ ⊢ e₂) (def e₁' ⊢ e₂') | kinddef = ⊑def (⊓e-lb₁ e₁ e₁') (⊓e-lb₁ e₂ e₂')
⊓e-lb₁ _         _                | diff    = ⊑□

⊓e-lb₂ : ∀ e₁ e₂ → e₁ ⊓e e₂ ⊑e e₂
⊓e-lb₂ e         e'            with diag e e'
⊓e-lb₂ □e        □e               | kind□   = ⊑□
⊓e-lb₂ *e        *e               | kind*   = ⊑*
⊓e-lb₂ < m >     < n >            | kindVar with m ≟ n
...                                         | yes refl = ⊑Var
...                                         | no  _    = ⊑□
⊓e-lb₂ (λ· τ ⇒ e₁) (λ· τ' ⇒ e₁')  | kindλ   = ⊑λ (⊓t-lb₂ τ τ') (⊓e-lb₂ e₁ e₁')
⊓e-lb₂ (e₁ ∘ e₂) (e₁' ∘ e₂')      | kind∘   = ⊑∘ (⊓e-lb₂ e₁ e₁') (⊓e-lb₂ e₂ e₂')
⊓e-lb₂ (e₁ & e₂) (e₁' & e₂')      | kind&   = ⊑& (⊓e-lb₂ e₁ e₁') (⊓e-lb₂ e₂ e₂')
⊓e-lb₂ (ιₗ e₁)   (ιₗ e₁')         | kindιₗ  = ⊑ιₗ (⊓e-lb₂ e₁ e₁')
⊓e-lb₂ (ιᵣ e₁)   (ιᵣ e₁')         | kindιᵣ  = ⊑ιᵣ (⊓e-lb₂ e₁ e₁')
⊓e-lb₂ (Λ e₁)    (Λ e₁')          | kindΛ   = ⊑Λ (⊓e-lb₂ e₁ e₁')
⊓e-lb₂ (def e₁ ⊢ e₂) (def e₁' ⊢ e₂') | kinddef = ⊑def (⊓e-lb₂ e₁ e₁') (⊓e-lb₂ e₂ e₂')
⊓e-lb₂ _         _                | diff    = ⊑□

⊓e-glb : ∀ {e e₁ e₂} → e ⊑e e₁ → e ⊑e e₂ → e ⊑e e₁ ⊓e e₂
⊓e-glb ⊑□ _                      = ⊑□
⊓e-glb ⊑* ⊑*                     = ⊑*
⊓e-glb (⊑Var {m}) (⊑Var {m}) with m ≟ m
... | yes _ = ⊑Var
... | no contr = ⊥-elim (contr refl)
⊓e-glb (⊑λ p₁ p₂) (⊑λ q₁ q₂)     = ⊑λ (⊓t-glb p₁ q₁) (⊓e-glb p₂ q₂)
⊓e-glb (⊑∘ p₁ p₂) (⊑∘ q₁ q₂)     = ⊑∘ (⊓e-glb p₁ q₁) (⊓e-glb p₂ q₂)
⊓e-glb (⊑& p₁ p₂) (⊑& q₁ q₂)     = ⊑& (⊓e-glb p₁ q₁) (⊓e-glb p₂ q₂)
⊓e-glb (⊑ιₗ p)    (⊑ιₗ q)        = ⊑ιₗ (⊓e-glb p q)
⊓e-glb (⊑ιᵣ p)    (⊑ιᵣ q)        = ⊑ιᵣ (⊓e-glb p q)
⊓e-glb (⊑Λ p)     (⊑Λ q)         = ⊑Λ (⊓e-glb p q)
⊓e-glb (⊑def p₁ p₂) (⊑def q₁ q₂) = ⊑def (⊓e-glb p₁ q₁) (⊓e-glb p₂ q₂)

-- Meets preserve precision
⊓e-preserves-⊑ : ∀ {e₁ e₁' e₂ e₂'} → e₁' ⊑e e₁ → e₂' ⊑e e₂ → e₁' ⊓e e₂' ⊑e e₁ ⊓e e₂
⊓e-preserves-⊑ {_} {e₁'} {_} {e₂'} lb₁ lb₂ = ⊓e-glb (⊑e-trans (⊓e-lb₁ e₁' e₂') lb₁) (⊑e-trans (⊓e-lb₂ e₁' e₂') lb₂)

-- In particular when e₁ = e₂ then we get the same notion as the slice joins below
⊓e-preserves-⊑-spec : ∀ {e₁ e₂ e : Exp} → e₁ ⊑e e → e₂ ⊑e e → e₁ ⊓e e₂ ⊑e e
⊓e-preserves-⊑-spec p₁ p₂ = ⊑e-trans (⊓e-lb₁ _ _) p₁

-- Meet is greatest lower bound
⊓e-infimum : Infimum _⊑e_ _⊓e_
⊓e-infimum e₁ e₂ = ⊓e-lb₁ e₁ e₂ , ⊓e-lb₂ e₁ e₂ , λ e → ⊓e-glb {e} {e₁} {e₂}

-- Meet semilattice structure
⊓e-isMeetSemilattice : IsMeetSemilattice _≡_ _⊑e_ _⊓e_
⊓e-isMeetSemilattice = record
  { isPartialOrder = ⊑e-isPartialOrder
  ; infimum        = ⊓e-infimum
  }

-- Joins. For expressions, slices of the same expression always have an upper bound (the expression itself)
_⊔e_ : Exp → Exp → Exp
e ⊔e e' with diag e e'
...        | kind□ = □e
...        | kind* = *e
...        | kindVar {m} {n} = < m >
(λ· τ ⇒ e₁) ⊔e (λ· τ' ⇒ e₁')     | kindλ = λ· (τ ⊔t τ') ⇒ (e₁ ⊔e e₁')
(e₁ ∘ e₂)   ⊔e (e₁' ∘ e₂')       | kind∘ = (e₁ ⊔e e₁') ∘ (e₂ ⊔e e₂')
(e₁ & e₂)   ⊔e (e₁' & e₂')       | kind& = (e₁ ⊔e e₁') & (e₂ ⊔e e₂')
(ιₗ e₁)     ⊔e (ιₗ e₁')          | kindιₗ = ιₗ (e₁ ⊔e e₁')
(ιᵣ e₁)     ⊔e (ιᵣ e₁')          | kindιᵣ = ιᵣ (e₁ ⊔e e₁')
(Λ e₁)      ⊔e (Λ e₁')           | kindΛ = Λ (e₁ ⊔e e₁')
(def e₁ ⊢ e₂) ⊔e (def e₁' ⊢ e₂') | kinddef = def (e₁ ⊔e e₁') ⊢ (e₂ ⊔e e₂')
-- For diff case, use decidability to pick the non-bottom element
e ⊔e e'    | diff with e ≟e □e
...                  | yes _ = e'
...                  | no  _ = e

infixl 6 _⊔e_

-- Join identity lemmas
⊔e-identityₗ : ∀ e → □e ⊔e e ≡ e
⊔e-identityₗ e with diag □e e
⊔e-identityₗ □e | kind□ = refl
⊔e-identityₗ _  | diff  = refl

⊔e-identityᵣ : ∀ e → e ⊔e □e ≡ e
⊔e-identityᵣ e with diag e □e
⊔e-identityᵣ □e | kind□ = refl
⊔e-identityᵣ e  | diff with e ≟e □e
...                    | yes refl = refl
...                    | no  _    = refl

-- Upper bound proofs (for slices of the same expression)
-- This is the key lemma: if e₁ ⊑e e and e₂ ⊑e e, then e₁ ⊔e e₂ ⊑e e
⊔e-preserves-⊑ : ∀ {e₁ e₂ e} → e₁ ⊑e e → e₂ ⊑e e → e₁ ⊔e e₂ ⊑e e
⊔e-preserves-⊑ ⊑□ ⊑□                               = ⊑□
⊔e-preserves-⊑ {e₂ = e₂} ⊑□ q with diag □e e₂
...                              | kind□           = q
...                              | diff            = q
⊔e-preserves-⊑ ⊑* ⊑*                               = ⊑*
⊔e-preserves-⊑ ⊑Var ⊑Var                           = ⊑Var
⊔e-preserves-⊑ (⊑λ p₁ p₂) (⊑λ q₁ q₂)               = ⊑λ (⊔t-preserves-⊑ p₁ q₁) (⊔e-preserves-⊑ p₂ q₂)
⊔e-preserves-⊑ (⊑∘ p₁ p₂) (⊑∘ q₁ q₂)               = ⊑∘ (⊔e-preserves-⊑ p₁ q₁) (⊔e-preserves-⊑ p₂ q₂)
⊔e-preserves-⊑ (⊑& p₁ p₂) (⊑& q₁ q₂)               = ⊑& (⊔e-preserves-⊑ p₁ q₁) (⊔e-preserves-⊑ p₂ q₂)
⊔e-preserves-⊑ (⊑ιₗ p) (⊑ιₗ q)                     = ⊑ιₗ (⊔e-preserves-⊑ p q)
⊔e-preserves-⊑ (⊑ιᵣ p) (⊑ιᵣ q)                     = ⊑ιᵣ (⊔e-preserves-⊑ p q)
⊔e-preserves-⊑ (⊑Λ p) (⊑Λ q)                       = ⊑Λ (⊔e-preserves-⊑ p q)
⊔e-preserves-⊑ (⊑def p₁ p₂) (⊑def q₁ q₂)           = ⊑def (⊔e-preserves-⊑ p₁ q₁) (⊔e-preserves-⊑ p₂ q₂)
⊔e-preserves-⊑ {e₁} p ⊑□ rewrite ⊔e-identityᵣ e₁ = p

-- Upper bound lemmas (for slices sharing the same target)
⊔e-ub₁ : ∀ {e₁ e₂ e} → e₁ ⊑e e → e₂ ⊑e e → e₁ ⊑e e₁ ⊔e e₂
⊔e-ub₁ ⊑□ ⊑□                       = ⊑□
⊔e-ub₁ {e₂ = e₂} ⊑□ _ with diag □e e₂
...                      | kind□   = ⊑□
...                      | diff    = ⊑□
⊔e-ub₁ ⊑* ⊑*                       = ⊑*
⊔e-ub₁ ⊑Var ⊑Var                   = ⊑Var
⊔e-ub₁ (⊑λ p₁ p₂) (⊑λ q₁ q₂)       = ⊑λ (⊔t-ub₁ (⊑t-consistent p₁ q₁)) (⊔e-ub₁ p₂ q₂)
⊔e-ub₁ (⊑∘ p₁ p₂) (⊑∘ q₁ q₂)       = ⊑∘ (⊔e-ub₁ p₁ q₁) (⊔e-ub₁ p₂ q₂)
⊔e-ub₁ (⊑& p₁ p₂) (⊑& q₁ q₂)       = ⊑& (⊔e-ub₁ p₁ q₁) (⊔e-ub₁ p₂ q₂)
⊔e-ub₁ (⊑ιₗ p) (⊑ιₗ q)             = ⊑ιₗ (⊔e-ub₁ p q)
⊔e-ub₁ (⊑ιᵣ p) (⊑ιᵣ q)             = ⊑ιᵣ (⊔e-ub₁ p q)
⊔e-ub₁ (⊑Λ p) (⊑Λ q)               = ⊑Λ (⊔e-ub₁ p q)
⊔e-ub₁ (⊑def p₁ p₂) (⊑def q₁ q₂)   = ⊑def (⊔e-ub₁ p₁ q₁) (⊔e-ub₁ p₂ q₂)
⊔e-ub₁ {e₁} p ⊑□ rewrite ⊔e-identityᵣ e₁ = ⊑e-refl

⊔e-ub₂ : ∀ {e₁ e₂ e} → e₁ ⊑e e → e₂ ⊑e e → e₂ ⊑e e₁ ⊔e e₂
⊔e-ub₂ ⊑□ ⊑□                       = ⊑□
⊔e-ub₂ {e₂ = e₂} ⊑□ q with diag □e e₂
...                      | kind□   = ⊑□
...                      | diff    = ⊑e-refl
⊔e-ub₂ ⊑* ⊑*                       = ⊑*
⊔e-ub₂ ⊑Var ⊑Var                   = ⊑Var
⊔e-ub₂ (⊑λ p₁ p₂) (⊑λ q₁ q₂)       = ⊑λ (⊔t-ub₂ (⊑t-consistent p₁ q₁)) (⊔e-ub₂ p₂ q₂)
⊔e-ub₂ (⊑∘ p₁ p₂) (⊑∘ q₁ q₂)       = ⊑∘ (⊔e-ub₂ p₁ q₁) (⊔e-ub₂ p₂ q₂)
⊔e-ub₂ (⊑& p₁ p₂) (⊑& q₁ q₂)       = ⊑& (⊔e-ub₂ p₁ q₁) (⊔e-ub₂ p₂ q₂)
⊔e-ub₂ (⊑ιₗ p) (⊑ιₗ q)             = ⊑ιₗ (⊔e-ub₂ p q)
⊔e-ub₂ (⊑ιᵣ p) (⊑ιᵣ q)             = ⊑ιᵣ (⊔e-ub₂ p q)
⊔e-ub₂ (⊑Λ p) (⊑Λ q)               = ⊑Λ (⊔e-ub₂ p q)
⊔e-ub₂ (⊑def p₁ p₂) (⊑def q₁ q₂)   = ⊑def (⊔e-ub₂ p₁ q₁) (⊔e-ub₂ p₂ q₂)
⊔e-ub₂ {e₁} p ⊑□ rewrite ⊔e-identityᵣ e₁ = ⊑□

⊔e-lub : ∀ {e e₁ e₂ e'} → e₁ ⊑e e' → e₂ ⊑e e' → e₁ ⊑e e → e₂ ⊑e e → e₁ ⊔e e₂ ⊑e e
⊔e-lub _ _ p q = ⊔e-preserves-⊑ p q

-- Meets (of slices of some expression)
_⊓eₛ_ : ∀ {e} → ⌊ e ⌋ → ⌊ e ⌋ → ⌊ e ⌋
υ ⊓eₛ υ' = υ .↓ ⊓e υ' .↓ isSlice ⊓e-preserves-⊑-spec (υ .proof) (υ' .proof)

infixl 6 _⊓eₛ_

-- Joins (of slices of some expression)
_⊔eₛ_ : ∀ {e} → ⌊ e ⌋ → ⌊ e ⌋ → ⌊ e ⌋
υ ⊔eₛ υ' = υ .↓ ⊔e υ' .↓ isSlice ⊔e-preserves-⊑ (υ .proof) (υ' .proof)

infixl 7 _⊔eₛ_

-- Slice meet is lower bound
⊓eₛ-lb₁ : ∀ {e} (υ₁ υ₂ : ⌊ e ⌋) → υ₁ ⊓eₛ υ₂ ⊑eₛ υ₁
⊓eₛ-lb₁ υ₁ υ₂ = ⊓e-lb₁ (υ₁ .↓) (υ₂ .↓)

⊓eₛ-lb₂ : ∀ {e} (υ₁ υ₂ : ⌊ e ⌋) → υ₁ ⊓eₛ υ₂ ⊑eₛ υ₂
⊓eₛ-lb₂ υ₁ υ₂ = ⊓e-lb₂ (υ₁ .↓) (υ₂ .↓)

⊓eₛ-glb : ∀ {e} {υ υ₁ υ₂ : ⌊ e ⌋} → υ ⊑eₛ υ₁ → υ ⊑eₛ υ₂ → υ ⊑eₛ υ₁ ⊓eₛ υ₂
⊓eₛ-glb = ⊓e-glb

-- Slice join is upper bound
⊔eₛ-ub₁ : ∀ {e} (υ₁ υ₂ : ⌊ e ⌋) → υ₁ ⊑eₛ υ₁ ⊔eₛ υ₂
⊔eₛ-ub₁ υ₁ υ₂ = ⊔e-ub₁ (υ₁ .proof) (υ₂ .proof)

⊔eₛ-ub₂ : ∀ {e} (υ₁ υ₂ : ⌊ e ⌋) → υ₂ ⊑eₛ υ₁ ⊔eₛ υ₂
⊔eₛ-ub₂ υ₁ υ₂ = ⊔e-ub₂ (υ₁ .proof) (υ₂ .proof)

⊔eₛ-lub : ∀ {e} {υ υ₁ υ₂ : ⌊ e ⌋} → υ₁ ⊑eₛ υ → υ₂ ⊑eₛ υ → υ₁ ⊔eₛ υ₂ ⊑eₛ υ
⊔eₛ-lub {_} {υ} {υ₁} {υ₂} p q = ⊔e-lub (υ₁ .proof) (υ₂ .proof) p q

-- Slice infimum and supremum
⊓eₛ-infimum : ∀ {e} → Infimum (_⊑eₛ_ {e}) _⊓eₛ_
⊓eₛ-infimum υ₁ υ₂ = ⊓eₛ-lb₁ υ₁ υ₂ , ⊓eₛ-lb₂ υ₁ υ₂ , λ υ → ⊓eₛ-glb {υ = υ} {υ₁} {υ₂}

⊔eₛ-supremum : ∀ {e} → Supremum (_⊑eₛ_ {e}) _⊔eₛ_
⊔eₛ-supremum υ₁ υ₂ = ⊔eₛ-ub₁ υ₁ υ₂ , ⊔eₛ-ub₂ υ₁ υ₂ , λ υ → ⊔eₛ-lub {υ = υ} {υ₁} {υ₂}

-- Slice meet semilattice
⊓eₛ-isMeetSemilattice : ∀ {e} → IsMeetSemilattice (_≡_ on ↓) (_⊑eₛ_ {e}) _⊓eₛ_
⊓eₛ-isMeetSemilattice = record
  { isPartialOrder = ⊑eₛ-isPartialOrder
  ; infimum        = ⊓eₛ-infimum
  }

-- Slice join semilattice
⊔eₛ-isJoinSemilattice : ∀ {e} → IsJoinSemilattice (_≡_ on ↓) (_⊑eₛ_ {e}) _⊔eₛ_
⊔eₛ-isJoinSemilattice = record
  { isPartialOrder = ⊑eₛ-isPartialOrder
  ; supremum       = ⊔eₛ-supremum
  }

-- Full lattice on slices of an expression
⊑eₛ-isLattice : ∀ {e} → IsLattice (_≡_ on ↓) (_⊑eₛ_ {e}) _⊔eₛ_ _⊓eₛ_
⊑eₛ-isLattice = record
  { isPartialOrder = ⊑eₛ-isPartialOrder
  ; supremum       = ⊔eₛ-supremum
  ; infimum        = ⊓eₛ-infimum
  }

-- Bounded lattice: □e is bottom, e is top
⊤eₛ-maximum : ∀ {e} → Maximum (_⊑eₛ_ {e}) ⊤eₛ
⊤eₛ-maximum υ = υ .proof

⊥eₛ-minimum : ∀ {e} → Minimum (_⊑eₛ_ {e}) ⊥eₛ
⊥eₛ-minimum υ = ⊑□

-- Bounded lattice on slices of an expression
⊑eₛ-isBoundedLattice : ∀ {e} → IsBoundedLattice (_≡_ on ↓) (_⊑eₛ_ {e}) _⊔eₛ_ _⊓eₛ_ ⊤eₛ ⊥eₛ
⊑eₛ-isBoundedLattice = record
  { isLattice = ⊑eₛ-isLattice
  ; maximum   = ⊤eₛ-maximum
  ; minimum   = ⊥eₛ-minimum
  }
