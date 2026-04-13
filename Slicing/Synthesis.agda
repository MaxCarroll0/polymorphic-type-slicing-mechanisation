open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsEquivalence; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; subst; cong; cong₂; sym; trans)
open Eq.≡-Reasoning
open import Data.Maybe using (just)
open import Data.List using (_∷_; [])
open import Core
open import Core.Typ.Base using (diag; kind□; kind*; kindVar; kind+; kind×; kind⇒; kind∀; diff; shallow-disequality)
open import Data.Empty using (⊥-elim)
open import Semantics.Statics
open import Semantics.Metatheory using (static-gradual-syn; syn-precision; static-gradual-ana)

module Slicing.Synthesis where

-- Synthesis slice: sliced assumptions and expression that still synthesize
-- a given type slice υ. Indexed by the original derivation D.
record SynSlice {n : ℕ} {Γ : Assms} {e : Exp} {τ : Typ}
                (D : n ； Γ ⊢ e ↦ τ) (υ : ⌊ τ ⌋) : Set where
  field
    γ     : ⌊ Γ ⌋
    σ     : ⌊ e ⌋
    valid : n ； γ .↓ ⊢ σ .↓ ↦ υ .↓
open SynSlice public

private
-- Precision polymorphic in υ
  _⊑syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂} →
             SynSlice D υ₁ → SynSlice D υ₂ → Set
  _⊑syn_ s₁ s₂ =
      s₁ .σ ⊑ₛ s₂ .σ
    ∧ s₁ .γ ⊑ₛ s₂ .γ

  _≈syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂} →
              SynSlice D υ₁ → SynSlice D υ₂ → Set
  _≈syn_ s₁ s₂ =
      s₁ .σ ≈ₛ s₂ .σ
    ∧ s₁ .γ ≈ₛ s₂ .γ

  _≈syn?_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → (s₁ s₂ : SynSlice D υ) → Relation.Nullary.Dec (s₁ ≈syn s₂)
  s₁ ≈syn? s₂ with s₁ .σ ≈ₛ? s₂ .σ | s₁ .γ ≈ₛ? s₂ .γ
  ...            | yes p          | yes q = yes (p , q)
  ...            | no ¬p          | _     = no λ where (p , _) → ¬p p
  ...            | _              | no ¬q = no λ where (_ , q) → ¬q q

  _⊑syn?_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → (s₁ s₂ : SynSlice D υ) → Relation.Nullary.Dec (s₁ ⊑syn s₂)
  s₁ ⊑syn? s₂ with s₁ .σ ⊑ₛ? s₂ .σ | s₁ .γ ⊑ₛ? s₂ .γ
  ...            | yes p          | yes q = yes (p , q)
  ...            | no ¬p          | _     = no λ where (p , _) → ¬p p
  ...            | _              | no ¬q = no λ where (_ , q) → ¬q q

  ⊑syn-isDecPartialOrder : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
                              IsDecPartialOrder (_≈syn_ {D = D} {υ₁ = υ} {υ₂ = υ}) _⊑syn_
  ⊑syn-isDecPartialOrder {Γ = Γ} {e = e} = record
                           { isPartialOrder = record
                                              { isPreorder = isPreorder
                                              ; antisym = λ (p₁ , q₁) (p₂ , q₂) → ⊑.antisym {Exp} p₁ p₂ , ⊑.antisym {Assms} q₁ q₂
                                              }
                           ; _≟_  = _≈syn?_
                           ; _≤?_ = _⊑syn?_ 
                           }
    where isPreorder = record
                       { isEquivalence = record
                           { refl  = λ {_} → refl , refl
                           ; sym   = λ where (refl , refl) → refl , refl
                           ; trans = λ where (refl , refl) (refl , refl) → refl , refl
                           }
                       ; reflexive  = λ where (refl , refl) → ⊑.refl {Exp} , ⊑.refl {Assms}
                       ; trans = λ (p₁ , q₁) (p₂ , q₂) → ⊑.trans {Exp} p₁ p₂ , ⊑.trans {Assms} q₁ q₂
                       }

instance
  synSlice-precision : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
                         HasPrecision (SynSlice D υ)
  synSlice-precision = record
    { _≈_               = _≈syn_
    ; _⊑_               = _⊑syn_
    ; isDecPartialOrder = ⊑syn-isDecPartialOrder
    }

⊥-syn : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} → SynSlice D ⊥ₛ
⊥-syn = record { γ = ⊥ₛ ; σ = ⊥ₛ ; valid = ↦□ }

⊤-syn : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) → SynSlice D ⊤ₛ
⊤-syn D = record { γ = ⊤ₛ ; σ = ⊤ₛ ; valid = D }

-- Minimality
IsMinimal : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} → SynSlice D υ → Set
IsMinimal {D = D} {υ = υ} s = ∀ (s' : SynSlice D υ) → s' ⊑syn s → s ⊑syn s'

MinSynSlice : ∀ {n Γ e τ} → (D : n ； Γ ⊢ e ↦ τ) → ⌊ τ ⌋ → Set
MinSynSlice D υ = Σ[ s ∈ SynSlice D υ ] IsMinimal s

-- Counterexample 1: without IsMinimal, same-type join closure is false.
-- ↦□ allows arbitrary γ, so joining pollutes the assumptions.
module ⊔-closure-counterexample where
  D' : 0 ； * ∷ [] ⊢ ⟨ 0 ⟩ ↦ *
  D' = ↦Var refl

  υ' : ⌊ Typ.* ⌋
  υ' = ⊥ₛ

  s₁' : SynSlice D' υ'
  s₁' = record { γ = ⊤ₛ ; σ = ⊥ₛ ; valid = ↦□ }

  s₂' : SynSlice D' υ'
  s₂' = record { γ = ⊥ₛ ; σ = ⊤ₛ ; valid = ↦Var refl }

  ¬⊔-valid : ¬ (0 ； (s₁' .γ ⊔ₛ s₂' .γ) .↓ ⊢ (s₁' .σ ⊔ₛ s₂' .σ) .↓ ↦ υ' .↓)
  ¬⊔-valid (↦Var ())

-- Counterexample 2: assuming minimality, EXACT join syn type
module ⊔-exact-counterexample where
  D-ce : 0 ； * ⇒ * ∷ [] ⊢ ⟨ 0 ⟩ & ⟨ 0 ⟩ ↦ (* ⇒ *) × (* ⇒ *)
  D-ce = ↦& (↦Var refl) (↦Var refl)

  υ₁-ce : ⌊ (* ⇒ *) × (* ⇒ *) ⌋
  υ₁-ce = □ × □ ⇒ * isSlice ⊑× ⊑□ (⊑⇒ ⊑□ ⊑*)

  s₁-ce : SynSlice D-ce υ₁-ce
  s₁-ce = record
    { γ = (Typ.□ ⇒ *) ∷ [] isSlice ⊑∷ (⊑⇒ ⊑□ ⊑*) ⊑[]
    ; σ = (Exp.□ & ⟨ 0 ⟩) isSlice ⊑& ⊑□ ⊑Var
    ; valid = ↦& ↦□ (↦Var refl)
    }

  -- s₁-ce is minimal: forced γ(0) = □ ⇒ * by ↦Var, forced σ by ⊑
  postulate min₁-ce : IsMinimal s₁-ce

  υ₂-ce : ⌊ (* ⇒ *) × (* ⇒ *) ⌋
  υ₂-ce = * ⇒ □ × □ isSlice ⊑× (⊑⇒ ⊑* ⊑□) ⊑□

  s₂-ce : SynSlice D-ce υ₂-ce
  s₂-ce = record
    { γ = * ⇒ □ ∷ [] isSlice ⊑∷ (⊑⇒ ⊑* ⊑□) ⊑[]
    ; σ = ⟨ 0 ⟩ & □ isSlice ⊑& ⊑Var ⊑□
    ; valid = ↦& (↦Var refl) ↦□
    }

  postulate min₂-ce : IsMinimal s₂-ce

  -- Joined context: (□ ⇒ *) ⊔ (* ⇒ □) = * ⇒ *
  -- Joined expression: (□ & ⟨0⟩) ⊔ (⟨0⟩ & □) = ⟨0⟩ & ⟨0⟩
  -- Expected type: (* ⇒ □) × (□ ⇒ *)
  -- Actual type: (* ⇒ *) × (* ⇒ *)  i.e. (more precise0
  check-joined-γ : (s₁-ce .γ ⊔ₛ s₂-ce .γ) .↓ ≡ (* ⇒ *) ∷ []
  check-joined-γ = refl

  check-expected : (υ₁-ce ⊔ₛ υ₂-ce) .↓ ≡ (* ⇒ Typ.□) × (Typ.□ ⇒ *)
  check-expected = refl

  actual : 0 ； (s₁-ce .γ ⊔ₛ s₂-ce .γ) .↓ ⊢ (s₁-ce .σ ⊔ₛ s₂-ce .σ) .↓ ↦ ((* ⇒ *) × (* ⇒ *))
  actual = ↦& (↦Var refl) (↦Var refl)

  types-differ : ((* ⇒ *) × (* ⇒ *)) ≢ ((* ⇒ Typ.□) × (Typ.□ ⇒ *))
  types-differ ()

private
  -- Type join idempotency TODO: move to Typ.Properties
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

  -- Transport ↦ τ to ↦ (τ ⊔ τ) and back
  idem-fix : ∀ {n Γ e τ} → n ； Γ ⊢ e ↦ (τ ⊔ τ) → n ； Γ ⊢ e ↦ τ
  idem-fix {τ = τ} v rewrite ⊔t-idem τ = v

  idem-unfix : ∀ {n Γ e τ} → n ； Γ ⊢ e ↦ τ → n ； Γ ⊢ e ↦ (τ ⊔ τ)
  idem-unfix {τ = τ} v rewrite ⊔t-idem τ = v


-- Operator: join two syn slices, producing a valid slice at some type
_⊔syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂}
  → SynSlice D υ₁ → SynSlice D υ₂
  → Σ[ υ' ∈ ⌊ τ ⌋ ] SynSlice D υ'
_⊔syn_ {D = D} s₁ s₂ =
  let γ⊔ = s₁ .γ ⊔ₛ s₂ .γ
      σ⊔ = s₁ .σ ⊔ₛ s₂ .σ
      (τ' , deriv , τ'⊑τ) = static-gradual-syn (γ⊔ .proof) (σ⊔ .proof) D
  in ↑ τ'⊑τ , record { γ = γ⊔ ; σ = σ⊔ ; valid = deriv }

-- Theorem 1: the join type is at least as precise as the join of the input types
⊔syn-upper
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂}
  → (s₁ : SynSlice D υ₁) → (s₂ : SynSlice D υ₂)
  → υ₁ ⊔ₛ υ₂ ⊑ₛ proj₁ (s₁ ⊔syn s₂)
⊔syn-upper {D = D} {υ₁} {υ₂} s₁ s₂ =
  let (υ' , s⊔) = s₁ ⊔syn s₂
      υ₁⊑ = syn-precision
               (⊑ₛLat.x⊑ₛx⊔ₛy (s₁ .γ) (s₂ .γ))
               (⊑ₛLat.x⊑ₛx⊔ₛy (s₁ .σ) (s₂ .σ))
               (s⊔ .valid) (s₁ .valid)
      υ₂⊑ = syn-precision
               (⊑ₛLat.y⊑ₛx⊔ₛy (s₁ .γ) (s₂ .γ))
               (⊑ₛLat.y⊑ₛx⊔ₛy (s₁ .σ) (s₂ .σ))
               (s⊔ .valid) (s₂ .valid)
  in ⊑ₛLat.⊔ₛ-least {x = υ₁} {y = υ₂} {z = υ'} υ₁⊑ υ₂⊑

open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Postulate 2: when joined minimal syn slices synthesise a strictly MORE precise
-- type than the join (υ ≉ υ₁ ⊔ υ₂), any strict sub-slice of the join synthesises
-- a LESS precise type than the join.
postulate
  ⊔syn-precise
    : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂}
    → (s₁ : SynSlice D υ₁) → IsMinimal s₁
    → (s₂ : SynSlice D υ₂) → IsMinimal s₂
    → let (υ' , s⊔) = s₁ ⊔syn s₂ in
      ¬ υ' ≈ₛ (υ₁ ⊔ₛ υ₂)
    → (∀ (υ'' : ⌊ τ ⌋) (s' : SynSlice D υ'')
       → ¬ (s' ≈syn s⊔)
       → s' ⊑syn s⊔
       → ¬ (υ₁ ⊔ₛ υ₂ ⊑ₛ υ''))

-- Theorem 3: minimal syn slices of the same type join to the same type
⊔syn-same
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
  → (s₁ s₂ : SynSlice D υ) → IsMinimal s₁ → IsMinimal s₂
  → proj₁ (s₁ ⊔syn s₂) ≈ₛ υ
⊔syn-same {D = D} {υ = υ} s₁ s₂ m₁ m₂
  with proj₁ (s₁ ⊔syn s₂) ≈ₛ? (υ ⊔ₛ υ)
...  | yes eq = trans eq (⊔t-idem (υ .↓))
...  | no neq
       = ⊥-elim (⊔syn-precise s₁ m₁ s₂ m₂ neq υ s₁ s₁≉s⊔ s₁⊑s⊔
                              (⊑.reflexive {Typ} (⊔t-idem (υ .↓))))
  where
  s₁⊑s⊔ : s₁ ⊑syn proj₂ (s₁ ⊔syn s₂)
  s₁⊑s⊔ = ⊑ₛLat.x⊑ₛx⊔ₛy (s₁ .σ) (s₂ .σ)
         , ⊑ₛLat.x⊑ₛx⊔ₛy (s₁ .γ) (s₂ .γ)
  s₁≉s⊔ : ¬ (s₁ ≈syn proj₂ (s₁ ⊔syn s₂))
  s₁≉s⊔ (σ≈ , γ≈) = neq (begin
    (proj₁ (s₁ ⊔syn s₂) .↓) ≡˘⟨ ⊑.antisym {Typ} υ⊑υ' υ'⊑υ ⟩
    (υ .↓)                  ≡˘⟨ ⊔t-idem (υ .↓) ⟩
    (υ .↓ ⊔ υ .↓)           ∎)
    where
    υ⊑υ' = syn-precision (⊑.reflexive {Assms} γ≈) (⊑.reflexive {Exp} σ≈)
              (proj₂ (s₁ ⊔syn s₂) .valid) (s₁ .valid)
    υ'⊑υ = syn-precision (⊑.reflexive {Assms} (sym γ≈)) (⊑.reflexive {Exp} (sym σ≈))
              (s₁ .valid) (proj₂ (s₁ ⊔syn s₂) .valid)

-- -- Postulate 4: Every derivation and type slice has a minimal SynSlice
-- -- TODO: Prove via classical methods using the fact that a bottom element exists
postulate
  minExists : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) υ
             → ∃[ m ] IsMinimal {D = D} {υ = υ} m

-- -- Postulate 5: Monotonicity: more precise type slice → more precise minimal slice
postulate
  mono : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂ : ⌊ τ ⌋}
         → υ₁ ⊑ₛ υ₂
         → (m₂ : SynSlice D υ₂) → IsMinimal m₂
         → Σ[ m₁ ∈ SynSlice D υ₁ ] IsMinimal m₁ ∧ m₁ ⊑syn m₂
