open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsEquivalence; IsDecEquivalence)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; subst; cong; cong₂; sym; trans)
open Eq.≡-Reasoning
open import Data.Maybe using (just)
open import Data.List using (_∷_; [])
open import Function using (_on_)
open import Core hiding (_×_)
open import Data.Empty using (⊥-elim)
open import Semantics.Statics
open import Semantics.Metatheory using (static-gradual-syn; syn-precision; static-gradual-ana)

module Slicing.Synthesis where

instance
  prog-slice-precision : HasPrecision (Assms ∧ Exp)
  prog-slice-precision = prod-precision

record SynSlice {n : ℕ} {Γ : Assms} {e : Exp} {τ : Typ}
                (D : n ； Γ ⊢ e ↦ τ) (υ : ⌊ τ ⌋) : Set where
  constructor _isSynSlice_
  field
    progₛ : ⌊ Γ , e ⌋
    valid  : n ； progₛ .↓ .proj₁ ⊢ progₛ .↓ .proj₂ ↦ υ .↓
open SynSlice public
infix 2 _isSynSlice_

prog : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} → SynSlice D υ → Assms ∧ Exp
prog s = s .progₛ .↓

prog⊑ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
        → (s : SynSlice D υ) → prog s ⊑ (Γ , e)
prog⊑ s = s .progₛ .proof

_↓γ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} → SynSlice D υ → Assms
_↓γ s = prog s .proj₁

_↓σ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} → SynSlice D υ → Exp
_↓σ s = prog s .proj₂

instance
  syn-slice-precision : ∀ {n Γ e τ υ} {D : n ； Γ ⊢ e ↦ τ} → HasPrecision (SynSlice D υ)
  syn-slice-precision = record
    { _≈_               = _≈_ on prog
    ; _⊑_               = _⊑_ on prog
    ; isDecPartialOrder = On.isDecPartialOrder prog (HasPrecision.isDecPartialOrder prog-slice-precision)
    }


⊥-syn : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} → SynSlice D ⊥ₛ
⊥-syn = record { progₛ = ⊥ₛ ; valid = ↦□ }

⊤-syn : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) → SynSlice D ⊤ₛ
⊤-syn D = record { progₛ = ⊤ₛ ; valid = D }

-- Minimality
IsMinimal : ∀ {A} ⦃ hp : HasPrecision A ⦄ (a : A) → Set
IsMinimal {A} a = ∀ (a' : A) → a' ⊑ a → a ≈ a'

MinSynSlice : ∀ {n Γ e τ} → (D : n ； Γ ⊢ e ↦ τ) → ⌊ τ ⌋ → Set
MinSynSlice D υ = Σ[ s ∈ SynSlice D υ ] IsMinimal s

_⊔syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ υ'}
         → SynSlice D υ → SynSlice D υ' → ⌊ Γ , e ⌋
_⊔syn_ s₁ s₂ = progₛ s₁ ⊔ₛ progₛ s₂

-- Counterexample 1: without IsMinimal, same-type join closure is false.
-- ↦□ allows arbitrary γ, so joining pollutes the assumptions.
module ⊔-closure-counterexample where
  D : 0 ； * ∷ [] ⊢ ⟨ 0 ⟩ ↦ *
  D = ↦Var refl

  υ : ⌊ Typ.* ⌋
  υ = ⊥ₛ

  s₁ : SynSlice D υ
  s₁ = ⊤ₛ ,ₛ ⊥ₛ isSynSlice ↦□

  s₂ : SynSlice D υ
  s₂ = ⊥ₛ ,ₛ ⊤ₛ isSynSlice ↦Var refl

  -- Both s₁ s₂ synthesise □ but their join synthesises *
  ⊔-closed-counterexample
    : ¬ (0 ； fstₛ (s₁ ⊔syn s₂) .↓ ⊢ sndₛ (s₁ ⊔syn s₂) .↓ ↦ υ .↓)
  ⊔-closed-counterexample (↦Var ())

-- ⊔syn does not always produce a result of type SynSlice D υ
¬⊔syn-closed
  : ¬ (∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
        (s₁ s₂ : SynSlice D υ)
      → Σ[ s ∈ SynSlice D υ ] prog s ≡ (s₁ ⊔syn s₂) .↓)
¬⊔syn-closed f =
  let open ⊔-closure-counterexample
      (s , eq) = f s₁ s₂
  in ⊔-closed-counterexample
       (subst (λ p → 0 ； proj₁ p ⊢ proj₂ p ↦ υ .↓) eq (valid s))

-- Counterexample 2: even with minimality, join does not synthesise the exact
-- join of the output types
module ⊔-syn-preserves-join-counterexample where
  D : 0 ； * ⇒ * ∷ [] ⊢ ⟨ 0 ⟩ & ⟨ 0 ⟩ ↦ (* ⇒ *) Typ.× (* ⇒ *)
  D = ↦& (↦Var refl) (↦Var refl)

  υ₁ : ⌊ (* ⇒ *) Typ.× (* ⇒ *) ⌋
  υ₁ = Typ.□ Typ.× (Typ.□ ⇒ *) isSlice ⊑× ⊑□ (⊑⇒ ⊑□ ⊑*)

  υ₂ : ⌊ (* ⇒ *) Typ.× (* ⇒ *) ⌋
  υ₂ = (* ⇒ Typ.□) Typ.× Typ.□ isSlice ⊑× (⊑⇒ ⊑* ⊑□) ⊑□

  s₁ : SynSlice D υ₁
  s₁ = ↑ (⊑∷ (⊑⇒ ⊑□ ⊑*) ⊑[]) ,ₛ ↑ (⊑& ⊑□ ⊑Var)
       isSynSlice ↦& ↦□ (↦Var refl)

  s₂ : SynSlice D υ₂
  s₂ = ↑ (⊑∷ (⊑⇒ ⊑* ⊑□) ⊑[]) ,ₛ ↑ (⊑& ⊑Var ⊑□)
       isSynSlice ↦& (↦Var refl) ↦□

  -- TODO, obvious
  postulate min₁ : IsMinimal s₁
  postulate min₂ : IsMinimal s₂

  -- Joined context: (□ ⇒ *) ⊔ (* ⇒ □) = * ⇒ *
  -- Joined expression: (□ & ⟨0⟩) ⊔ (⟨0⟩ & □) = ⟨0⟩ & ⟨0⟩
  -- Expected type: (* ⇒ □) × (□ ⇒ *)
  -- Actual type: (* ⇒ *) × (* ⇒ *)  (more precise)
  check-expected : (υ₁ ⊔ₛ υ₂) .↓ ≡ (* ⇒ Typ.□) Typ.× (Typ.□ ⇒ *)
  check-expected = refl

  ⊔-syn-preserves-join-counterexample
    : ¬ (0 ； fstₛ (s₁ ⊔syn s₂) .↓ ⊢ sndₛ (s₁ ⊔syn s₂) .↓ ↦ (υ₁ ⊔ₛ υ₂) .↓)
  ⊔-syn-preserves-join-counterexample (↦& (↦Var ()) _)

-- Even with minimality, ⊔syn does not always synthesise υ₁ ⊔ₛ υ₂
¬⊔syn-preserves-join
  : ¬ (∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂}
        (s₁ : SynSlice D υ₁) (s₂ : SynSlice D υ₂)
      → IsMinimal s₁ → IsMinimal s₂
      → Σ[ s ∈ SynSlice D (υ₁ ⊔ₛ υ₂) ] prog s ≡ (s₁ ⊔syn s₂) .↓)
¬⊔syn-preserves-join f =
  let open ⊔-syn-preserves-join-counterexample
      (s , eq) = f s₁ s₂ min₁ min₂
  in ⊔-syn-preserves-join-counterexample
       (subst (λ p → 0 ； proj₁ p ⊢ proj₂ p ↦ (υ₁ ⊔ₛ υ₂) .↓) eq (valid s))

-- By graduality we do know that it does synthesise some type slice of τ
_⊔syn'_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂}
          → SynSlice D υ₁ → SynSlice D υ₂
          → Σ[ υ' ∈ ⌊ τ ⌋ ] SynSlice D υ'
_⊔syn'_ {D = D} s₁ s₂ =
  let (τ' , deriv , τ'⊑τ) = static-gradual-syn
                          (fstₛ (s₁ ⊔syn s₂) .proof)
                          (sndₛ (s₁ ⊔syn s₂) .proof)
                          D
  in ↑ τ'⊑τ , (s₁ ⊔syn s₂ isSynSlice deriv)

-- -- Theorem 1: the join type is at least as precise as the join of the input types
-- ⊔syn-upper
--   : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂}
--   → (s₁ : SynSlice D υ₁) → (s₂ : SynSlice D υ₂)
--   → υ₁ ⊔ₛ υ₂ ⊑ₛ proj₁ (s₁ ⊔syn s₂)
-- ⊔syn-upper {D = D} {υ₁} {υ₂} s₁ s₂ =
--   let (υ' , s⊔) = s₁ ⊔syn s₂
--       υ₁⊑ = syn-precision
--                (⊑ₛLat.x⊑ₛx⊔ₛy (s₁ .γ) (s₂ .γ))
--                (⊑ₛLat.x⊑ₛx⊔ₛy (s₁ .σ) (s₂ .σ))
--                (s⊔ .valid) (s₁ .valid)
--       υ₂⊑ = syn-precision
--                (⊑ₛLat.y⊑ₛx⊔ₛy (s₁ .γ) (s₂ .γ))
--                (⊑ₛLat.y⊑ₛx⊔ₛy (s₁ .σ) (s₂ .σ))
--                (s⊔ .valid) (s₂ .valid)
--   in ⊑ₛLat.⊔ₛ-least {x = υ₁} {y = υ₂} {z = υ'} υ₁⊑ υ₂⊑

-- open import Data.Sum using (_⊎_; inj₁; inj₂)

-- -- Theorem 2: when joined minimal syn slices synthesise a strictly MORE precise
-- -- type than the join (υ ≉ υ₁ ⊔ υ₂), any strict sub-slice of the join synthesises
-- -- a LESS precise type than the join.
-- -- Proof by induction on D, pattern matching on s₁.valid and s₂.valid.
-- postulate
--   ⊔syn-precise
--     : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂}
--     → (s₁ : SynSlice D υ₁) → IsMinimal s₁
--     → (s₂ : SynSlice D υ₂) → IsMinimal s₂
--     → let (υ' , s⊔) = s₁ ⊔syn s₂ in
--       υ' ⊐ₛ υ₁ ⊔ₛ υ₂
--     → (∀ (υ'' : ⌊ τ ⌋) (s' : SynSlice D υ'')
--       → s' ⊑syn s⊔ → ¬ (s' ≈syn s⊔)
--       → υ'' ⊏ₛ υ₁ ⊔ₛ υ₂)


-- -- Theorem 3: minimal syn slices of the same type join to the same type
-- -- ⊔syn-same
-- --   : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
-- --   → (s₁ s₂ : SynSlice D υ) → IsMinimal s₁ → IsMinimal s₂
-- --   → proj₁ (s₁ ⊔syn s₂) ≈ₛ υ
-- -- ⊔syn-same {D = D} {υ = υ} s₁ s₂ m₁ m₂
-- --   with proj₁ (s₁ ⊔syn s₂) ≈ₛ? (υ ⊔ₛ υ)
-- -- ...  | yes eq = trans eq (⊔t-idem (υ .↓))
-- -- ...  | no neq
-- --        = ⊥-elim (⊔syn-precise s₁ m₁ s₂ m₂ neq υ s₁ s₁≉s⊔ s₁⊑s⊔
-- --                               (⊑.reflexive {Typ} (⊔t-idem (υ .↓))))
-- --   where
-- --   s₁⊑s⊔ : s₁ ⊑syn proj₂ (s₁ ⊔syn s₂)
-- --   s₁⊑s⊔ = ⊑ₛLat.x⊑ₛx⊔ₛy (s₁ .σ) (s₂ .σ)
-- --          , ⊑ₛLat.x⊑ₛx⊔ₛy (s₁ .γ) (s₂ .γ)
-- --   s₁≉s⊔ : ¬ (s₁ ≈syn proj₂ (s₁ ⊔syn s₂))
-- --   s₁≉s⊔ (σ≈ , γ≈) = neq (begin
-- --     (proj₁ (s₁ ⊔syn s₂) .↓) ≡˘⟨ ⊑.antisym {Typ} υ⊑υ' υ'⊑υ ⟩
-- --     (υ .↓)                  ≡˘⟨ ⊔t-idem (υ .↓) ⟩
-- --     (υ .↓ ⊔ υ .↓)           ∎)
-- --     where
-- --     υ⊑υ' = syn-precision (⊑.reflexive {Assms} γ≈) (⊑.reflexive {Exp} σ≈)
-- --               (proj₂ (s₁ ⊔syn s₂) .valid) (s₁ .valid)
-- --     υ'⊑υ = syn-precision (⊑.reflexive {Assms} (sym γ≈)) (⊑.reflexive {Exp} (sym σ≈))
-- --               (s₁ .valid) (proj₂ (s₁ ⊔syn s₂) .valid)

-- -- -- -- Postulate 4: Every derivation and type slice has a minimal SynSlice
-- -- -- -- TODO: Prove via classical methods using the fact that a bottom element exists
-- -- postulate
-- --   minExists : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) υ
-- --              → ∃[ m ] IsMinimal {D = D} {υ = υ} m

-- -- -- -- Postulate 5: Monotonicity: more precise type slice → more precise minimal slice
-- -- postulate
-- --   mono : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂ : ⌊ τ ⌋}
-- --          → υ₁ ⊑ₛ υ₂
-- --          → (m₂ : SynSlice D υ₂) → IsMinimal m₂
-- --          → Σ[ m₁ ∈ SynSlice D υ₁ ] IsMinimal m₁ ∧ m₁ ⊑syn m₂
