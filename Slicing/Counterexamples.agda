open import Data.Nat hiding (_+_; _⊔_)
open import Data.Unit
open import Agda.Builtin.FromNat
open import Data.Nat.Literals
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)
open import Data.List using (_∷_; [])
open import Core
open import Semantics.Statics
open import Semantics.Graduality using (syn-unicity)
open import Slicing.Synthesis.Synthesis

module Slicing.Counterexamples where

-- Counterexample 1: ⊔syn does not preserve exactness
-- ↦□ allows arbitrary γ, so joining pollutes the assumptions.
¬⊔syn-closed
  : ¬ (∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
         (s₁ s₂ : ExactSynSlice D ◂ υ)
       → (s₁ .proj₁ ⊔syn s₂ .proj₁) .type ⊑ₛ υ)

module ⊔-closure-counterexample where
  open Eq using (refl)
  D : 0 ； * ∷ [] ⊢ 0 ↦ *
  D = ↦Var refl

  υ : ⌊ Typ.* ⌋
  υ = ⊥ₛ

  s₁e : ExactSynSlice D ◂ υ
  s₁e = (⊤ₛ ,ₛ ⊥ₛ) ⇑ ⊥ₛ ∈! ↦□
  s₁ = s₁e .proj₁

  s₂e : ExactSynSlice D ◂ υ
  s₂e = (⊥ₛ ,ₛ ⊤ₛ) ⇑ ⊥ₛ ∈! ↦Var refl
  s₂ = s₂e .proj₁

  ϕ⊔ = (s₁ ⊔syn s₂) .type
  -- Both s₁ s₂ synthesise □ but their join synthesises *
  ⊔-closed-counterexample
    : ϕ⊔ ⋢ₛ υ
  ⊔-closed-counterexample = ⊑ₛ.⊐⇒⋢ {x = ϕ⊔} {υ}
                            (⊑ₛ.⊒∧≉⇒⊐ {x = ϕ⊔} {υ}
                              ⊑□
                              (begin-apartness
                                ϕ⊔ ≈⟨ syn-unicity ((s₁ ⊔syn s₂) .syn) D ⟩
                                ⊤ₛ #⟨ (λ ()) ⟩
                                υ ∎)
                              )
                            where open ≈ₛ

¬⊔syn-closed f =
  let open ⊔-closure-counterexample
      (⋢) = f s₁e s₂e
  in ⊔-closed-counterexample ⋢


-- Counterexample 2: Even with minimality, ⊔syn still
--                   does not always synthesise exactly υ₁ ⊔ₛ υ₂
¬⊔syn-preserves-join
  : ¬ (∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂}
        ((s₁ , _) : ExactSynSlice D ◂ υ₁) ((s₂ , _) : ExactSynSlice D ◂ υ₂)
      → IsMinimal s₁ → IsMinimal s₂
      → (s₁ ⊔syn s₂) .type ⊑ₛ υ₁ ⊔ₛ υ₂)
module ⊔-syn-preserves-join-counterexample where
  open Eq using (refl)

  D : 0 ； * ⇒ * ∷ [] ⊢ 0 & 0 ↦ (* ⇒ *) × (* ⇒ *)
  D = ↦& (↦Var refl) (↦Var refl)

  υ₁ : ⌊ (* ⇒ *) × (* ⇒ *) ⌋
  υ₁ = □ × (□ ⇒ *) isSlice ⊑× ⊑□ (⊑⇒ ⊑□ ⊑*)

  υ₂ : ⌊ (* ⇒ *) × (* ⇒ *) ⌋
  υ₂ = (* ⇒ □) × □ isSlice ⊑× (⊑⇒ ⊑* ⊑□) ⊑□

  s₁e : ExactSynSlice D ◂ υ₁
  s₁e = (↑ (⊑∷ (⊑⇒ ⊑□ ⊑*) ⊑[]) ,ₛ ↑ (⊑& ⊑□ ⊑Var))
        ⇑ υ₁ ∈! ↦& ↦□ (↦Var refl)
  s₁ = s₁e .proj₁

  s₂e : ExactSynSlice D ◂ υ₂
  s₂e = (↑ (⊑∷ (⊑⇒ ⊑* ⊑□) ⊑[]) ,ₛ ↑ (⊑& ⊑Var ⊑□))
        ⇑ υ₂ ∈! ↦& (↦Var refl) ↦□
  s₂ = s₂e .proj₁

  min₁ : IsMinimal s₁
  min₁ s' ρₛ'⊒ρₛ with s' .syn | s' .valid
  min₁ _ (⊑∷ (⊑⇒ ⊑□ ⊑*) ⊑[]  , ⊑& ⊑□ ⊑Var)
         | ↦& _ (↦Var refl)  | ⊑× _ (⊑⇒ _ _)
         = refl , refl
  min₂ : IsMinimal s₂
  min₂ s' ρₛ'⊒ρₛ with s' .syn | s' .valid
  min₂ _ (⊑∷ (⊑⇒ ⊑* ⊑□) ⊑[]  , ⊑& ⊑Var ⊑□)
         | ↦& (↦Var refl) _  | ⊑× (⊑⇒ _ _) _
         = refl , refl

  -- Joined context: (□ ⇒ *) ⊔ (* ⇒ □) = * ⇒ *
  -- Joined expression: (□ & ⟨0⟩) ⊔ (⟨0⟩ & □) = ⟨0⟩ & ⟨0⟩
  -- Expected type: (* ⇒ □) × (□ ⇒ *)
  -- Actual type: (* ⇒ *) × (* ⇒ *)  (more precise)
  check-expected : (υ₁ ⊔ₛ υ₂) .↓ ≡ (* ⇒ □) × (□ ⇒ *)
  check-expected = refl

  ϕ⊔ = (s₁ ⊔syn s₂) .type
  υ⊔ = υ₁ ⊔ₛ υ₂

  ⊔-syn-preserves-join-counterexample
    : ϕ⊔ ⊐ₛ υ⊔
  ⊔-syn-preserves-join-counterexample
    = ⊑ₛ.⊒∧≉⇒⊐ {x = ϕ⊔} {υ⊔} (⊑× (⊑⇒ ⊑* ⊑□) (⊑⇒ ⊑□ ⊑*)) λ ()

¬⊔syn-preserves-join f =
  let open ⊔-syn-preserves-join-counterexample
      ϕ⊔⊑υ⊔ = f s₁e s₂e min₁ min₂
  in ⊑ₛ.⊐⇒⋢ {x = ϕ⊔} {υ⊔} ⊔-syn-preserves-join-counterexample ϕ⊔⊑υ⊔

-- Counterexample 3 (informal): Product of min slices is NOT MINIMAL
-- D: x : * ⇒ *; y : * ⇒ * ⊢ x + y ⇑ * ⇒ *
-- x : * ⇒ □; y : □ ⇒ A ⊢ x + y ⇑ * ⇒ *
-- x : * ⇒ *; y : □ ⊢ x + □ ⇑ A ⇒ □
-- Product of min slices:
-- x : A ⇒ A; y : □ ⇒ A ⊢ (x + y, x + □) ⇑ * ⇒ * × * ⇒ *
-- is NOT MINIMAL!!
-- Naive join of context in constructing products from joins is bad!
