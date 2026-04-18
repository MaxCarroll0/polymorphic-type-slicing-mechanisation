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
open import Semantics.Graduality using (syn-unicity; static-gradual-syn)
open import Slicing.Synthesis.Synthesis
open import Slicing.Synthesis.Decompositions

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
    : ϕ⊔ ⋢ₛ υ
  ⊔-closed-counterexample = ⊑ₛ.⊐⇒⋢ {x = ϕ⊔} {υ}
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
      (⋢) = f s₁e s₂e
  in ⊔-closed-counterexample ⋢


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
  in ⊑ₛ.⊐⇒⋢ {x = ϕ⊔} {υ⊔} ⊔-syn-preserves-join-counterexample ϕ⊔⊑υ⊔

-- Counterexample 3: Naive product of minimal sub-slices (via &syn) is NOT
-- always minimal. Naive join of contexts over-approximates when
-- sub-slices use overlapping variables with incompatible precision.
-- However, the converse does hole (Decompositions.min-prod-decomposability)
¬&syn-preserves-minimality
  : ¬ (∀ {n Γ e₁ e₂ τ₁ τ₂} {D₁ : n ； Γ ⊢ e₁ ↦ τ₁} {D₂ : n ； Γ ⊢ e₂ ↦ τ₂}
          {υ₁ υ₂}
        → ((m₁ , _) : MinSynSlice D₁ ◂ υ₁) ((m₂ , _) : MinSynSlice D₂ ◂ υ₂)
        → IsMinimal (m₁ &syn m₂))
module &syn-minimality-counterexample where
  open Eq using (refl)

  Γ = (* ⇒ *) ∷ (* ⇒ *) ∷ []

  -- D₁ = D₂
  D₁ : 0 ； Γ ⊢ case □ of 1 · 2 ↦ * ⇒ *
  D₁ = ↦case ↦□ refl (↦Var refl) (↦Var refl) (~⇒ ~* ~*)
  D₂ = D₁

  υ : ⌊ * ⇒ * ⌋
  υ = ⊤ₛ

  -- m₁: uses only var 0 (via left branch)
  -- m₁ : * ⇒ * ∷ □ ⊢ case □ of 1 · □
  m₁ : SynSlice D₁ ◂ υ
  m₁ = (↑ (⊑∷ (⊑⇒ ⊑* ⊑*) (⊑∷ ⊑□ ⊑[])) ,ₛ ↑ (⊑case ⊑□ ⊑Var ⊑□))
       ⇑ ⊤ₛ ∈!₁ ↦case ↦□ refl (↦Var refl) ↦□ ~?₁

  -- m₂: uses both vars with components from each assumption
  -- m₂ : * ⇒ □ ∷ □ ⇒ * ⊢ case □ of 1 · 2
  m₂ : SynSlice D₂ ◂ υ
  m₂ = (↑ (⊑∷ (⊑⇒ ⊑* ⊑□) (⊑∷ (⊑⇒ ⊑□ ⊑*) ⊑[])) ,ₛ ↑ (⊑case ⊑□ ⊑Var ⊑Var))
       ⇑ ⊤ₛ ∈!₁ ↦case ↦□ refl (↦Var refl) (↦Var refl) (~⇒ ~?₁ ~?₂)

  min₁ : IsMinimal m₁
  min₁ s s⊑m₁                                        with s .syn                     | s .valid
  min₁ _ (_                         , ⊑□)               | ↦□                         | ()
  min₁ _ (_                         , ⊑case _  ⊑□ ⊑□)   | ↦case _ _ ↦□          ↦□ _ | ()
  min₁ _ (⊑∷ ⊑□         _           , ⊑case _  ⊑Var ⊑□) | ↦case _ _ (↦Var refl) ↦□ _ | ()
  min₁ _ (⊑∷ (⊑⇒ ⊑□ _)  _           , ⊑case _  ⊑Var ⊑□) | ↦case _ _ (↦Var refl) ↦□ _ | ⊑⇒ () _
  min₁ _ (⊑∷ (⊑⇒ _ ⊑□)  _           , ⊑case _  ⊑Var ⊑□) | ↦case _ _ (↦Var refl) ↦□ _ | ⊑⇒ _ ()
  min₁ _ (⊑∷ (⊑⇒ ⊑* ⊑*) (⊑∷ ⊑□ ⊑[]) , ⊑case ⊑□ ⊑Var ⊑□) | ↦case _ _ (↦Var refl) ↦□ _ | ⊑⇒ ⊑* ⊑* = refl , refl

  min₂ : IsMinimal m₂
  min₂ s s⊑m₂                                                  with s .syn                              | s .valid
  min₂ _ (_                                 , ⊑□)                 | ↦□                                  | ()
  min₂ _ (_                                 , ⊑case _  ⊑□   ⊑□)   | ↦case _ _ ↦□          ↦□ _          | ()
  min₂ _ (⊑∷ ⊑□ _                           , ⊑case _  ⊑Var ⊑□)   | ↦case _ _ (↦Var refl) ↦□ _          | ()
  min₂ _ (⊑∷ (⊑⇒ _ ⊑□)  _                   , ⊑case _  ⊑Var ⊑□)   | ↦case _ _ (↦Var refl) ↦□ _          | ⊑⇒ _ ()
  min₂ _ (⊑∷ _          (⊑∷ ⊑□         _)   , ⊑case _  ⊑□   ⊑Var) | ↦case _ _ ↦□          (↦Var refl) _ | ()
  min₂ _ (⊑∷ _          (⊑∷ (⊑⇒ ⊑□ _)  _)   , ⊑case _  ⊑□   ⊑Var) | ↦case _ _ ↦□          (↦Var refl) _ | ⊑⇒ () _
  min₂ _ (⊑∷ (⊑⇒ _  ⊑□) (⊑∷ ⊑□         ⊑[]) , ⊑case ⊑□ ⊑Var ⊑Var) | ↦case _ _ (↦Var refl) (↦Var refl) _ | ⊑⇒ _ ()
  min₂ _ (⊑∷ ⊑□         (⊑∷ (⊑⇒ ⊑□ _)  ⊑[]) , ⊑case ⊑□ ⊑Var ⊑Var) | ↦case _ _ (↦Var refl) (↦Var refl) _ | ⊑⇒ () _
  min₂ _ (⊑∷ (⊑⇒ ⊑* ⊑□) (⊑∷ (⊑⇒ ⊑□ ⊑*) ⊑[]) , ⊑case ⊑□ ⊑Var ⊑Var) | ↦case _ _ (↦Var refl) (↦Var refl) _ | ⊑⇒ ⊑* ⊑* = refl , refl

  -- naive product join: m₁ &syn m₂:
  -- (* ⇒ *) ∷ (□ ⇒ *) ∷ [] ⊢ (case □ of 1 · □) & (case □ of 1 · 2)
  m⊔ = m₁ &syn m₂

  -- Has strict sub-slice m': slicing ⟨2⟩ (the second case branch)
  -- Yet the result is still valid (ϕ ⊒ (* ⇒ *) × (* ⇒ *))
  m' : SynSlice (↦& D₁ D₂) ◂ (υ ×ₛ υ)
  m' = (↑ (⊑∷ (⊑⇒ ⊑* ⊑*) (⊑∷ ⊑□ ⊑[])) ,ₛ ↑ (⊑& (⊑case ⊑□ ⊑Var ⊑□) (⊑case ⊑□ ⊑Var ⊑□)))
       ⇑ ⊤ₛ ∈!₁ ↦& (↦case ↦□ refl (↦Var refl) ↦□ ~?₁) (↦case ↦□ refl (↦Var refl) ↦□ ~?₁)

¬&syn-preserves-minimality f
  with (min⊔ m' (⊑∷ (⊑⇒ ⊑* ⊑*) (⊑∷ ⊑□ ⊑[]) , ⊑& (⊑case ⊑□ ⊑Var ⊑□) (⊑case ⊑□ ⊑Var ⊑□)))
  where open &syn-minimality-counterexample
        min⊔ = f (m₁ , min₁) (m₂ , min₂)
...  | ()
