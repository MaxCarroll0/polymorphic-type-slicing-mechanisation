{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Nat hiding (_+_; _⊔_)
open import Data.Unit
open import Agda.Builtin.FromNat
open import Data.Nat.Literals
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_; [])
open import Function using (case_of_)
open import Core
open import Semantics.Statics
open import Semantics.Graduality using (syn-unicity; static-gradual-syn)
open import Slicing.Synthesis.Synthesis
import Slicing.Synthesis.Synthesis as SS
open import Slicing.Synthesis.Decompositions
open import Slicing.Synthesis.FixedAssmsSynthesis as Fix

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

-- Counterexample 3: ψ of MinFixedAssmsSynSlice has no global minimum.
-- Case branches using different variables produce incomparable ψ values.
--
-- Γ = ((* ⇒ □) ⇒ *) , ((□ ⇒ *) ⇒ *) ⊢ case □ of 1 · 2 ⇒ (* ⇒ *) ⇒ *
-- υ = (□ ⇒ □) ⇒ □
-- s₁: case □ of 1 · □ ⇒ (* ⇒ □) ⇒ *    s₂: case □ of □ · 2 ⇒ (□ ⇒ *) ⇒ *
--
-- Consequence: we cannot pick a canonical minimal ψ to make the zone
-- iteration monotone (rules out ψ-monotonicity approach to case algorithm).
¬global-min-ψ-fixedassms
  : ¬ (∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ : ⌊ τ ⌋}
       → Σ[ s ∈ Fix.FixedAssmsSynSlice D υ ] IsMinimal s
         ∧ (∀ (t : Fix.FixedAssmsSynSlice D υ) → IsMinimal t → s .Fix.type ⊑ₛ t .Fix.type))

module global-min-ψ-counterexample where
  open Eq using (refl)

  Γ = ((* ⇒ □) ⇒ *) ∷ ((□ ⇒ *) ⇒ *) ∷ []

  D : 0 ； Γ ⊢ case □ of 1 · 2 ↦ (* ⇒ *) ⇒ *
  D = ↦case ↦□ refl (↦Var refl) (↦Var refl) (~⇒ (~⇒ ~?₁ ~?₂) ~*)

  υ : ⌊ (* ⇒ *) ⇒ * ⌋
  υ = ((□ ⇒ □) ⇒ □) isSlice (⊑⇒ (⊑⇒ ⊑□ ⊑□) ⊑□)

  -- s₁: branch 1 only, ψ₁ = (* ⇒ □) ⇒ *
  s₁ : Fix.FixedAssmsSynSlice D υ
  s₁ = ↑ (⊑case ⊑□ ⊑Var ⊑□)
     ⇑ ↑ (⊑⇒ (⊑⇒ ⊑* ⊑□) ⊑*)
     ∈ ↦case ↦□ refl (↦Var refl) ↦□ ~?₁
     ⊒ ⊑⇒ (⊑⇒ ⊑□ ⊑□) ⊑□

  min₁ : IsMinimal s₁
  min₁ t t⊑s₁ with t .Fix.expₛ .proof | t⊑s₁
  ... | ⊑□ | ⊑□ with t .Fix.syn | t .Fix.valid
  ...   | ↦□ | ()
  min₁ t t⊑s₁
      | ⊑case ⊑□ ⊑□ ⊑□ | ⊑case ⊑□ ⊑□ ⊑□ with t .Fix.syn | t .Fix.valid
  ...   | ↦case ↦□ _ ↦□ ↦□ _ | ()
  min₁ t t⊑s₁
      | ⊑case ⊑□ ⊑Var ⊑□ | ⊑case ⊑□ ⊑Var ⊑□ = refl

  -- s₂: branch 2 only, ψ₂ = (□ ⇒ *) ⇒ *
  s₂ : Fix.FixedAssmsSynSlice D υ
  s₂ = ↑ (⊑case ⊑□ ⊑□ ⊑Var)
     ⇑ ↑ (⊑⇒ (⊑⇒ ⊑□ ⊑*) ⊑*)
     ∈ ↦case ↦□ refl ↦□ (↦Var refl) ~?₂
     ⊒ ⊑⇒ (⊑⇒ ⊑□ ⊑□) ⊑□

  min₂ : IsMinimal s₂
  min₂ t t⊑s₂ with t .Fix.expₛ .proof | t⊑s₂
  ... | ⊑□ | ⊑□ with t .Fix.syn | t .Fix.valid
  ...   | ↦□ | ()
  min₂ t t⊑s₂
      | ⊑case ⊑□ ⊑□ ⊑□ | ⊑case ⊑□ ⊑□ ⊑□ with t .Fix.syn | t .Fix.valid
  ...   | ↦case ↦□ _ ↦□ ↦□ _ | ()
  min₂ t t⊑s₂
      | ⊑case ⊑□ ⊑□ ⊑Var | ⊑case ⊑□ ⊑□ ⊑Var = refl

  ψ₁⋢ψ₂ : s₁ .Fix.type .↓ ⊑ s₂ .Fix.type .↓ → Data.Empty.⊥
  ψ₁⋢ψ₂ (⊑⇒ (⊑⇒ () _) _)

  ψ₂⋢ψ₁ : s₂ .Fix.type .↓ ⊑ s₁ .Fix.type .↓ → Data.Empty.⊥
  ψ₂⋢ψ₁ (⊑⇒ (⊑⇒ _ ()) _)

¬global-min-ψ-fixedassms f =
  let open global-min-ψ-counterexample
      (s , min-s , ψ-min) = f {D = D} {υ = υ}
      s⊑ψ₁ = ψ-min s₁ min₁
      s⊑ψ₂ = ψ-min s₂ min₂
  in go s min-s s⊑ψ₁ s⊑ψ₂
  where
    open global-min-ψ-counterexample
    -- ψ₁ ⊓ ψ₂ = (□ ⇒ □) ⇒ * is unachievable: both vars overshoot in different args
    go : (s : Fix.FixedAssmsSynSlice D υ) → IsMinimal s
       → s .Fix.type .↓ ⊑ s₁ .Fix.type .↓
       → s .Fix.type .↓ ⊑ s₂ .Fix.type .↓
       → Data.Empty.⊥
    go s _ s⊑ψ₁ s⊑ψ₂ with s .Fix.expₛ .proof
    ... | ⊑□ with s .Fix.syn | s .Fix.valid
    ...   | ↦□ | ()
    go s _ s⊑ψ₁ s⊑ψ₂
        | ⊑case ⊑□ ⊑□ ⊑□ with s .Fix.syn | s .Fix.valid
    ...   | ↦case ↦□ _ ↦□ ↦□ _ | ()
    go s _ s⊑ψ₁ s⊑ψ₂
        | ⊑case ⊑□ ⊑Var ⊑□ with s .Fix.syn | s⊑ψ₂
    ...   | ↦case ↦□ _ (↦Var refl) ↦□ _ | ⊑⇒ (⊑⇒ () _) _
    go s _ s⊑ψ₁ s⊑ψ₂
        | ⊑case ⊑□ ⊑□ ⊑Var with s .Fix.syn | s⊑ψ₁
    ...   | ↦case ↦□ _ ↦□ (↦Var refl) _ | ⊑⇒ (⊑⇒ _ ()) _
    go s _ s⊑ψ₁ s⊑ψ₂
        | ⊑case ⊑□ ⊑Var ⊑Var with s .Fix.syn | s⊑ψ₂
    ...   | ↦case ↦□ _ (↦Var refl) (↦Var refl) _ | ⊑⇒ (⊑⇒ () _) _

-- Counterexample 4: Naive product of minimal sub-slices (via &syn) is NOT
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

-- Counterexample 5: MinSynSlice ⇏ MinFixedAssmsSynSlice.
-- Consequence: min syn slices purely slicing the expression
-- followed by slicing the context will not be complete
¬min-syn-is-min-fixedassms
  : ¬ (∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
       → ((m , _) : MinSynSlice D ◂ υ)
       → (f : FixedAssmsSynSlice D υ)
       → f .expₛ .↓ ⊑ SS._↓σ m
       → SS._↓σ m ⊑ f .Fix.expₛ .↓)

module min-syn-not-fixedassms-counterexample where
  open &syn-minimality-counterexample
  open Eq using (refl)

  f' : Fix.FixedAssmsSynSlice D₁ υ
  f' = record
    { expₛ = ↑ (⊑case ⊑□ ⊑Var ⊑□)
    ; type  = ⊤ₛ
    ; syn   = ↦case ↦□ refl (↦Var refl) ↦□ ~?₁
    ; valid = ⊑ₛ.refl {A = Typ} {x = ⊤ₛ}
    }

  f'⊑m₂ : f' .Fix.expₛ .↓ ⊑ SS._↓σ m₂
  f'⊑m₂ = ⊑case ⊑□ ⊑Var ⊑□

¬min-syn-is-min-fixedassms g
  with g (m₂ , min₂) f' f'⊑m₂
  where open min-syn-not-fixedassms-counterexample
        open &syn-minimality-counterexample
...  | ⊑case _ _ ()

-- Counterexample 6: MinFixedAssmsSynSlice is NOT upward-closed in the query.
-- Increasing the query can switch which branch matters, giving incomparable slices.
--
-- x : * × * ⊢ case □ of 1 · (* & □) ⇒ * × *
-- υ' = * × □: min slice case □ of □ · (* & □) ⇒ * × □
-- υ  = * × *: min slice case □ of 1 · □       ⇒ * × *   (incomparable)
--
-- Consequence: [co]-slice cannot lift case slices to larger queries.
¬upward-closure-min-fixedassms
  : ¬ (∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ' υ : ⌊ τ ⌋}
       → υ' ⊑ₛ υ
       → (s' : Fix.FixedAssmsSynSlice D υ') → IsMinimal s'
       → Σ[ s ∈ Fix.FixedAssmsSynSlice D υ ] IsMinimal s ∧ (s' .Fix.expₛ .↓ ⊑ s .Fix.expₛ .↓))

module upward-closure-counterexample where
  open Eq using (refl)

  D : 0 ； (* × *) ∷ [] ⊢ case □ of 1 · (* & □) ↦ * × *
  D = ↦case ↦□ refl (↦Var refl) (↦& ↦* ↦□) (~× ~* ~?₁)

  υ' : ⌊ * × * ⌋
  υ' = (* × □) isSlice (⊑× ⊑* ⊑□)

  υ : ⌊ * × * ⌋
  υ = ⊤ₛ

  υ'⊑υ : υ' ⊑ₛ υ
  υ'⊑υ = ⊑× ⊑* ⊑□

  s' : Fix.FixedAssmsSynSlice D υ'
  s' = ↑ (⊑case ⊑□ ⊑□ (⊑& ⊑* ⊑□))
     ⇑ ↑ (⊑× ⊑* ⊑□)
     ∈ ↦case ↦□ refl ↦□ (↦& ↦* ↦□) ~?₂
     ⊒ ⊑× ⊑* ⊑□

  min' : IsMinimal s'
  min' t t⊑s' with t .Fix.expₛ .proof | t⊑s'
  ... | ⊑□ | ⊑□ with t .Fix.syn | t .Fix.valid
  ...   | ↦□ | ()
  min' t t⊑s'
      | ⊑case ⊑□ ⊑□ ⊑□ | ⊑case ⊑□ ⊑□ ⊑□ with t .Fix.syn | t .Fix.valid
  ...   | ↦case ↦□ _ ↦□ ↦□ _ | ()
  min' t t⊑s'
      | ⊑case ⊑□ ⊑□ (⊑& ⊑□ ⊑□) | ⊑case ⊑□ ⊑□ (⊑& ⊑□ ⊑□) with t .Fix.syn | t .Fix.valid
  ...   | ↦case ↦□ _ ↦□ (↦& ↦□ ↦□) _ | ⊑× () _
  min' t t⊑s'
      | ⊑case ⊑□ ⊑□ (⊑& ⊑* ⊑□) | ⊑case ⊑□ ⊑□ (⊑& ⊑* ⊑□) = refl

  s : Fix.FixedAssmsSynSlice D υ
  s = ↑ (⊑case ⊑□ ⊑Var ⊑□)
    ⇑ ⊤ₛ
    ∈ ↦case ↦□ refl (↦Var refl) ↦□ ~?₁
    ⊒ ⊑× ⊑* ⊑*

  min-s : IsMinimal s
  min-s t t⊑s with t .Fix.expₛ .proof | t⊑s
  ... | ⊑□ | ⊑□ with t .Fix.syn | t .Fix.valid
  ...   | ↦□ | ()
  min-s t t⊑s
      | ⊑case ⊑□ ⊑□ ⊑□ | ⊑case ⊑□ ⊑□ ⊑□ with t .Fix.syn | t .Fix.valid
  ...   | ↦case ↦□ _ ↦□ ↦□ _ | ()
  min-s t t⊑s
      | ⊑case ⊑□ ⊑Var ⊑□ | ⊑case ⊑□ ⊑Var ⊑□ = refl

  -- branch 2 ⊑ (* & □) types ⊑ * × □ ⋢ * × *, so branch 1 must be var 1
  any-valid-⊒s : (t : Fix.FixedAssmsSynSlice D υ) → s .Fix.expₛ .↓ ⊑ t .Fix.expₛ .↓
  any-valid-⊒s t with t .Fix.expₛ .proof
  ... | ⊑□ with t .Fix.syn | t .Fix.valid
  ...   | ↦□ | ()
  any-valid-⊒s t | ⊑case ⊑□ ⊑□ ⊑□ with t .Fix.syn | t .Fix.valid
  ... | ↦case ↦□ _ ↦□ ↦□ _ | ()
  any-valid-⊒s t | ⊑case ⊑□ ⊑□ (⊑& ⊑□ ⊑□) with t .Fix.syn | t .Fix.valid
  ... | ↦case ↦□ _ ↦□ (↦& ↦□ ↦□) _ | ⊑× () _
  any-valid-⊒s t | ⊑case ⊑□ ⊑□ (⊑& ⊑* ⊑□) with t .Fix.syn | t .Fix.valid
  ... | ↦case ↦□ _ ↦□ (↦& ↦* ↦□) _ | ⊑× ⊑* ()
  any-valid-⊒s t | ⊑case ⊑□ ⊑Var ⊑□ = ⊑case ⊑□ ⊑Var ⊑□
  any-valid-⊒s t | ⊑case ⊑□ ⊑Var (⊑& _ _) = ⊑case ⊑□ ⊑Var ⊑□

¬upward-closure-min-fixedassms f =
  let open upward-closure-counterexample
      (t , min-t , s'⊑t) = f υ'⊑υ s' min'
      s⊑t : s .Fix.expₛ .↓ ⊑ t .Fix.expₛ .↓
      s⊑t = any-valid-⊒s t
      t≡s : t .Fix.expₛ .↓ ≡ s .Fix.expₛ .↓
      t≡s = min-t s s⊑t
      s'⊑s : s' .Fix.expₛ .↓ ⊑ s .Fix.expₛ .↓
      s'⊑s = Eq.subst (s' .Fix.expₛ .↓ ⊑_) t≡s s'⊑t
  in case s'⊑s of λ where
    (⊑case _ _ ())
