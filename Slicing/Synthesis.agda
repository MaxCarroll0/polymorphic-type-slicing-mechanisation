open import Data.Nat hiding (_+_; _⊔_)
open import Data.Unit
open import Agda.Builtin.FromNat
open import Data.Nat.Literals
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsEquivalence; IsDecEquivalence)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; subst; cong; cong₂)
open import Data.Maybe using (just)
open import Data.List using (_∷_; [])
open import Function using (_on_)
open import Core hiding (_×_)
open import Data.Empty using (⊥-elim)
open import Semantics.Statics
open import Semantics.Graduality using (static-gradual-syn; syn-precision; static-gradual-ana; syn-unicity)
module Slicing.Synthesis where

instance
  prog-slice-precision : HasPrecision (Assms ∧ Exp)
  prog-slice-precision = prod-precision

-- A SynSlice of D on υ is a program slice which synthesises a type larger than υ
-- Here υ is the 'query' and the slice provides enough information to explain the query: υ ⊑ type
record SynSlice_◂_ {n : ℕ} {Γ : Assms} {e : Exp} {τ : Typ}
                (D : n ； Γ ⊢ e ↦ τ) (υ : ⌊ τ ⌋) : Set where
  constructor _⇑_∈_⊒_
  field
    progₛ  : ⌊ Γ , e ⌋
    type  : ⌊ τ ⌋
    syn   : n ； progₛ .↓ .proj₁ ⊢ progₛ .↓ .proj₂ ↦ type .↓
    valid : υ ⊑ₛ type

  ↓ρ = progₛ .↓
  ↓ρₛ = progₛ
  ↓ρ⊑ = ↓ρₛ .proof

  ↓γ = ↓ρ .proj₁
  ↓γₛ = fstₛ ↓ρₛ
  ↓γ⊑ = fstₛ ↓ρₛ .proof

  ↓σ = ↓ρ .proj₂
  ↓σₛ = sndₛ ↓ρₛ
  ↓σ⊑ = sndₛ ↓ρₛ .proof

  ↓ϕ = type .↓
  ↓ϕₛ = type
  ↓ϕ⊑ = type .proof
open SynSlice_◂_ public
  renaming ( ↓ρ to _↓ρ; ↓ρₛ to _↓ρₛ; ↓ρ⊑ to _↓ρ⊑
           ; ↓ϕ to _↓ϕ; ↓ϕₛ to _↓ϕₛ; ↓ϕ⊑ to _↓ϕ⊑
           ; ↓γ to _↓γ; ↓γₛ to _↓γₛ; ↓σ to _↓σ
           ; ↓σₛ to _↓σₛ; ↓γ⊑ to _↓γ⊑; ↓σ⊑ to ↓σ⊑)
infix 10 SynSlice_◂_
infix 10 _⇑_∈_⊒_

-- Sometimes the slice is exact, explaining exactly the queried parts of the type
ExactSynSlice_◂_ : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) (υ : ⌊ τ ⌋) → Set
ExactSynSlice_◂_ D υ = Σ[ s ∈ SynSlice D ◂ υ ] s .type ⊑ₛ υ

exact : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} (s : SynSlice D ◂ υ) → {p : s .type ⊑ₛ υ} → ExactSynSlice D ◂ υ
exact s {p} = s , p
 

-- TODO: lift typing rules to slices for ease of use
_⇑_∈!_ : ∀ {n : ℕ} {Γ : Assms} {e : Exp} {τ : Typ}
           {D : n ； Γ ⊢ e ↦ τ} (ρₛ : ⌊ Γ , e ⌋) (υ : ⌊ τ ⌋)
           (d : n ； fstₛ ρₛ .↓ ⊢ sndₛ ρₛ .↓ ↦ υ .↓) → ExactSynSlice D ◂ υ
_⇑_∈!_ {τ = τ} ρₛ υ d = ρₛ ⇑ υ ∈ d ⊒ ⊑ₛ.refl {x = υ} , ⊑ₛ.refl {x = υ}

_⇑_∈!₁_ : ∀ {n : ℕ} {Γ : Assms} {e : Exp} {τ : Typ}
           {D : n ； Γ ⊢ e ↦ τ} (ρₛ : ⌊ Γ , e ⌋) (υ : ⌊ τ ⌋)
           (d : n ； fstₛ ρₛ .↓ ⊢ sndₛ ρₛ .↓ ↦ υ .↓) → SynSlice D ◂ υ
_⇑_∈!₁_ ρₛ υ d = (ρₛ ⇑ υ ∈! d) .proj₁

instance
  syn-slice-precision : ∀ {n Γ e τ υ} {D : n ； Γ ⊢ e ↦ τ} → HasPrecision (SynSlice D ◂ υ)
  syn-slice-precision = record
    { _≈_               = _≈_ on _↓ρ
    ; _⊑_               = _⊑_ on _↓ρ
    ; isDecPartialOrder = On.isDecPartialOrder _↓ρ (HasPrecision.isDecPartialOrder prog-slice-precision)
    }


⊥-syn : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} → SynSlice D ◂ ⊥ₛ
⊥-syn = ⊥ₛ ⇑ ⊥ₛ ∈ ↦□ ⊒ ⊑□

⊤-syn : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) → SynSlice D ◂ ⊤ₛ
⊤-syn D = (⊤ₛ ⇑ ⊤ₛ ∈! D) .proj₁

-- Minimality
IsMinimal : ∀ {A} ⦃ hp : HasPrecision A ⦄ (a : A) → Set
IsMinimal {A} a = ∀ (a' : A) → a' ⊑ a → a ≈ a'

IsMinSynSlice : ∀ {n Γ e τ} → (D : n ； Γ ⊢ e ↦ τ) → ⌊ τ ⌋ → Set
IsMinSynSlice D υ = Σ[ s ∈ SynSlice D ◂ υ ] IsMinimal s


-- Theorem 1: By using graduality we can construct a joined derivation
--            This join must synthesise a more or equally specific type
--            Hence, it is a valid SynSlice 

static-gradual-syn-prog -- (simple helpers)
  : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ}
    → (ρₛ : ⌊ Γ , e ⌋)
    → Σ[ ϕ ∈ ⌊ τ ⌋ ] n ； fstₛ ρₛ .↓ ⊢ sndₛ ρₛ .↓ ↦ ϕ .↓
static-gradual-syn-prog {D = D} ρₛ 
  with static-gradual-syn ((fstₛ ρₛ) .proof) ((sndₛ ρₛ) .proof) D
...  | ϕt , (d , ϕt⊑τ) = ↑ ϕt⊑τ , d

syn-precision-prog -- (simple helpers)
  : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ)
    → (ρₛ : ⌊ Γ , e ⌋) → ∀ {υ}
    → _
    → υ ⊑ τ
syn-precision-prog D ρₛ 
  = syn-precision ((fstₛ ρₛ) .proof) ((sndₛ ρₛ) .proof) D

_⊔syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂}
         → SynSlice D ◂ υ₁ → SynSlice D ◂ υ₂ → SynSlice D ◂ υ₁ ⊔ₛ υ₂
_⊔syn_ {τ = τ} {D = D} {υ₁} {υ₂}
       s₁@(ρₛ₁ ⇑ ϕ₁ ∈ d₁ ⊒ υ₁⊑ϕ₁) s₂@(ρₛ₂ ⇑ ϕ₂ ∈ d₂ ⊒ υ₂⊑ϕ₂)
  with static-gradual-syn-prog {D = D} (ρₛ₁ ⊔ₛ ρₛ₂) in eq
...  | ϕ⊔ , d⊔ = ρₛ₁ ⊔ₛ ρₛ₂ ⇑ ϕ⊔ ∈ d⊔ ⊒ υ⊔⊑ϕ⊔
                 where open ⊑ₛ {a = τ}
                       open ⊑ₛLat {a = τ}
                       υ₁⊑ϕ⊔ = begin υ₁ ⊑⟨ υ₁⊑ϕ₁ ⟩
                                     ϕ₁ ⊑⟨ syn-precision-prog d⊔
                                           (↑ (⊑ₛLat.x⊑ₛx⊔ₛy ρₛ₁ ρₛ₂)) d₁ ⟩
                                     ϕ⊔ ∎
                       υ₂⊑ϕ⊔ = begin υ₂ ⊑⟨ υ₂⊑ϕ₂ ⟩
                                     ϕ₂ ⊑⟨ syn-precision-prog d⊔
                                           (↑ (⊑ₛLat.y⊑ₛx⊔ₛy ρₛ₁ ρₛ₂)) d₂ ⟩
                                     ϕ⊔ ∎
                       υ⊔⊑ϕ⊔ = ⊔ₛ-least {υ₁} {υ₂} {ϕ⊔}
                                        υ₁⊑ϕ⊔ υ₂⊑ϕ⊔

-- TODO: lift to lattice

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
  min₁ _ (⊑∷ (⊑⇒ ⊑□ ⊑*) ⊑[] , ⊑& ⊑□ ⊑Var)
         | ↦& _ (↦Var refl) | ⊑× _ (⊑⇒ _ _)
         = refl , refl
  min₂ : IsMinimal s₂
  min₂ s' ρₛ'⊒ρₛ with s' .syn | s' .valid
  min₂ _ (⊑∷ (⊑⇒ ⊑* ⊑□) ⊑[] , ⊑& ⊑Var ⊑□)
         | ↦& (↦Var refl) _ | ⊑× (⊑⇒ _ _) _
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

-- -- By graduality we do know that it does synthesise some type slice of τ
-- _⊔syn'_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂}
--           → SynSlice D υ₁ → SynSlice D υ₂
--           → Σ[ υ' ∈ ⌊ τ ⌋ ] SynSlice D υ'
-- _⊔syn'_ {D = D} s₁ s₂ =
--   let (τ' , deriv , τ'⊑τ) = static-gradual-syn
--                           (fstₛ (s₁ ⊔syn s₂) .proof)
--                           (sndₛ (s₁ ⊔syn s₂) .proof)
--                           D
--   in ↑ τ'⊑τ , (s₁ ⊔syn s₂ isSynSlice deriv)


-- -- Theorem 2: when joined minimal syn slices synthesise a strictly MORE precise
-- -- type than the join (υ ≉ υ₁ ⊔ υ₂), any strict sub-slice of the join synthesises
-- -- a strictly LESS precise type than the join.
-- -- Proof by induction on D, pattern matching on s₁.valid and s₂.valid.
-- postulate
--   ⊔syn-precise
--     : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂}
--       → (s₁ : SynSlice D υ₁) → (s₂ : SynSlice D υ₂)
--       → IsMinimal s₁ → IsMinimal s₂
--       → let (υ' , s⊔) = s₁ ⊔syn' s₂ in
--         υ' ⊐ₛ υ₁ ⊔ₛ υ₂
--       → (∀ {υ'' : ⌊ τ ⌋} (s' : SynSlice D υ'')
--         → s' .progₛ ⊏ₛ s⊔ .progₛ
--         → υ'' ⊏ₛ υ₁ ⊔ₛ υ₂
--         )

-- -- Theorem 3: minimal syn slices of the same type join to the same type.
-- -- If u' ⊑ u ⊔ u = u then by Theorem 1, u' = u
-- -- Otherwie υ' ⊐ υ ⊔ₛ υ = u is impossible:
-- --   Split on s₁ = s₁ ⊔ s₂.
-- --     If   s₁ = s₁ ⊔ s₂, then s₁ synthesises u by unicity (contradiction, u' ⊐ u)
-- --     Else s₁ ⊏ s₁ ⊔ s₂ (as s₁ ⊑ s₁ ⊔ s₂), then theorem 2 gives u ⊏ u ⊔ u (contradiction)
-- -- TODO: Update comment to newest version
-- -- TODO: Use IsMinSynSlice type
-- ⊔syn-same
--   : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
--   → (s₁ s₂ : SynSlice D υ) → IsMinimal s₁ → IsMinimal s₂
--   → proj₁ (s₁ ⊔syn' s₂) ≈ₛ υ
-- ⊔syn-same {Γ = Γ} {e = e} {τ = τ} {D = D} {υ = υ} s₁ s₂ m₁ m₂
--   with (υ' , s⊔) ← s₁ ⊔syn' s₂ in eq with Eq.refl ← eq
--   with υ' ⊑ₛ? υ
-- ...  | yes υ'⊑υ = antisym {i = υ'} {υ} υ'⊑υ υ⊑υ' 
--                   where open ⊑ₛ
--                         υ⊑υ' = begin
--                                υ ≈˘⟨ ⊑ₛLat.⊔-idempotent υ ⟩
--                                υ ⊔ₛ υ ≤⟨ ⊔syn-upper s₁ s₂ ⟩
--                                υ' ∎
-- ...  | no  υ'⋢υ with s₁ .progₛ ≈ₛ? s⊔ .progₛ
-- ...               | yes s₁≈s⊔ = ⊥-elim (υ'⋢υ υ'⊑υ)
--                                 where open ⊑ₛ
--                                       s⊔⊑s₁ = begin
--                                               s⊔ .progₛ ≈˘⟨ s₁≈s⊔ ⟩
--                                               s₁ .progₛ ≤⟨ refl {x = ⊤ₛ {a = prog s₁}} ⟩
--                                               s₁ .progₛ ∎
--                                       υ'⊑υ  = syn-precision (s⊔⊑s₁ .proj₁)
--                                                             (s⊔⊑s₁ .proj₂)
--                                                             (s₁    .valid)
--                                                             (s⊔    .valid)
-- ...               | no  s₁≉s⊔ = begin-contradiction
--                                 υ <⟨ ⊔syn-precise s₁ s₂ m₁ m₂ υ'⊐υ⊔υ s₁ s₁⊏s⊔ ⟩
--                                 υ ⊔ₛ υ ≈⟨ ⊑ₛLat.⊔-idempotent υ ⟩
--                                 υ ∎
--                                 where open ⊑ₛ
--                                       s₁⊑s⊔  = ⊑ₛLat.x⊑ₛx⊔ₛy (s₁ .progₛ) (s₂ .progₛ)
--                                       s₁⊏s⊔  = ⊑∧≉⇒⊏ {x = s₁ .progₛ} {s⊔ .progₛ} s₁⊑s⊔ s₁≉s⊔
--                                       υ'⊐υ⊔υ = ⊒∧≉⇒⊐ {x = υ'} {υ ⊔ₛ υ} (⊔syn-upper s₁ s₂)
--                                                   λ υ'≈υ⊔υ → υ'⋢υ
--                                                     (begin
--                                                      υ' ≈⟨ υ'≈υ⊔υ ⟩
--                                                      υ ⊔ₛ υ ≈⟨ ⊑ₛLat.⊔-idempotent υ ⟩
--                                                      υ ∎)

-- -- -- Postulate 4: Every derivation and type slice has a minimal SynSlice
-- -- -- TODO: Prove via classical methods using the fact that a bottom element exists
-- postulate
--   minExists : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) (υ : ⌊ τ ⌋)
--              → ∃[ m ] IsMinimal {A = SynSlice D υ} m

-- -- -- Postulate 5: Monotonicity: more precise type slice → more precise minimal slice
-- postulate
--   mono : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂ : ⌊ τ ⌋}
--          → υ₁ ⊑ₛ υ₂
--          → (m₂ : SynSlice D υ₂) → IsMinimal m₂
--          → Σ[ m₁ ∈ SynSlice D υ₁ ] IsMinimal m₁ ∧ prog m₁ ⊑ prog m₂
