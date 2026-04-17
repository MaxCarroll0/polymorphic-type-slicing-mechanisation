open import Data.Nat hiding (_+_; _⊔_)
open import Data.Unit
open import Agda.Builtin.FromNat
open import Data.Nat.Literals
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsEquivalence; IsDecEquivalence)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; subst; cong; cong₂)
open import Data.Maybe using (just)
open import Data.List using (_∷_; [])
open import Function using (_on_)
open import Core
open import Core.Typ.Properties using (⊔t-zeroₗ; ⊔t-zeroᵣ; ⊔-×-⊑; ⊔□×□)
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

  reindex : ∀ {υ'} → υ' ⊑ₛ type → SynSlice D ◂ υ'
  reindex p = record {progₛ = progₛ; type = type; syn = syn; valid = p}
  
open SynSlice_◂_ public
  renaming ( ↓ρ to _↓ρ; ↓ρₛ to _↓ρₛ; ↓ρ⊑ to _↓ρ⊑
           ; ↓ϕ to _↓ϕ; ↓ϕₛ to _↓ϕₛ; ↓ϕ⊑ to _↓ϕ⊑
           ; ↓γ to _↓γ; ↓γₛ to _↓γₛ; ↓σ to _↓σ
           ; ↓σₛ to _↓σₛ; ↓γ⊑ to _↓γ⊑; ↓σ⊑ to _↓σ⊑)
infix 10 SynSlice_◂_
infix 10 _⇑_∈_⊒_
infix 11 _↓ρ _↓ρₛ _↓ρ⊑ _↓ϕ _↓ϕₛ _↓ϕ⊑ _↓γ _↓γₛ _↓σ _↓σₛ _↓γ⊑

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

MinSynSlice_◂_ : ∀ {n Γ e τ} → (D : n ； Γ ⊢ e ↦ τ) → ⌊ τ ⌋ → Set
MinSynSlice D ◂ υ = Σ[ s ∈ SynSlice D ◂ υ ] IsMinimal s

_↓s : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} → MinSynSlice D ◂ υ → SynSlice D ◂ υ
_↓s = proj₁
minimality : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} → ((s , _) : MinSynSlice D ◂ υ) → IsMinimal s
minimality = proj₂


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

infixl 6 _⊔syn_
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


-- Theorem 2: when joined minimal syn slices synthesise a strictly MORE precise, the result is minimal bounded by the joined query υ₁ ⊔ υ₂
-- type than the join (υ ≉ υ₁ ⊔ υ₂), any strict sub-slice of the join synthesises
-- a strictly LESS precise type than the join.
-- Proof by induction on D, pattern matching on s₁.valid and s₂.valid.
-- possibly untrue I think, consider an aliased term in multple ways and remove just one part of the alias? though maybe minimality rules this out
--  ⊔syn-precise
--    : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂}
--      → (s₁ : SynSlice D ◂ υ₁) → (s₂ : SynSlice D ◂ υ₂)
--      → IsMinimal s₁ → IsMinimal s₂
--      → (s₁ ⊔syn s₂) .type ⊐ₛ υ₁ ⊔ₛ υ₂ 
--      → IsMinimal (s₁ ⊔syn s₂)
        
        
-- Theorem 3: minimal syn slices of the same type join to the same type.
-- If u' ⊑ u ⊔ u = u then by Theorem 1, u' = u
-- Otherwie υ' ⊐ υ ⊔ₛ υ = u is impossible:
--   Split on s₁ = s₁ ⊔ s₂.
--     If   s₁ = s₁ ⊔ s₂, then s₁ synthesises u by unicity (contradiction, u' ⊐ u)
--     Else s₁ ⊏ s₁ ⊔ s₂ (as s₁ ⊑ s₁ ⊔ s₂), then theorem 2 gives u ⊏ u ⊔ u (contradiction)
-- TODO: Update comment to newest version
-- TODO: Use IsMinSynSlice type
-- ⊔syn-same
--   : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
--   → (s₁ s₂ : SynSlice D ◂ υ) → IsMinimal s₁ → IsMinimal s₂
--   → (s₁ ⊔syn s₂) .type ≈ₛ υ
-- ⊔syn-same {Γ = Γ} {e = e} {τ = τ} {D = D} {υ = υ} s₁ s₂ m₁ m₂
--   with s⊔@(ρₛ⊔ ⇑ ϕ⊔ ∈ d⊔ ⊒ υ⊔⊑) ← s₁ ⊔syn s₂ in eq with Eq.refl ← eq
--   with υ ⊑ₛ? υ
-- ...  | yes ϕ⊔⊑υ = antisym {i = ϕ⊔} {υ} {!ϕ⊔⊑υ!} {!υ⊑ϕ⊔!} 
--                   where open ⊑ₛ
--                         υ⊑ϕ⊔ = begin
--                                --υ ≈˘⟨ ⊑ₛLat.⊔-idempotent υ ⟩
--                                --υ ⊔ₛ υ ≤⟨ ⊔syn-upper s₁ s₂ ⟩
--                                ϕ⊔ ∎
-- ...  | no  ϕ⊔⋢υ with (s₁ ↓ρₛ) ≈ₛ? ρₛ⊔
-- ...               | yes s₁≈s⊔ = ⊥-elim (ϕ⊔⋢υ υ'⊑υ)
--                                 where open ⊑
--                                       s⊔⊑s₁ = begin
--                                               --s⊔ ≈˘⟨ s₁≈s⊔ ⟩
--                                               --s₁ ≤⟨ refl {x = ⊤ₛ {a = prog s₁}} ⟩
--                                               s₁ ∎
--                                       υ'⊑υ  = syn-precision ({!s⊔⊑s₁ .syn!})
--                                                             ({!s⊔⊑s₁ .syn!})
--                                                             ({!s₁    .valid!})
--                                                             ({!s⊔    .valid!})
-- ...               | no  s₁≉s⊔ = begin-contradiction
--                                 --υ <⟨ ⊔syn-precise s₁ s₂ m₁ m₂ υ'⊐υ⊔υ s₁ s₁⊏s⊔ ⟩
--                                 --υ ⊔ₛ υ ≈⟨ ⊑ₛLat.⊔-idempotent υ ⟩
--                                 υ ∎
--                                 where open ⊑ₛ
--                                       s₁⊑s⊔  = ⊑ₛLat.x⊑ₛx⊔ₛy (s₁ .progₛ) (s₂ .progₛ)
--                                       s₁⊏s⊔  = ⊑∧≉⇒⊏ {x = s₁ .progₛ} {s⊔ .progₛ} {!s₁⊑s⊔!} s₁≉s⊔
--                                       υ'⊐υ⊔υ = ⊒∧≉⇒⊐ {x = ϕ⊔} {υ ⊔ₛ υ} (υ⊔⊑)
--                                                   λ υ'≈υ⊔υ → ϕ⊔⋢υ
--                                                     ({!begin
--                                                      ϕ⊔ ≈⟨ υ'≈υ⊔υ ⟩
--                                                      υ ⊔ₛ υ ≈⟨ ⊑ₛLat.⊔-idempotent υ ⟩
--                                                      υ ∎!})

-- Postulate 4: Syn Slice (and hence also any derivation) has a minimal SynSlice
--              below it for any query slices υ
-- TODO: Prove via classical methods using the fact that a bottom element exists
postulate
  minExists : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ : ⌊ τ ⌋}
                (s : SynSlice D ◂ υ)
              → Σ[ (m , _) ∈ MinSynSlice D ◂ υ ]
                  m ⊑ s
             

-- Postulate 5: Monotonicity: more precise type slice → more precise minimal slice
postulate
  mono : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂ : ⌊ τ ⌋}
         → υ₁ ⊑ₛ υ₂
         → (m₂ : SynSlice D ◂ υ₂) → IsMinimal m₂
         → Σ[ m₁ ∈ SynSlice D ◂ υ₁ ] IsMinimal m₁ ∧ m₁ ↓ρ ⊑ m₂ ↓ρ

-- -- D: x : * ⇒ *; y : * ⇒ * ⊢ x + y ⇑ * ⇒ *
-- -- x : * ⇒ □; y : □ ⇒ A ⊢ x + y ⇑ * ⇒ *
-- -- x : * ⇒ *; y : □ ⊢ x + □ ⇑ A ⇒ □

-- -- Product of min slices:
-- -- x : A ⇒ A; y : □ ⇒ A ⊢ (x + y, x + □) ⇑ * ⇒ * × * ⇒ *
-- -- is NOT MINIMAL!!

-- -- Naive join of context in constructing products from joins is bad!

-- MIN SLICE DECOMPOSITIONS
_×ₛ_ : ∀ {τ₁ τ₂ : Typ} → ⌊ τ₁ ⌋ → ⌊ τ₂ ⌋ → ⌊ τ₁ × τ₂ ⌋
s₁ ×ₛ s₂ = (s₁ .↓ × s₂ .↓) isSlice ⊑× (s₁ .proof) (s₂ .proof)

_&ₛ_ : ∀ {e₁ e₂ : Exp} → ⌊ e₁ ⌋ → ⌊ e₂ ⌋ → ⌊ e₁ & e₂ ⌋
s₁ &ₛ s₂ = (s₁ .↓ & s₂ .↓) isSlice ⊑& (s₁ .proof) (s₂ .proof)

-- Pair construction: given m₁ : D₁ ◂ υ₁ and m₂ : D₂ ◂ υ₂, form
-- a slice of ↦& D₁ D₂ ◂ (υ₁ ×ₛ υ₂) by joining assumptions (γ₁ ⊔ γ₂)
-- and re-deriving both components under the shared context.
--   γₛ⊔ = γₛ₁ ⊔ₛ γₛ₂ ⊑ Γ   (join closure)
--   dᵢ' : γ⊔ ⊢ σᵢ ↦ ϕᵢ'    (static gradual guarantee)
--   υᵢ ⊑ ϕᵢ ⊑ ϕᵢ'          (valid of dᵢ + syn-precision)
_&syn_   : ∀ {n Γ e₁ e₂ τ₁ τ₂} {D₁ : n ； Γ ⊢ e₁ ↦ τ₁}
             {D₂ : n ； Γ ⊢ e₂ ↦ τ₂} {υ₁ υ₂}
           → SynSlice D₁ ◂ υ₁ → SynSlice D₂ ◂ υ₂
           → SynSlice (↦& D₁ D₂) ◂ (υ₁ ×ₛ υ₂)
_&syn_ {D₁ = D₁} {D₂ = D₂}
       (ρₛ₁ ⇑ ϕ₁ ∈ d₁ ⊒ υ₁⊑ϕ₁) (ρₛ₂ ⇑ ϕ₂ ∈ d₂ ⊒ υ₂⊑ϕ₂)
  with static-gradual-syn (γₛ⊔ .proof) (sndₛ ρₛ₁ .proof) D₁
     | static-gradual-syn (γₛ⊔ .proof) (sndₛ ρₛ₂ .proof) D₂
  where γₛ⊔ = fstₛ ρₛ₁ ⊔ₛ fstₛ ρₛ₂
... | ϕ₁' , d₁' , ϕ₁'⊑τ₁ | ϕ₂' , d₂' , ϕ₂'⊑τ₂
  = (γₛ⊔ ,ₛ (σₛ₁ &ₛ σₛ₂)) ⇑ (↑ ϕ₁'⊑τ₁) ×ₛ (↑ ϕ₂'⊑τ₂)
    ∈ ↦& d₁' d₂' ⊒ ⊑× υ₁⊑ϕ₁' υ₂⊑ϕ₂'
  where
    γₛ⊔ = fstₛ ρₛ₁ ⊔ₛ fstₛ ρₛ₂
    σₛ₁ = sndₛ ρₛ₁
    σₛ₂ = sndₛ ρₛ₂
    open ⊑ {A = Typ} using () renaming (trans to ⊑t-trans)
    open ⊑ {A = Exp} using () renaming (refl to ⊑e-refl)
    υ₁⊑ϕ₁' = ⊑t-trans υ₁⊑ϕ₁
              (syn-precision (⊑ₛLat.x⊑ₛx⊔ₛy (fstₛ ρₛ₁) (fstₛ ρₛ₂))
                             ⊑e-refl d₁' d₁)
    υ₂⊑ϕ₂' = ⊑t-trans υ₂⊑ϕ₂
              (syn-precision (⊑ₛLat.y⊑ₛx⊔ₛy (fstₛ ρₛ₁) (fstₛ ρₛ₂))
                             ⊑e-refl d₂' d₂)

-- Minimal product slices decompose into minimal component slices.
-- Querying with a product υ₁ ×ₛ υ₂ forces the slice to have
-- synthesise a product ϕ₁ × ϕ₂ type, and have a σ₁ & σ₂ shape
-- From minimal γ ⊢ σ₁ & σ₂ ↦ ϕ₁ × ϕ₂ ⊒ υ₁ × υ₂
-- Rule inversion gives subderivations d₁ and d₂ on assumptions γ,
-- From any two minimal slices γ₁, σ₁' and γ₂, σ₂' on d₁ d₂
-- Construct a product γ₁⊔γ₂ ⊢ σ₁' & σ₂' ↦ ϕ'
-- (where ϕ' ⊒ ϕ₁ × ϕ₂ ⊑ υ₁ × υ₂ by graduality via _&syn_ def)
-- Finally, γ₁⊔γ₂ ⊑ γ by join LUB property giving γ₁⊔γ₂ ≈ γ by minimality
min-prod-decomposability
  : ∀ {n Γ e₁ e₂ τ₁ τ₂}
      {D₁ : n ； Γ ⊢ e₁ ↦ τ₁} {D₂ : n ； Γ ⊢ e₂ ↦ τ₂}
      {υ₁ : ⌊ τ₁ ⌋} {υ₂ : ⌊ τ₂ ⌋}
      ((m× , _) : MinSynSlice (↦& D₁ D₂) ◂ (υ₁ ×ₛ υ₂))
    → Σ[ (m₁ , _) ∈ MinSynSlice D₁ ◂ υ₁ ]
      Σ[ (m₂ , _) ∈ MinSynSlice D₂ ◂ υ₂ ]
         m× ≈ m₁ &syn m₂
min-prod-decomposability (m× , min)
  with m× .valid | m× ↓σ | m× ↓σ⊑ | m× ↓ϕ⊑ | m× .syn
...  | ⊑× υ₁⊑ϕ₁ υ₂⊑ϕ₂ | σ₁ & σ₂ | ⊑& σ₁⊑e₁ σ₂⊑e₂ | ⊑× ϕ₁⊑τ₁ ϕ₂⊑τ₂ | ↦& d₁ d₂
  = let s₁ = ((m× ↓γₛ) ,ₛ (σ₁ isSlice σ₁⊑e₁)) ⇑ ↑ ϕ₁⊑τ₁ ∈ d₁ ⊒ υ₁⊑ϕ₁
        s₂ = ((m× ↓γₛ) ,ₛ (σ₂ isSlice σ₂⊑e₂)) ⇑ ↑ ϕ₂⊑τ₂ ∈ d₂ ⊒ υ₂⊑ϕ₂
        m₁ , (γ₁⊑γ , σ₁'⊑σ₁) = minExists s₁
        m₂ , (γ₂⊑γ , σ₂'⊑σ₂) = minExists s₂
    in m₁ , m₂
     , min ((m₁ ↓s) &syn (m₂ ↓s))
           (HasJoin.closure assms-join γ₁⊑γ γ₂⊑γ , ⊑& σ₁'⊑σ₁ σ₂'⊑σ₂)

π₁ₛ : ∀ {e : Exp} → ⌊ e ⌋ → ⌊ π₁ e ⌋
π₁ₛ (σ isSlice σ⊑e) = (π₁ σ) isSlice (⊑π₁ σ⊑e)

π₁syn : ∀ {n Γ e τ₁ τ₂} {D : n ； Γ ⊢ e ↦ τ₁ × τ₂}
          {υ₁ : ⌊ τ₁ ⌋} {υ₂ : ⌊ τ₂ ⌋}
        → SynSlice D ◂ (υ₁ ×ₛ υ₂)
        → SynSlice (↦π₁ {τ₂ = τ₂} D ⊔□×□) ◂ υ₁
π₁syn {τ₁ = τ₁} {τ₂ = τ₂} {D = D} s
  with s .valid | s ↓ϕ⊑ | s .syn
... | ⊑× υ₁⊑ϕ₁ _ | ⊑× {τ₁ = ϕ₁} {τ₂ = ϕ₂} ϕ₁⊑τ₁ ϕ₂⊑τ₂ | d
  = (fstₛ (s ↓ρₛ) ,ₛ π₁ₛ (sndₛ (s ↓ρₛ))) ⇑ ↑ ϕ₁⊑τ₁ ∈ ↦π₁ d (⊔□×□ {ϕ₁} {ϕ₂}) ⊒ υ₁⊑ϕ₁

π₁syn-↓ρ : ∀ {n Γ e τ₁ τ₂} {D : n ； Γ ⊢ e ↦ τ₁ × τ₂}
              {υ₁ : ⌊ τ₁ ⌋} {υ₂ : ⌊ τ₂ ⌋}
              (s : SynSlice D ◂ (υ₁ ×ₛ υ₂))
            → (π₁syn s) ↓ρ ≡ (s ↓γ , π₁ (s ↓σ))
π₁syn-↓ρ {τ₁ = τ₁} {τ₂ = τ₂} s
  with s .valid | s ↓ϕ⊑ | s .syn
... | ⊑× _ _ | ⊑× {τ₁ = ϕ₁} {τ₂ = ϕ₂} _ _ | d = refl

-- Projection decomposability: a minimal slice of ↦π₁ D ◂ υ (for υ ≢ □)
-- decomposes into a minimal slice of D ◂ (υ ×ₛ ⊥ₛ). (if υ≡□ then m=□)
-- Case □: impossible with υ ≢ □.
-- Case ↦π₁ s x: invert to get sub-derivation s on e, build
-- s× : SynSlice D ◂ (υ ×ₛ ⊥ₛ) from s, then show use minimality on π₁
min-π₁-decomposability
  : ∀ {n Γ e τ₁ τ₂} {D : n ； Γ ⊢ e ↦ τ₁ × τ₂}
      {υ : ⌊ τ₁ ⌋}
    → υ .↓ ≢ □
    → ((mπ₁ , _) : MinSynSlice (↦π₁ D ⊔□×□) ◂ υ)
    → Σ[ (m× , _) ∈ MinSynSlice D ◂ (υ ×ₛ ⊥ₛ) ]
        mπ₁ ≈ π₁syn m×
min-π₁-decomposability {τ₁ = τ₁} {τ₂ = τ₂} {D = D} υ≢□ (mπ₁ , min)
  with mπ₁ .syn  | mπ₁ .valid | mπ₁ .type | mπ₁ ↓σ⊑
... | ↦□ | ⊑□ | _ | _ = ⊥-elim (υ≢□ refl)
... | ↦π₁ {τ = ϕ'} s x | υ⊑ϕ₁ | ϕ₁ isSlice ϕ₁⊑τ₁ | ⊑π₁ σ'⊑e
  with syn-precision (mπ₁ ↓γ⊑) σ'⊑e D s
... | ⊑× {τ₁ = ϕ₁'} {τ₂ = ϕ₂'} ϕ₁'⊑τ₁ ϕ₂'⊑τ₂
  rewrite ⊔t-zeroᵣ {ϕ₁'} | ⊔t-zeroᵣ {ϕ₂'} with refl ← x
  = (m× , min×) , min (π₁syn m×) π₁m×⊑mπ₁
  where
    s× = ((mπ₁ ↓γₛ) ,ₛ (↑ σ'⊑e))
           ⇑ (↑ ϕ₁'⊑τ₁) ×ₛ (↑ ϕ₂'⊑τ₂) ∈ s ⊒ ⊑× υ⊑ϕ₁ ⊑□
    m× = minExists s× .proj₁ .proj₁
    min× = minExists s× .proj₁ .proj₂
    π₁m×⊑mπ₁ : (π₁syn m×) ↓ρ ⊑ mπ₁ ↓ρ
    π₁m×⊑mπ₁ rewrite π₁syn-↓ρ m×
      = minExists s× .proj₂ .proj₁ , ⊑π₁ (minExists s× .proj₂ .proj₂)
... | ⊑□ rewrite ⊔t-zeroₗ {□ × □} with refl ← x with ⊑□ ← υ⊑ϕ₁ = ⊥-elim (υ≢□ refl)

π₂ₛ : ∀ {e : Exp} → ⌊ e ⌋ → ⌊ π₂ e ⌋
π₂ₛ (σ isSlice σ⊑e) = (π₂ σ) isSlice (⊑π₂ σ⊑e)

π₂syn : ∀ {n Γ e τ₁ τ₂} {D : n ； Γ ⊢ e ↦ τ₁ × τ₂}
          {υ₁ : ⌊ τ₁ ⌋} {υ₂ : ⌊ τ₂ ⌋}
        → SynSlice D ◂ (υ₁ ×ₛ υ₂)
        → SynSlice (↦π₂ {τ₁ = τ₁} D ⊔□×□) ◂ υ₂
π₂syn {τ₁ = τ₁} {τ₂ = τ₂} {D = D} s
  with s .valid | s ↓ϕ⊑ | s .syn
... | ⊑× _ υ₂⊑ϕ₂ | ⊑× {τ₁ = ϕ₁} {τ₂ = ϕ₂} ϕ₁⊑τ₁ ϕ₂⊑τ₂ | d
  = (fstₛ (s ↓ρₛ) ,ₛ π₂ₛ (sndₛ (s ↓ρₛ))) ⇑ ↑ ϕ₂⊑τ₂ ∈ ↦π₂ d (⊔□×□ {ϕ₁} {ϕ₂}) ⊒ υ₂⊑ϕ₂

π₂syn-↓ρ : ∀ {n Γ e τ₁ τ₂} {D : n ； Γ ⊢ e ↦ τ₁ × τ₂}
              {υ₁ : ⌊ τ₁ ⌋} {υ₂ : ⌊ τ₂ ⌋}
              (s : SynSlice D ◂ (υ₁ ×ₛ υ₂))
            → (π₂syn s) ↓ρ ≡ (s ↓γ , π₂ (s ↓σ))
π₂syn-↓ρ {τ₁ = τ₁} {τ₂ = τ₂} s
  with s .valid | s ↓ϕ⊑ | s .syn
... | ⊑× _ _ | ⊑× {τ₁ = ϕ₁} {τ₂ = ϕ₂} _ _ | d = refl

min-π₂-decomposability
  : ∀ {n Γ e τ₁ τ₂} {D : n ； Γ ⊢ e ↦ τ₁ × τ₂}
      {υ : ⌊ τ₂ ⌋}
    → υ .↓ ≢ □
    → ((mπ₂ , _) : MinSynSlice (↦π₂ D ⊔□×□) ◂ υ)
    → Σ[ (m× , _) ∈ MinSynSlice D ◂ (⊥ₛ ×ₛ υ) ]
        mπ₂ ≈ π₂syn m×
min-π₂-decomposability {τ₁ = τ₁} {τ₂ = τ₂} {D = D} υ≢□ (mπ₂ , min)
  with mπ₂ .syn  | mπ₂ .valid | mπ₂ .type | mπ₂ ↓σ⊑
... | ↦□ | ⊑□ | _ | _ = ⊥-elim (υ≢□ refl)
... | ↦π₂ {τ = ϕ'} s x | υ⊑ϕ₂ | ϕ₂ isSlice ϕ₂⊑τ₂ | ⊑π₂ σ'⊑e
  with syn-precision (mπ₂ ↓γ⊑) σ'⊑e D s
... | ⊑× {τ₁ = ϕ₁'} {τ₂ = ϕ₂'} ϕ₁'⊑τ₁ ϕ₂'⊑τ₂
  rewrite ⊔t-zeroᵣ {ϕ₁'} | ⊔t-zeroᵣ {ϕ₂'} with refl ← x
  = (m× , min×) , min (π₂syn m×) π₂m×⊑mπ₂
  where
    s× = ((mπ₂ ↓γₛ) ,ₛ (↑ σ'⊑e))
           ⇑ (↑ ϕ₁'⊑τ₁) ×ₛ (↑ ϕ₂'⊑τ₂) ∈ s ⊒ ⊑× ⊑□ υ⊑ϕ₂
    m× = minExists s× .proj₁ ↓s
    min× = minimality (minExists s× .proj₁)
    π₂m×⊑mπ₂ : (π₂syn m×) ↓ρ ⊑ mπ₂ ↓ρ
    π₂m×⊑mπ₂ rewrite π₂syn-↓ρ m×
      = minExists s× .proj₂ .proj₁ , ⊑π₂ (minExists s× .proj₂ .proj₂)
... | ⊑□ rewrite ⊔t-zeroₗ {□ × □} with refl ← x with ⊑□ ← υ⊑ϕ₂ = ⊥-elim (υ≢□ refl)
