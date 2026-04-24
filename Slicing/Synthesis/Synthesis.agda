open import Data.Nat hiding (_+_; _⊔_)
open import Data.Unit
open import Agda.Builtin.FromNat
open import Data.Nat.Literals
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Induction.WellFounded using (WellFounded; Acc; acc)
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
module Slicing.Synthesis.Synthesis where

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

-- Bounded minimality (BoundedIsMinimal, BoundedMinSynSlice)
-- is in Slicing.Synthesis.BoundedSynthesis

-- Theorem 1: By using graduality we can construct a joined derivation
--            This join must synthesise a more or equally specific type
--            Hence, it is a valid SynSlice

static-gradual-syn-prog -- (simple helpers)
  : ∀ {n Γ e τ} → (D : n ； Γ ⊢ e ↦ τ)
    → (ρₛ : ⌊ Γ , e ⌋) 
    → Σ[ ϕ ∈ ⌊ τ ⌋ ] n ； fstₛ ρₛ .↓ ⊢ sndₛ ρₛ .↓ ↦ ϕ .↓
static-gradual-syn-prog D ρₛ
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
  with static-gradual-syn-prog D (ρₛ₁ ⊔ₛ ρₛ₂) in eq
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
-- ...  | no  ϕ⊔⋢υ with (s₁ ↓ρₛ) ≈ₛ? ρₛ⊔
-- ...               | yes s₁≈s⊔ = ⊥-elim (ϕ⊔⋢υ υ'⊑υ)
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
--                                                   λ υ'≈υ⊔υ → ϕ⊔⋢υ
--                                                     ({!begin
--                                                      ϕ⊔ ≈⟨ υ'≈υ⊔υ ⟩
--                                                      υ ⊔ₛ υ ≈⟨ ⊑ₛLat.⊔-idempotent υ ⟩
--                                                      υ ∎!})

-- Theorem 4: Every SynSlice has a minimal SynSlice below it
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

