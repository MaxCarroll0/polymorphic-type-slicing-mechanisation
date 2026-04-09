module Core.Typ.Lattice where

open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary using (IsPartialOrder)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Maximum; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Relation.Binary.Lattice.Structures using (IsMeetSemilattice; IsJoinSemilattice; IsLattice; IsBoundedLattice; IsDistributiveLattice)
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum)
open import Relation.Nullary using (yes; no)
open import Function using (_on_)

open import Core.Typ.Base
open import Core.Typ.Equality
open import Core.Typ.Consistency
open import Core.Typ.Precision renaming (⊤ₛ to ⊤ₛ')

-- TODO: separate all lattice modules into different directory and import from Core

-- Meet operator. Note: order theoretic, does not require consistent types
_⊓_ : Typ → Typ → Typ
τ ⊓ τ' with diag τ τ'
...       | diff  = □
...       | kind□  = □
...       | kind* = *
...       | kind+ {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊓ τ₁') + (τ₂ ⊓ τ₂')
...       | kind× {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊓ τ₁') × (τ₂ ⊓ τ₂')
...       | kind⇒ {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊓ τ₁') ⇒ (τ₂ ⊓ τ₂')
...       | kind∀ {τ} {τ'} = ∀· (τ ⊓ τ')
...       | kindVar {m} {n} with m ≟ℕ n
...                         | yes _ = ⟨ m ⟩
...                         | no  _ = □

infixl 6 _⊓_

-- Join operator. Note: Only a LUB on consistent types
-- TODO: consider returning Maybe Typ to distinguish join failure from □
_⊔_ : Typ → Typ → Typ
τ ⊔ τ' with diag τ τ'
...       | kind□  = □
...       | kind* = *
...       | kind+ {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊔ τ₁') + (τ₂ ⊔ τ₂')
...       | kind× {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊔ τ₁') × (τ₂ ⊔ τ₂')
...       | kind⇒ {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊔ τ₁') ⇒ (τ₂ ⊔ τ₂')
...       | kind∀ {τ} {τ'} = ∀· (τ ⊔ τ')
...       | kindVar {m} {n} = ⟨ m ⟩
τ ⊔ τ'    | diff with τ ≟ □ | τ' ≟ □
...                 | yes _  | _      = τ'
...                 | no  _  | yes _  = τ
...                 | no  _  | no  _  = □

infixl 6 _⊔_

private
  -- Meet lower bounds
  ⊓-lb₁ : ∀ τ₁ τ₂ → τ₁ ⊓ τ₂ ⊑ τ₁
  ⊓-lb₁ τ       τ'         with diag τ τ'
  ⊓-lb₁ (τ₁ + τ₂) (τ₁' + τ₂') | kind+ = ⊑+ (⊓-lb₁ τ₁ τ₁') (⊓-lb₁ τ₂ τ₂')
  ⊓-lb₁ (τ₁ × τ₂) (τ₁' × τ₂') | kind× = ⊑× (⊓-lb₁ τ₁ τ₁') (⊓-lb₁ τ₂ τ₂')
  ⊓-lb₁ (τ₁ ⇒ τ₂) (τ₁' ⇒ τ₂') | kind⇒ = ⊑⇒ (⊓-lb₁ τ₁ τ₁') (⊓-lb₁ τ₂ τ₂')
  ⊓-lb₁ (∀· τ)    (∀· τ')     | kind∀ = ⊑∀ (⊓-lb₁ τ τ')
  ⊓-lb₁ ⟨ m ⟩     ⟨ n ⟩       | kindVar with m ≟ℕ n
  ...                               | yes _ = ⊑Var
  ...                               | no  _ = ⊑□
  ⊓-lb₁ *         *           | kind* = ⊑*
  ⊓-lb₁ □         □           | kind□ = ⊑□
  ⊓-lb₁ _         _           | diff = ⊑□

  ⊓-lb₂ : ∀ τ₁ τ₂ → τ₁ ⊓ τ₂ ⊑ τ₂
  ⊓-lb₂ τ       τ'        with diag τ τ'
  ⊓-lb₂ (τ₁ + τ₂) (τ₁' + τ₂') | kind+ = ⊑+ (⊓-lb₂ τ₁ τ₁') (⊓-lb₂ τ₂ τ₂')
  ⊓-lb₂ (τ₁ × τ₂) (τ₁' × τ₂') | kind× = ⊑× (⊓-lb₂ τ₁ τ₁') (⊓-lb₂ τ₂ τ₂')
  ⊓-lb₂ (τ₁ ⇒ τ₂) (τ₁' ⇒ τ₂') | kind⇒ = ⊑⇒ (⊓-lb₂ τ₁ τ₁') (⊓-lb₂ τ₂ τ₂')
  ⊓-lb₂ (∀· τ)    (∀· τ')     | kind∀ = ⊑∀ (⊓-lb₂ τ τ')
  ⊓-lb₂ ⟨ m ⟩     ⟨ n ⟩       | kindVar with m ≟ℕ n
  ...                               | yes refl = ⊑Var
  ...                               | no  _ = ⊑□
  ⊓-lb₂ *         *           | kind* = ⊑*
  ⊓-lb₂ □         □           | kind□ = ⊑□
  ⊓-lb₂ _         _           | diff  = ⊑□

  -- Meet is Greatest lower bound
  ⊓-glb : ∀ {τ τ₁ τ₂} → τ ⊑ τ₁ → τ ⊑ τ₂ → τ ⊑ τ₁ ⊓ τ₂
  ⊓-glb ⊑□ _                   = ⊑□
  ⊓-glb ⊑* ⊑*                  = ⊑*
  ⊓-glb (⊑Var {m}) (⊑Var {m}) with m ≟ℕ m
  ... | yes _ = ⊑Var
  ... | no contr = ⊥-elim (contr refl)
  ⊓-glb (⊑+ p₁ p₂) (⊑+ q₁ q₂) = ⊑+ (⊓-glb p₁ q₁) (⊓-glb p₂ q₂)
  ⊓-glb (⊑× p₁ p₂) (⊑× q₁ q₂) = ⊑× (⊓-glb p₁ q₁) (⊓-glb p₂ q₂)
  ⊓-glb (⊑⇒ p₁ p₂) (⊑⇒ q₁ q₂) = ⊑⇒ (⊓-glb p₁ q₁) (⊓-glb p₂ q₂)
  ⊓-glb (⊑∀ p)     (⊑∀ q)     = ⊑∀ (⊓-glb p q)

  ⊓-infimum : Infimum _⊑_ _⊓_
  ⊓-infimum τ₁ τ₂ = ⊓-lb₁ τ₁ τ₂ , ⊓-lb₂ τ₁ τ₂ , λ τ → ⊓-glb {τ} {τ₁} {τ₂}


  ⊑-isMeetSemilattice : IsMeetSemilattice _≡_ _⊑_ _⊓_
  ⊑-isMeetSemilattice = record
                        { isPartialOrder = ⊑.isPartialOrder
                        ; infimum        = ⊓-infimum
                        }

module ⊑Lat where
  open IsMeetSemilattice ⊑-isMeetSemilattice public
    using (infimum)
    renaming (∧-greatest to ⊓-greatest; x∧y≤x to x⊓y⊑x; x∧y≤y to x⊓y⊑y)

  isMeetSemilattice = ⊑-isMeetSemilattice

open LiftMeetSemilattice ⊑-isMeetSemilattice public

private
  ⊔-identityₗ : ∀ τ → □ ⊔ τ ≡ τ
  ⊔-identityₗ τ with diag □ τ
  ⊔-identityₗ □         | kind□ = refl
  ⊔-identityₗ τ         | diff with □ ≟ □ | τ ≟ □
  ...                          | yes _  | _      = refl
  ...                          | no □≢□ | _      = ⊥-elim (□≢□ refl)

  ⊔-identityᵣ : ∀ τ → τ ⊔ □ ≡ τ
  ⊔-identityᵣ τ with diag τ □
  ⊔-identityᵣ □         | kind□ = refl
  ⊔-identityᵣ τ         | diff with τ ≟ □ | □ ≟ □
  ...                          | yes refl | _      = refl
  ...                          | no  _    | yes _  = refl
  ...                          | no  _    | no □≢□ = ⊥-elim (□≢□ refl)


-- Join upper bounds (requires consistency)
-- TODO: refactor into Typ.Properties
module ~ where
  ⊔-ub₁ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → τ₁ ⊑ τ₁ ⊔ τ₂
  ⊔-ub₁ ~*               = ⊑*
  ⊔-ub₁ ~Var             = ⊑Var
  ⊔-ub₁ (~?₁ {τ})        rewrite ⊔-identityᵣ τ = ⊑.refl
  ⊔-ub₁ ~?₂              = ⊑□
  ⊔-ub₁ (~+ c₁ c₂)       = ⊑+ (⊔-ub₁ c₁) (⊔-ub₁ c₂)
  ⊔-ub₁ (~× c₁ c₂)       = ⊑× (⊔-ub₁ c₁) (⊔-ub₁ c₂)
  ⊔-ub₁ (~⇒ c₁ c₂)       = ⊑⇒ (⊔-ub₁ c₁) (⊔-ub₁ c₂)
  ⊔-ub₁ (~∀ c)           = ⊑∀ (⊔-ub₁ c)
  
  ⊔-ub₂ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → τ₂ ⊑ τ₁ ⊔ τ₂
  ⊔-ub₂ ~*               = ⊑*
  ⊔-ub₂ ~Var             = ⊑Var
  ⊔-ub₂ ~?₁              = ⊑□
  ⊔-ub₂ (~?₂ {τ})        rewrite ⊔-identityₗ τ = ⊑.refl
  ⊔-ub₂ (~+ c₁ c₂)       = ⊑+ (⊔-ub₂ c₁) (⊔-ub₂ c₂)
  ⊔-ub₂ (~× c₁ c₂)       = ⊑× (⊔-ub₂ c₁) (⊔-ub₂ c₂)
  ⊔-ub₂ (~⇒ c₁ c₂)       = ⊑⇒ (⊔-ub₂ c₁) (⊔-ub₂ c₂)
  ⊔-ub₂ (~∀ c)           = ⊑∀ (⊔-ub₂ c)
  
  ⊔-lub : ∀ {τ τ₁ τ₂} → τ₁ ~ τ₂ → τ₁ ⊑ τ → τ₂ ⊑ τ → τ₁ ⊔ τ₂ ⊑ τ
  ⊔-lub ~*               ⊑*         ⊑*         = ⊑*
  ⊔-lub ~Var             ⊑Var       ⊑Var       = ⊑Var
  ⊔-lub (~?₁ {τ₁})       p          ⊑□         rewrite ⊔-identityᵣ τ₁ = p
  ⊔-lub (~?₂ {τ₂})       ⊑□         q          rewrite ⊔-identityₗ τ₂ = q
  ⊔-lub (~+ c₁ c₂)       (⊑+ p₁ p₂) (⊑+ q₁ q₂) = ⊑+ (⊔-lub c₁ p₁ q₁) (⊔-lub c₂ p₂ q₂)
  ⊔-lub (~× c₁ c₂)       (⊑× p₁ p₂) (⊑× q₁ q₂) = ⊑× (⊔-lub c₁ p₁ q₁) (⊔-lub c₂ p₂ q₂)
  ⊔-lub (~⇒ c₁ c₂)       (⊑⇒ p₁ p₂) (⊑⇒ q₁ q₂) = ⊑⇒ (⊔-lub c₁ p₁ q₁) (⊔-lub c₂ p₂ q₂)
  ⊔-lub (~∀ c)           (⊑∀ p)     (⊑∀ q)     = ⊑∀ (⊔-lub c p q)


private
  ⊥ₛ' : ∀ {τ} → ⌊ τ ⌋
  ⊥ₛ' {τ} = □ isSlice ⊑□

  ⊥ₛ-min : ∀ {τ} → Minimum (_⊑ₛ_ {τ}) ⊥ₛ'
  ⊥ₛ-min υ = ⊑□

  ⊔-preserves-⊑ : ∀ {τ₁ τ₂ τ} → τ₁ ⊑ τ → τ₂ ⊑ τ → τ₁ ⊔ τ₂ ⊑ τ
  ⊔-preserves-⊑ p q = ~.⊔-lub (⊑-consistent p q) p q

-- Lift joins
_⊔ₛ_ : ∀ {τ} → ⌊ τ ⌋ → ⌊ τ ⌋ → ⌊ τ ⌋
υ ⊔ₛ υ' = υ .↓ ⊔ υ' .↓ isSlice ⊔-preserves-⊑ (υ .proof) (υ' .proof)

infixl 7 _⊔ₛ_

private
  ⊔ₛ-ub₁ : ∀ {τ} (υ₁ υ₂ : ⌊ τ ⌋) → υ₁ ⊑ₛ υ₁ ⊔ₛ υ₂
  ⊔ₛ-ub₁ υ₁ υ₂ = ~.⊔-ub₁ (⊑-consistent (υ₁ .proof) (υ₂ .proof))

  ⊔ₛ-ub₂ : ∀ {τ} (υ₁ υ₂ : ⌊ τ ⌋) → υ₂ ⊑ₛ υ₁ ⊔ₛ υ₂
  ⊔ₛ-ub₂ υ₁ υ₂ = ~.⊔-ub₂ (⊑-consistent (υ₁ .proof) (υ₂ .proof))
  ⊔ₛ-lub : ∀ {τ} {υ υ₁ υ₂ : ⌊ τ ⌋} → υ₁ ⊑ₛ υ → υ₂ ⊑ₛ υ → υ₁ ⊔ₛ υ₂ ⊑ₛ υ
  ⊔ₛ-lub {_} {υ} {υ₁} {υ₂} p q = ⊔-preserves-⊑ p q

  ⊔ₛ-supremum : ∀ {τ} → Supremum (_⊑ₛ_ {τ}) _⊔ₛ_
  ⊔ₛ-supremum υ₁ υ₂ = ⊔ₛ-ub₁ υ₁ υ₂ , ⊔ₛ-ub₂ υ₁ υ₂ , λ υ → ⊔ₛ-lub {υ = υ} {υ₁} {υ₂}


  ⊑ₛ-isJoinSemilattice : ∀ {τ} → IsJoinSemilattice (_≡_ on ↓) (_⊑ₛ_ {τ}) _⊔ₛ_
  ⊑ₛ-isJoinSemilattice = record
                         { isPartialOrder = ⊑ₛ.isPartialOrder
                         ; supremum       = ⊔ₛ-supremum
                         }

  ⊑ₛ-isLattice : ∀ {τ} → IsLattice (_≡_ on ↓) (_⊑ₛ_ {τ}) _⊔ₛ_ _⊓ₛ_
  ⊑ₛ-isLattice = record
                 { isPartialOrder = ⊑ₛ.isPartialOrder
                 ; supremum       = ⊔ₛ-supremum
                 ; infimum        = ⊓ₛ.infimum
                 }

  ⊑ₛ-isBoundedLattice : ∀ {τ} → IsBoundedLattice (_≡_ on ↓) (_⊑ₛ_ {τ}) _⊔ₛ_ _⊓ₛ_ ⊤ₛ' ⊥ₛ'
  ⊑ₛ-isBoundedLattice = record
                        { isLattice = ⊑ₛ-isLattice
                        ; maximum   = ⊤ₛ-max
                        ; minimum   = ⊥ₛ-min
                        }

  □⊓-absorb : ∀ τ → □ ⊓ τ ≡ □
  □⊓-absorb τ with diag □ τ
  ... | kind□ = refl
  ... | diff  = refl

  ⊓□-absorb : ∀ τ → τ ⊓ □ ≡ □
  ⊓□-absorb τ with diag τ □
  ... | kind□ = refl
  ... | diff  = refl

  □⊔□ : □ ⊔ □ ≡ □
  □⊔□ = refl

  dist : ∀ {τ τ₁ τ₂ τ₃} → τ₁ ⊑ τ → τ₂ ⊑ τ → τ₃ ⊑ τ → τ₁ ⊓ (τ₂ ⊔ τ₃) ≡ (τ₁ ⊓ τ₂) ⊔ (τ₁ ⊓ τ₃)
  dist {τ₂ = τ₂} {τ₃ = τ₃} ⊑□ _ _ =
    begin
    □ ⊓ (τ₂ ⊔ τ₃)          ≡⟨ □⊓-absorb (τ₂ ⊔ τ₃) ⟩
    □                      ≡⟨⟩
    □ ⊔ □                  ≡˘⟨ cong₂ _⊔_ (□⊓-absorb τ₂) (□⊓-absorb τ₃) ⟩
    (□ ⊓ τ₂) ⊔ (□ ⊓ τ₃)    ∎
  dist {τ₁ = τ₁} {τ₃ = τ₃} _ ⊑□ _ =
    begin
    τ₁ ⊓ (□ ⊔ τ₃)          ≡⟨ cong (τ₁ ⊓_) (⊔-identityₗ τ₃) ⟩
    τ₁ ⊓ τ₃                ≡˘⟨ ⊔-identityₗ (τ₁ ⊓ τ₃) ⟩
    □ ⊔ (τ₁ ⊓ τ₃)          ≡˘⟨ cong (_⊔ (τ₁ ⊓ τ₃)) (⊓□-absorb τ₁) ⟩
    (τ₁ ⊓ □) ⊔ (τ₁ ⊓ τ₃)   ∎
  dist {τ₁ = τ₁} {τ₂ = τ₂} _ _ ⊑□ =
    begin
    τ₁ ⊓ (τ₂ ⊔ □)          ≡⟨ cong (τ₁ ⊓_) (⊔-identityᵣ τ₂) ⟩
    τ₁ ⊓ τ₂                ≡˘⟨ ⊔-identityᵣ (τ₁ ⊓ τ₂) ⟩
    (τ₁ ⊓ τ₂) ⊔ □          ≡˘⟨ cong ((τ₁ ⊓ τ₂) ⊔_) (⊓□-absorb τ₁) ⟩
    (τ₁ ⊓ τ₂) ⊔ (τ₁ ⊓ □)   ∎
  dist ⊑*         ⊑*   ⊑*  = refl
  dist (⊑Var {n}) ⊑Var ⊑Var with n ≟ℕ n
  ... | yes _ = refl
  ... | no n≢n = ⊥-elim (n≢n refl)
  dist (⊑+ p₁ p₂) (⊑+ q₁ q₂) (⊑+ r₁ r₂) =
    cong₂ _+_ (dist p₁ q₁ r₁) (dist p₂ q₂ r₂)
  dist (⊑× p₁ p₂) (⊑× q₁ q₂) (⊑× r₁ r₂) =
    cong₂ _×_ (dist p₁ q₁ r₁) (dist p₂ q₂ r₂)
  dist (⊑⇒ p₁ p₂) (⊑⇒ q₁ q₂) (⊑⇒ r₁ r₂) =
    cong₂ _⇒_ (dist p₁ q₁ r₁) (dist p₂ q₂ r₂)
  dist (⊑∀ p) (⊑∀ q) (⊑∀ r) =
    cong ∀· (dist p q r)

  ⊓ₛ-distribˡ-⊔ₛ : ∀ {τ} (υ₁ υ₂ υ₃ : ⌊ τ ⌋) → (υ₁ ⊓ₛ (υ₂ ⊔ₛ υ₃)) ≈ₛ ((υ₁ ⊓ₛ υ₂) ⊔ₛ (υ₁ ⊓ₛ υ₃))
  ⊓ₛ-distribˡ-⊔ₛ υ₁ υ₂ υ₃ = dist (υ₁ .proof) (υ₂ .proof) (υ₃ .proof)

  ⊑ₛ-isDistributiveLattice : ∀ {τ} → IsDistributiveLattice (_≡_ on ↓) (_⊑ₛ_ {τ}) _⊔ₛ_ _⊓ₛ_
  ⊑ₛ-isDistributiveLattice = record
                             { isLattice    = ⊑ₛ-isLattice
                             ; ∧-distribˡ-∨ = ⊓ₛ-distribˡ-⊔ₛ
                             }

module ⊑ₛLat {τ} where
  open IsBoundedLattice (⊑ₛ-isBoundedLattice {τ}) public
    using (infimum; supremum;
           isBoundedJoinSemilattice; isBoundedMeetSemilattice; isJoinSemilattice; isMeetSemilattice; isLattice)
    renaming (x∧y≤x to x⊓ₛy⊑ₛx; x∧y≤y to x⊓ₛy⊑ₛy; x≤x∨y to x⊑ₛx⊔ₛy; y≤x∨y to y⊑ₛx⊔ₛy;
              ∧-greatest to ⊓ₛ-greatest; ∨-least to ⊔ₛ-least;
              maximum to ⊤ₛ-max; minimum to ⊥ₛ-min)
  ⊤ₛ : ⌊ τ ⌋
  ⊤ₛ = ⊤ₛ'

  ⊥ₛ : ⌊ τ ⌋
  ⊥ₛ = ⊥ₛ'

  isBoundedLattice = ⊑ₛ-isBoundedLattice

  open IsDistributiveLattice (⊑ₛ-isDistributiveLattice {τ}) public
    using () renaming (∧-distribˡ-∨ to ⊓ₛ-distribˡ-⊔ₛ)

  isDistributiveLattice = ⊑ₛ-isDistributiveLattice

import Core.Instances as I
instance
  typ-meet : I.HasMeet Typ
  typ-meet = record { _⊓_ = _⊓_ }
  typ-join : I.HasJoin Typ
  typ-join = record { _⊔_ = _⊔_ }
  typ-meetSemilattice : I.HasMeetSemilattice Typ
  typ-meetSemilattice = record { isMeetSemilattice = ⊑-isMeetSemilattice }
  typ-sliceLattice : I.SliceLattice SliceOf ↓
  typ-sliceLattice = record
    { _⊑ₛ_ = _⊑ₛ_ ; _⊓ₛ_ = _⊓ₛ_ ; _⊔ₛ_ = _⊔ₛ_
    ; ⊤ₛ = ⊤ₛ' ; ⊥ₛ = ⊥ₛ'
    ; isBoundedLattice = ⊑ₛ-isBoundedLattice
    ; isDistributiveLattice = ⊑ₛ-isDistributiveLattice
    }
