module Core.Typ.Lattice where

open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary using (IsPartialOrder)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Maximum; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Relation.Binary.Lattice.Structures using (IsMeetSemilattice; IsJoinSemilattice; IsLattice; IsBoundedLattice; IsDistributiveLattice)
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum)
open import Relation.Nullary using (yes; no)
open import Function using (_on_)

open import Core.Typ.Base
open import Core.Typ.Equality
open import Core.Typ.Consistency
open import Core.Typ.Precision
open import Core.Instances

private
  -- Meet operator. Note: order theoretic, does not require consistent types
  _⊓t_ : Typ → Typ → Typ
  τ ⊓t τ' with diag τ τ'
  ...       | diff  = □
  ...       | kind□  = □
  ...       | kind* = *
  ...       | kind+ {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊓t τ₁') + (τ₂ ⊓t τ₂')
  ...       | kind× {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊓t τ₁') × (τ₂ ⊓t τ₂')
  ...       | kind⇒ {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊓t τ₁') ⇒ (τ₂ ⊓t τ₂')
  ...       | kind∀ {τ} {τ'} = ∀· (τ ⊓t τ')
  ...       | kindVar {m} {n} with m ≟ℕ n
  ...                         | yes _ = ⟨ m ⟩
  ...                         | no  _ = □
  
  infixl 6 _⊓t_

  -- Join operator. Note: Only a LUB on consistent types
  -- TODO: consider returning Maybe Typ to distinguish join failure from □
  _⊔t_ : Typ → Typ → Typ
  τ ⊔t τ' with diag τ τ'
  ...       | kind□  = □
  ...       | kind* = *
  ...       | kind+ {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊔t τ₁') + (τ₂ ⊔t τ₂')
  ...       | kind× {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊔t τ₁') × (τ₂ ⊔t τ₂')
  ...       | kind⇒ {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊔t τ₁') ⇒ (τ₂ ⊔t τ₂')
  ...       | kind∀ {τ} {τ'} = ∀· (τ ⊔t τ')
  ...       | kindVar {m} {n} = ⟨ m ⟩
  τ ⊔t τ'    | diff with τ ≟ □ | τ' ≟ □
  ...                 | yes _  | _      = τ'
  ...                 | no  _  | yes _  = τ
  ...                 | no  _  | no  _  = □

  infixl 6 _⊔t_

  -- Meet lower bounds
  ⊓-lb₁ : ∀ τ₁ τ₂ → τ₁ ⊓t τ₂ ⊑ τ₁
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

  ⊓-lb₂ : ∀ τ₁ τ₂ → τ₁ ⊓t τ₂ ⊑ τ₂
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
  ⊓-glb : ∀ {τ τ₁ τ₂} → τ ⊑ τ₁ → τ ⊑ τ₂ → τ ⊑ τ₁ ⊓t τ₂
  ⊓-glb ⊑□ _                   = ⊑□
  ⊓-glb ⊑* ⊑*                  = ⊑*
  ⊓-glb (⊑Var {m}) (⊑Var {m}) with m ≟ℕ m
  ... | yes _ = ⊑Var
  ... | no contr = ⊥-elim (contr refl)
  ⊓-glb (⊑+ p₁ p₂) (⊑+ q₁ q₂) = ⊑+ (⊓-glb p₁ q₁) (⊓-glb p₂ q₂)
  ⊓-glb (⊑× p₁ p₂) (⊑× q₁ q₂) = ⊑× (⊓-glb p₁ q₁) (⊓-glb p₂ q₂)
  ⊓-glb (⊑⇒ p₁ p₂) (⊑⇒ q₁ q₂) = ⊑⇒ (⊓-glb p₁ q₁) (⊓-glb p₂ q₂)
  ⊓-glb (⊑∀ p)     (⊑∀ q)     = ⊑∀ (⊓-glb p q)

  ⊓-infimum : Infimum _⊑t_ _⊓t_
  ⊓-infimum τ₁ τ₂ = ⊓-lb₁ τ₁ τ₂ , ⊓-lb₂ τ₁ τ₂ , λ τ → ⊓-glb {τ} {τ₁} {τ₂}


  ⊑-isMeetSemilattice : IsMeetSemilattice _≡_ _⊑t_ _⊓t_
  ⊑-isMeetSemilattice = record
                        { isPartialOrder = ⊑.isPartialOrder
                        ; infimum        = ⊓-infimum
                        }

  ⊔-identityₗ : ∀ τ → □ ⊔t τ ≡ τ
  ⊔-identityₗ τ with diag □ τ
  ⊔-identityₗ □ | kind□ = refl
  ⊔-identityₗ τ | diff  = refl

  ⊔-identityᵣ : ∀ τ → τ ⊔t □ ≡ τ
  ⊔-identityᵣ τ with diag τ □
  ⊔-identityᵣ □ | kind□ = refl
  ⊔-identityᵣ τ | diff with τ ≟ □
  ...                  | yes refl = refl
  ...                  | no  _    = refl

-- Join upper bounds (requires consistency)
module ~ where
  open Core.Typ.Consistency.IsCompatibility
  sym = ~-isCompatibility .symmetric
  refle = ~-isCompatibility .reflexive -- TODO: rename imported refl to avoid name clash

  ⊔-ub₁ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → τ₁ ⊑ τ₁ ⊔t τ₂
  ⊔-ub₁ ~*               = ⊑*
  ⊔-ub₁ ~Var             = ⊑Var
  ⊔-ub₁ (~?₁ {τ})        rewrite ⊔-identityᵣ τ = ⊑.refl
  ⊔-ub₁ ~?₂              = ⊑□
  ⊔-ub₁ (~+ c₁ c₂)       = ⊑+ (⊔-ub₁ c₁) (⊔-ub₁ c₂)
  ⊔-ub₁ (~× c₁ c₂)       = ⊑× (⊔-ub₁ c₁) (⊔-ub₁ c₂)
  ⊔-ub₁ (~⇒ c₁ c₂)       = ⊑⇒ (⊔-ub₁ c₁) (⊔-ub₁ c₂)
  ⊔-ub₁ (~∀ c)           = ⊑∀ (⊔-ub₁ c)

  ⊔-ub₂ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → τ₂ ⊑ τ₁ ⊔t τ₂
  ⊔-ub₂ ~*               = ⊑*
  ⊔-ub₂ ~Var             = ⊑Var
  ⊔-ub₂ ~?₁              = ⊑□
  ⊔-ub₂ (~?₂ {τ})        rewrite ⊔-identityₗ τ = ⊑.refl
  ⊔-ub₂ (~+ c₁ c₂)       = ⊑+ (⊔-ub₂ c₁) (⊔-ub₂ c₂)
  ⊔-ub₂ (~× c₁ c₂)       = ⊑× (⊔-ub₂ c₁) (⊔-ub₂ c₂)
  ⊔-ub₂ (~⇒ c₁ c₂)       = ⊑⇒ (⊔-ub₂ c₁) (⊔-ub₂ c₂)
  ⊔-ub₂ (~∀ c)           = ⊑∀ (⊔-ub₂ c)

  ⊔-lub : ∀ {τ τ₁ τ₂} → τ₁ ~ τ₂ → τ₁ ⊑ τ → τ₂ ⊑ τ → τ₁ ⊔t τ₂ ⊑ τ
  ⊔-lub ~*               ⊑*         ⊑*         = ⊑*
  ⊔-lub ~Var             ⊑Var       ⊑Var       = ⊑Var
  ⊔-lub (~?₁ {τ₁})       p          ⊑□         rewrite ⊔-identityᵣ τ₁ = p
  ⊔-lub (~?₂ {τ₂})       ⊑□         q          rewrite ⊔-identityₗ τ₂ = q
  ⊔-lub (~+ c₁ c₂)       (⊑+ p₁ p₂) (⊑+ q₁ q₂) = ⊑+ (⊔-lub c₁ p₁ q₁) (⊔-lub c₂ p₂ q₂)
  ⊔-lub (~× c₁ c₂)       (⊑× p₁ p₂) (⊑× q₁ q₂) = ⊑× (⊔-lub c₁ p₁ q₁) (⊔-lub c₂ p₂ q₂)
  ⊔-lub (~⇒ c₁ c₂)       (⊑⇒ p₁ p₂) (⊑⇒ q₁ q₂) = ⊑⇒ (⊔-lub c₁ p₁ q₁) (⊔-lub c₂ p₂ q₂)
  ⊔-lub (~∀ c)           (⊑∀ p)     (⊑∀ q)     = ⊑∀ (⊔-lub c p q)

private
  ⊔-preserves-⊑ : ∀ {τ₁ τ₂ τ} → τ₁ ⊑ τ → τ₂ ⊑ τ → τ₁ ⊔t τ₂ ⊑ τ
  ⊔-preserves-⊑ p q = ~.⊔-lub (⊑-consistent p q) p q

-- Register meet/join/slice instances
import Core.Instances as I
instance
  typ-meet : I.HasMeet Typ
  typ-meet = record { _⊓_ = _⊓t_ ; closure = λ p q → ⊑.trans (⊓-lb₁ _ _) p }
  typ-join : I.HasJoin Typ
  typ-join = record { _⊔_ = _⊔t_ ; closure = ⊔-preserves-⊑ }
  typ-meetSemilattice : I.HasMeetSemilattice Typ
  typ-meetSemilattice = record { isMeetSemilattice = ⊑-isMeetSemilattice }

private
  ⊥ₛ' : ∀ {τ} → ⌊ τ ⌋
  ⊥ₛ' {τ} = □ isSlice ⊑□

  ⊥ₛ-min : ∀ {τ} → Minimum (_⊑ₛ_ {a = τ}) ⊥ₛ'
  ⊥ₛ-min υ = ⊑□

  ⊔ₛ-ub₁ : ∀ {τ} (υ₁ υ₂ : ⌊ τ ⌋) → υ₁ ⊑ₛ (_⊔ₛ_ {Typ} {τ} υ₁ υ₂)
  ⊔ₛ-ub₁ υ₁ υ₂ = ~.⊔-ub₁ (⊑-consistent (υ₁ .proof) (υ₂ .proof))

  ⊔ₛ-ub₂ : ∀ {τ} (υ₁ υ₂ : ⌊ τ ⌋) → υ₂ ⊑ₛ (_⊔ₛ_ {Typ} {τ} υ₁ υ₂)
  ⊔ₛ-ub₂ υ₁ υ₂ = ~.⊔-ub₂ (⊑-consistent (υ₁ .proof) (υ₂ .proof))

  □⊓-absorb : ∀ τ → □ ⊓t τ ≡ □
  □⊓-absorb τ with diag □ τ
  ... | kind□ = refl
  ... | diff  = refl

  ⊓□-absorb : ∀ τ → τ ⊓t □ ≡ □
  ⊓□-absorb τ with diag τ □
  ... | kind□ = refl
  ... | diff  = refl

  dist : ∀ {τ τ₁ τ₂ τ₃} → τ₁ ⊑ τ → τ₂ ⊑ τ → τ₃ ⊑ τ → τ₁ ⊓t (τ₂ ⊔t τ₃) ≡ (τ₁ ⊓t τ₂) ⊔t (τ₁ ⊓t τ₃)
  dist {τ₂ = τ₂} {τ₃ = τ₃} ⊑□ _ _ =
    begin
    □ ⊓t (τ₂ ⊔t τ₃)          ≡⟨ □⊓-absorb (τ₂ ⊔t τ₃) ⟩
    □                      ≡⟨⟩
    □ ⊔t □                  ≡˘⟨ cong₂ _⊔t_ (□⊓-absorb τ₂) (□⊓-absorb τ₃) ⟩
    (□ ⊓t τ₂) ⊔t (□ ⊓t τ₃)    ∎
  dist {τ₁ = τ₁} {τ₃ = τ₃} _ ⊑□ _ =
    begin
    τ₁ ⊓t (□ ⊔t τ₃)          ≡⟨ cong (τ₁ ⊓t_) (⊔-identityₗ τ₃) ⟩
    τ₁ ⊓t τ₃                ≡˘⟨ ⊔-identityₗ (τ₁ ⊓t τ₃) ⟩
    □ ⊔t (τ₁ ⊓t τ₃)          ≡˘⟨ cong (_⊔t (τ₁ ⊓t τ₃)) (⊓□-absorb τ₁) ⟩
    (τ₁ ⊓t □) ⊔t (τ₁ ⊓t τ₃)   ∎
  dist {τ₁ = τ₁} {τ₂ = τ₂} _ _ ⊑□ =
    begin
    τ₁ ⊓t (τ₂ ⊔t □)          ≡⟨ cong (τ₁ ⊓t_) (⊔-identityᵣ τ₂) ⟩
    τ₁ ⊓t τ₂                ≡˘⟨ ⊔-identityᵣ (τ₁ ⊓t τ₂) ⟩
    (τ₁ ⊓t τ₂) ⊔t □          ≡˘⟨ cong ((τ₁ ⊓t τ₂) ⊔t_) (⊓□-absorb τ₁) ⟩
    (τ₁ ⊓t τ₂) ⊔t (τ₁ ⊓t □)   ∎
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

  ⊓ₛ-distribˡ-⊔ₛ' : ∀ {τ : Typ} (υ₁ υ₂ υ₃ : ⌊ τ ⌋) → _≈ₛ_ (υ₁ ⊓ₛ (υ₂ ⊔ₛ υ₃)) ((υ₁ ⊓ₛ υ₂) ⊔ₛ (υ₁ ⊓ₛ υ₃))
  ⊓ₛ-distribˡ-⊔ₛ' υ₁ υ₂ υ₃ = dist (υ₁ .proof) (υ₂ .proof) (υ₃ .proof)

postulate
  typ-¬ₛ : ∀ {τ : Typ} → ⌊ τ ⌋ → ⌊ τ ⌋
  typ-⊔ₛ-complement : ∀ {τ : Typ} (s : ⌊ τ ⌋) → _≈ₛ_ (s ⊔ₛ typ-¬ₛ s) (⊤ₛ {a = τ})
  typ-⊓ₛ-complement : ∀ {τ : Typ} (s : ⌊ τ ⌋) → _≈ₛ_ (s ⊓ₛ typ-¬ₛ s) (⊥ₛ' {τ})
  typ-¬ₛ-cong : ∀ {τ : Typ} {s₁ s₂ : ⌊ τ ⌋} → _≈ₛ_ s₁ s₂ → _≈ₛ_ (typ-¬ₛ s₁) (typ-¬ₛ s₂)

instance
  typ-sliceLattice : I.SliceLattice Typ
  typ-sliceLattice = record
    { ⊥ₛ = ⊥ₛ'
    ; ⊥ₛ-min = ⊥ₛ-min
    ; x⊓ₛy⊑ₛx = λ s₁ s₂ → ⊓-lb₁ (s₁ .↓) (s₂ .↓)
    ; x⊓ₛy⊑ₛy = λ s₁ s₂ → ⊓-lb₂ (s₁ .↓) (s₂ .↓)
    ; ⊓ₛ-greatest = λ p q → ⊓-glb p q
    ; x⊑ₛx⊔ₛy = ⊔ₛ-ub₁
    ; y⊑ₛx⊔ₛy = ⊔ₛ-ub₂
    ; ⊓ₛ-distribˡ-⊔ₛ = ⊓ₛ-distribˡ-⊔ₛ'
    ; ¬ₛ_ = typ-¬ₛ
    ; ⊔ₛ-complement = typ-⊔ₛ-complement
    ; ⊓ₛ-complement = typ-⊓ₛ-complement
    ; ¬ₛ-cong = typ-¬ₛ-cong
    }
