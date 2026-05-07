module Core.Typ.Lattice where

open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _∧_)
open import Relation.Binary using (IsPartialOrder)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Maximum; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Relation.Binary.Lattice.Structures using (IsMeetSemilattice; IsJoinSemilattice; IsLattice; IsBoundedLattice; IsDistributiveLattice)
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum; Exponential)
open import Relation.Nullary using (yes; no)
open import Function using (_on_; case_of_; flip)

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

  -- Collapse helpers: combine results, returning □ if all are □
  c+ : Typ → Typ → Typ
  c+ □ □ = □
  c+ a b = a + b

  c× : Typ → Typ → Typ
  c× □ □ = □
  c× a b = a × b

  c⇒ : Typ → Typ → Typ
  c⇒ □ □ = □
  c⇒ a b = a ⇒ b

  c∀ : Typ → Typ
  c∀ □ = □
  c∀ a = ∀· a

  -- Co-Heyting subtraction: componentwise removal with collapse
  _\\t_ : Typ → Typ → Typ
  τ \\t τ' with diag τ τ'
  ...       | kind□  = □
  ...       | kind* = □
  ...       | kindVar {m} {n} with m ≟ℕ n
  ...                         | yes _ = □
  ...                         | no  _ = ⟨ m ⟩
  (τ₁ + τ₂) \\t (τ₁' + τ₂') | kind+ = c+ (τ₁ \\t τ₁') (τ₂ \\t τ₂')
  (τ₁ × τ₂) \\t (τ₁' × τ₂') | kind× = c× (τ₁ \\t τ₁') (τ₂ \\t τ₂')
  (τ₁ ⇒ τ₂) \\t (τ₁' ⇒ τ₂') | kind⇒ = c⇒ (τ₁ \\t τ₁') (τ₂ \\t τ₂')
  (∀· τ)    \\t (∀· τ')      | kind∀ = c∀ (τ \\t τ')
  τ \\t τ'    | diff with τ ≟ □
  ...                 | yes _ = □
  ...                 | no  _ = τ

  -- Closure lemmas for collapse helpers
  c+-⊑ : ∀ {τ₁ τ₂} (a b : Typ) → a ⊑ τ₁ → b ⊑ τ₂ → c+ a b ⊑ τ₁ + τ₂
  c+-⊑ □       □       _   _  = ⊑□
  c+-⊑ □       *       p   q  = ⊑+ p q
  c+-⊑ □       ⟨ _ ⟩   p   q  = ⊑+ p q
  c+-⊑ □       (_ + _) p   q  = ⊑+ p q
  c+-⊑ □       (_ × _) p   q  = ⊑+ p q
  c+-⊑ □       (_ ⇒ _) p   q  = ⊑+ p q
  c+-⊑ □       (∀· _)  p   q  = ⊑+ p q
  c+-⊑ *       _       p   q  = ⊑+ p q
  c+-⊑ ⟨ _ ⟩   _       p   q  = ⊑+ p q
  c+-⊑ (_ + _) _       p   q  = ⊑+ p q
  c+-⊑ (_ × _) _       p   q  = ⊑+ p q
  c+-⊑ (_ ⇒ _) _       p   q  = ⊑+ p q
  c+-⊑ (∀· _)  _       p   q  = ⊑+ p q

  c×-⊑ : ∀ {τ₁ τ₂} (a b : Typ) → a ⊑ τ₁ → b ⊑ τ₂ → c× a b ⊑ τ₁ × τ₂
  c×-⊑ □       □       _   _  = ⊑□
  c×-⊑ □       *       p   q  = ⊑× p q
  c×-⊑ □       ⟨ _ ⟩   p   q  = ⊑× p q
  c×-⊑ □       (_ + _) p   q  = ⊑× p q
  c×-⊑ □       (_ × _) p   q  = ⊑× p q
  c×-⊑ □       (_ ⇒ _) p   q  = ⊑× p q
  c×-⊑ □       (∀· _)  p   q  = ⊑× p q
  c×-⊑ *       _       p   q  = ⊑× p q
  c×-⊑ ⟨ _ ⟩   _       p   q  = ⊑× p q
  c×-⊑ (_ + _) _       p   q  = ⊑× p q
  c×-⊑ (_ × _) _       p   q  = ⊑× p q
  c×-⊑ (_ ⇒ _) _       p   q  = ⊑× p q
  c×-⊑ (∀· _)  _       p   q  = ⊑× p q

  c⇒-⊑ : ∀ {τ₁ τ₂} (a b : Typ) → a ⊑ τ₁ → b ⊑ τ₂ → c⇒ a b ⊑ τ₁ ⇒ τ₂
  c⇒-⊑ □       □       _   _  = ⊑□
  c⇒-⊑ □       *       p   q  = ⊑⇒ p q
  c⇒-⊑ □       ⟨ _ ⟩   p   q  = ⊑⇒ p q
  c⇒-⊑ □       (_ + _) p   q  = ⊑⇒ p q
  c⇒-⊑ □       (_ × _) p   q  = ⊑⇒ p q
  c⇒-⊑ □       (_ ⇒ _) p   q  = ⊑⇒ p q
  c⇒-⊑ □       (∀· _)  p   q  = ⊑⇒ p q
  c⇒-⊑ *       _       p   q  = ⊑⇒ p q
  c⇒-⊑ ⟨ _ ⟩   _       p   q  = ⊑⇒ p q
  c⇒-⊑ (_ + _) _       p   q  = ⊑⇒ p q
  c⇒-⊑ (_ × _) _       p   q  = ⊑⇒ p q
  c⇒-⊑ (_ ⇒ _) _       p   q  = ⊑⇒ p q
  c⇒-⊑ (∀· _)  _       p   q  = ⊑⇒ p q

  c∀-⊑ : ∀ {τ} (a : Typ) → a ⊑ τ → c∀ a ⊑ ∀· τ
  c∀-⊑ □       _ = ⊑□
  c∀-⊑ *       p = ⊑∀ p
  c∀-⊑ ⟨ _ ⟩   p = ⊑∀ p
  c∀-⊑ (_ + _) p = ⊑∀ p
  c∀-⊑ (_ × _) p = ⊑∀ p
  c∀-⊑ (_ ⇒ _) p = ⊑∀ p
  c∀-⊑ (∀· _)  p = ⊑∀ p

  -- Inverse closure: c+ a b ⊑ τ₁ + τ₂ implies a ⊑ τ₁ ∧ b ⊑ τ₂ (similar for ×, ⇒, ∀)
  c+-⊑-inv : ∀ {τ₁ τ₂} (a b : Typ) → c+ a b ⊑ τ₁ + τ₂ → a ⊑ τ₁ ∧ b ⊑ τ₂
  c+-⊑-inv □       □       ⊑□            = ⊑□ , ⊑□
  c+-⊑-inv □       *       (⊑+ p q)      = p , q
  c+-⊑-inv □       ⟨ _ ⟩   (⊑+ p q)      = p , q
  c+-⊑-inv □       (_ + _) (⊑+ p q)      = p , q
  c+-⊑-inv □       (_ × _) (⊑+ p q)      = p , q
  c+-⊑-inv □       (_ ⇒ _) (⊑+ p q)      = p , q
  c+-⊑-inv □       (∀· _)  (⊑+ p q)      = p , q
  c+-⊑-inv *       _       (⊑+ p q)      = p , q
  c+-⊑-inv ⟨ _ ⟩   _       (⊑+ p q)      = p , q
  c+-⊑-inv (_ + _) _       (⊑+ p q)      = p , q
  c+-⊑-inv (_ × _) _       (⊑+ p q)      = p , q
  c+-⊑-inv (_ ⇒ _) _       (⊑+ p q)      = p , q
  c+-⊑-inv (∀· _)  _       (⊑+ p q)      = p , q

  c×-⊑-inv : ∀ {τ₁ τ₂} (a b : Typ) → c× a b ⊑ τ₁ × τ₂ → a ⊑ τ₁ ∧ b ⊑ τ₂
  c×-⊑-inv □       □       ⊑□            = ⊑□ , ⊑□
  c×-⊑-inv □       *       (⊑× p q)      = p , q
  c×-⊑-inv □       ⟨ _ ⟩   (⊑× p q)      = p , q
  c×-⊑-inv □       (_ + _) (⊑× p q)      = p , q
  c×-⊑-inv □       (_ × _) (⊑× p q)      = p , q
  c×-⊑-inv □       (_ ⇒ _) (⊑× p q)      = p , q
  c×-⊑-inv □       (∀· _)  (⊑× p q)      = p , q
  c×-⊑-inv *       _       (⊑× p q)      = p , q
  c×-⊑-inv ⟨ _ ⟩   _       (⊑× p q)      = p , q
  c×-⊑-inv (_ + _) _       (⊑× p q)      = p , q
  c×-⊑-inv (_ × _) _       (⊑× p q)      = p , q
  c×-⊑-inv (_ ⇒ _) _       (⊑× p q)      = p , q
  c×-⊑-inv (∀· _)  _       (⊑× p q)      = p , q

  c⇒-⊑-inv : ∀ {τ₁ τ₂} (a b : Typ) → c⇒ a b ⊑ τ₁ ⇒ τ₂ → a ⊑ τ₁ ∧ b ⊑ τ₂
  c⇒-⊑-inv □       □       ⊑□            = ⊑□ , ⊑□
  c⇒-⊑-inv □       *       (⊑⇒ p q)      = p , q
  c⇒-⊑-inv □       ⟨ _ ⟩   (⊑⇒ p q)      = p , q
  c⇒-⊑-inv □       (_ + _) (⊑⇒ p q)      = p , q
  c⇒-⊑-inv □       (_ × _) (⊑⇒ p q)      = p , q
  c⇒-⊑-inv □       (_ ⇒ _) (⊑⇒ p q)      = p , q
  c⇒-⊑-inv □       (∀· _)  (⊑⇒ p q)      = p , q
  c⇒-⊑-inv *       _       (⊑⇒ p q)      = p , q
  c⇒-⊑-inv ⟨ _ ⟩   _       (⊑⇒ p q)      = p , q
  c⇒-⊑-inv (_ + _) _       (⊑⇒ p q)      = p , q
  c⇒-⊑-inv (_ × _) _       (⊑⇒ p q)      = p , q
  c⇒-⊑-inv (_ ⇒ _) _       (⊑⇒ p q)      = p , q
  c⇒-⊑-inv (∀· _)  _       (⊑⇒ p q)      = p , q

  c∀-⊑-inv : ∀ {τ} (a : Typ) → c∀ a ⊑ ∀· τ → a ⊑ τ
  c∀-⊑-inv □       ⊑□      = ⊑□
  c∀-⊑-inv *       (⊑∀ p)  = p
  c∀-⊑-inv ⟨ _ ⟩   (⊑∀ p)  = p
  c∀-⊑-inv (_ + _) (⊑∀ p)  = p
  c∀-⊑-inv (_ × _) (⊑∀ p)  = p
  c∀-⊑-inv (_ ⇒ _) (⊑∀ p)  = p
  c∀-⊑-inv (∀· _)  (⊑∀ p)  = p

  infixl 7 _\\t_

  -- Subtraction is below first argument: τ₁ \\t τ₂ ⊑ τ₁
  \\t-⊑₁ : ∀ τ₁ τ₂ → τ₁ \\t τ₂ ⊑ τ₁
  \\t-⊑₁ τ₁         τ₂          with diag τ₁ τ₂
  \\t-⊑₁ □          □           | kind□ = ⊑□
  \\t-⊑₁ *          *           | kind* = ⊑□
  \\t-⊑₁ ⟨ m ⟩      ⟨ n ⟩       | kindVar with m ≟ℕ n
  ...                                       | yes _ = ⊑□
  ...                                       | no  _ = ⊑Var
  \\t-⊑₁ (τ₁ + τ₂)  (τ₁' + τ₂') | kind+ = c+-⊑ (τ₁ \\t τ₁') (τ₂ \\t τ₂') (\\t-⊑₁ τ₁ τ₁') (\\t-⊑₁ τ₂ τ₂')
  \\t-⊑₁ (τ₁ × τ₂)  (τ₁' × τ₂') | kind× = c×-⊑ (τ₁ \\t τ₁') (τ₂ \\t τ₂') (\\t-⊑₁ τ₁ τ₁') (\\t-⊑₁ τ₂ τ₂')
  \\t-⊑₁ (τ₁ ⇒ τ₂)  (τ₁' ⇒ τ₂') | kind⇒ = c⇒-⊑ (τ₁ \\t τ₁') (τ₂ \\t τ₂') (\\t-⊑₁ τ₁ τ₁') (\\t-⊑₁ τ₂ τ₂')
  \\t-⊑₁ (∀· τ)     (∀· τ')     | kind∀ = c∀-⊑ (τ \\t τ') (\\t-⊑₁ τ τ')
  \\t-⊑₁ τ₁         τ₂          | diff with τ₁ ≟ □
  ...                                       | yes refl = ⊑□
  ...                                       | no  _    = ⊑.refl

  -- Closure: subtraction of slices stays in the slice lattice
  \\t-closure : ∀ {τ₁ τ₂ τ} → τ₁ ⊑ τ → τ₂ ⊑ τ → τ₁ \\t τ₂ ⊑ τ
  \\t-closure p _ = ⊑.trans (\\t-⊑₁ _ _) p

  -- Inversions of collapse helpers: c+ a b ≡ □ implies a ≡ □ ∧ b ≡ □
  c+-≡-□ : ∀ a b → c+ a b ≡ □ → a ≡ □ ∧ b ≡ □
  c+-≡-□ □ □ refl    = refl , refl
  c+-≡-□ □ *       ()
  c+-≡-□ □ ⟨ _ ⟩    ()
  c+-≡-□ □ (_ + _)  ()
  c+-≡-□ □ (_ × _)  ()
  c+-≡-□ □ (_ ⇒ _)  ()
  c+-≡-□ □ (∀· _)   ()
  c+-≡-□ * _        ()
  c+-≡-□ ⟨ _ ⟩ _    ()
  c+-≡-□ (_ + _) _  ()
  c+-≡-□ (_ × _) _  ()
  c+-≡-□ (_ ⇒ _) _  ()
  c+-≡-□ (∀· _) _   ()

  c×-≡-□ : ∀ a b → c× a b ≡ □ → a ≡ □ ∧ b ≡ □
  c×-≡-□ □ □ refl    = refl , refl
  c×-≡-□ □ *       ()
  c×-≡-□ □ ⟨ _ ⟩    ()
  c×-≡-□ □ (_ + _)  ()
  c×-≡-□ □ (_ × _)  ()
  c×-≡-□ □ (_ ⇒ _)  ()
  c×-≡-□ □ (∀· _)   ()
  c×-≡-□ * _        ()
  c×-≡-□ ⟨ _ ⟩ _    ()
  c×-≡-□ (_ + _) _  ()
  c×-≡-□ (_ × _) _  ()
  c×-≡-□ (_ ⇒ _) _  ()
  c×-≡-□ (∀· _) _   ()

  c⇒-≡-□ : ∀ a b → c⇒ a b ≡ □ → a ≡ □ ∧ b ≡ □
  c⇒-≡-□ □ □ refl    = refl , refl
  c⇒-≡-□ □ *       ()
  c⇒-≡-□ □ ⟨ _ ⟩    ()
  c⇒-≡-□ □ (_ + _)  ()
  c⇒-≡-□ □ (_ × _)  ()
  c⇒-≡-□ □ (_ ⇒ _)  ()
  c⇒-≡-□ □ (∀· _)   ()
  c⇒-≡-□ * _        ()
  c⇒-≡-□ ⟨ _ ⟩ _    ()
  c⇒-≡-□ (_ + _) _  ()
  c⇒-≡-□ (_ × _) _  ()
  c⇒-≡-□ (_ ⇒ _) _  ()
  c⇒-≡-□ (∀· _) _   ()

  c∀-≡-□ : ∀ a → c∀ a ≡ □ → a ≡ □
  c∀-≡-□ □ refl    = refl
  c∀-≡-□ *       ()
  c∀-≡-□ ⟨ _ ⟩    ()
  c∀-≡-□ (_ + _)  ()
  c∀-≡-□ (_ × _)  ()
  c∀-≡-□ (_ ⇒ _)  ()
  c∀-≡-□ (∀· _)   ()

  -- Bottom-absorption for subtraction
  \\t-□ₗ : ∀ τ → □ \\t τ ≡ □
  \\t-□ₗ τ with diag □ τ
  ... | kind□ = refl
  ... | diff  = refl

  \\t-□ᵣ : ∀ τ → τ ≢ □ → τ \\t □ ≡ τ
  \\t-□ᵣ □       neq = ⊥-elim (neq refl)
  \\t-□ᵣ *       _   = refl
  \\t-□ᵣ ⟨ _ ⟩   _   = refl
  \\t-□ᵣ (_ + _) _   = refl
  \\t-□ᵣ (_ × _) _   = refl
  \\t-□ᵣ (_ ⇒ _) _   = refl
  \\t-□ᵣ (∀· _)  _   = refl

  -- Subtraction trivializes exactly when first ⊑ second
  ⊑⇒\\t-≡-□ : ∀ {τ τ'} → τ ⊑ τ' → τ \\t τ' ≡ □
  ⊑⇒\\t-≡-□ {τ' = τ'} ⊑□ = \\t-□ₗ τ'
  ⊑⇒\\t-≡-□ ⊑*           = refl
  ⊑⇒\\t-≡-□ (⊑Var {n}) with n ≟ℕ n
  ... | yes _     = refl
  ... | no contra = ⊥-elim (contra refl)
  ⊑⇒\\t-≡-□ (⊑+ p₁ p₂) rewrite ⊑⇒\\t-≡-□ p₁ | ⊑⇒\\t-≡-□ p₂ = refl
  ⊑⇒\\t-≡-□ (⊑× p₁ p₂) rewrite ⊑⇒\\t-≡-□ p₁ | ⊑⇒\\t-≡-□ p₂ = refl
  ⊑⇒\\t-≡-□ (⊑⇒ p₁ p₂) rewrite ⊑⇒\\t-≡-□ p₁ | ⊑⇒\\t-≡-□ p₂ = refl
  ⊑⇒\\t-≡-□ (⊑∀ p)     rewrite ⊑⇒\\t-≡-□ p              = refl

  \\t-≡-□⇒⊑ : ∀ τ τ' → τ \\t τ' ≡ □ → τ ⊑ τ'
  \\t-≡-□⇒⊑ τ τ' h with diag τ τ'
  \\t-≡-□⇒⊑ □ □ refl | kind□ = ⊑□
  \\t-≡-□⇒⊑ * * refl | kind* = ⊑*
  \\t-≡-□⇒⊑ ⟨ m ⟩ ⟨ n ⟩ h | kindVar with m ≟ℕ n
  ... | yes refl = ⊑Var
  ... | no  _    = case h of λ ()
    where open import Function using (case_of_)
  \\t-≡-□⇒⊑ (τ₁ + τ₂) (τ₁' + τ₂') h | kind+
    with c+-≡-□ (τ₁ \\t τ₁') (τ₂ \\t τ₂') h
  ... | eq₁ , eq₂ = ⊑+ (\\t-≡-□⇒⊑ τ₁ τ₁' eq₁) (\\t-≡-□⇒⊑ τ₂ τ₂' eq₂)
  \\t-≡-□⇒⊑ (τ₁ × τ₂) (τ₁' × τ₂') h | kind×
    with c×-≡-□ (τ₁ \\t τ₁') (τ₂ \\t τ₂') h
  ... | eq₁ , eq₂ = ⊑× (\\t-≡-□⇒⊑ τ₁ τ₁' eq₁) (\\t-≡-□⇒⊑ τ₂ τ₂' eq₂)
  \\t-≡-□⇒⊑ (τ₁ ⇒ τ₂) (τ₁' ⇒ τ₂') h | kind⇒
    with c⇒-≡-□ (τ₁ \\t τ₁') (τ₂ \\t τ₂') h
  ... | eq₁ , eq₂ = ⊑⇒ (\\t-≡-□⇒⊑ τ₁ τ₁' eq₁) (\\t-≡-□⇒⊑ τ₂ τ₂' eq₂)
  \\t-≡-□⇒⊑ (∀· τ) (∀· τ') h | kind∀ =
    ⊑∀ (\\t-≡-□⇒⊑ τ τ' (c∀-≡-□ (τ \\t τ') h))
  \\t-≡-□⇒⊑ τ τ' h | diff with τ ≟ □
  ... | yes refl = ⊑□
  ... | no  neq  = ⊥-elim (neq h)

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

-- Componentwise complement for type slices
typ-¬ₛ : ∀ {τ : Typ} → ⌊ τ ⌋ → ⌊ τ ⌋
typ-¬ₛ {□}       _                             = □ isSlice ⊑□
typ-¬ₛ {*}       (□ isSlice ⊑□)                = * isSlice ⊑*
typ-¬ₛ {*}       (* isSlice ⊑*)                = □ isSlice ⊑□
typ-¬ₛ {⟨ _ ⟩}   (□ isSlice ⊑□)                = ⟨ _ ⟩ isSlice ⊑Var
typ-¬ₛ {⟨ _ ⟩}   (._ isSlice ⊑Var)             = □ isSlice ⊑□
typ-¬ₛ {τ₁ + τ₂} (□ isSlice ⊑□)                = (τ₁ + τ₂) isSlice ⊑+ ⊑.refl ⊑.refl
typ-¬ₛ {τ₁ + τ₂} ((_ + _) isSlice ⊑+ p₁ p₂)   =
  let ¬s₁ = typ-¬ₛ (_ isSlice p₁)
      ¬s₂ = typ-¬ₛ (_ isSlice p₂)
  in (¬s₁ .↓ + ¬s₂ .↓) isSlice ⊑+ (¬s₁ .proof) (¬s₂ .proof)
typ-¬ₛ {τ₁ × τ₂} (□ isSlice ⊑□)                = (τ₁ × τ₂) isSlice ⊑× ⊑.refl ⊑.refl
typ-¬ₛ {τ₁ × τ₂} ((_ × _) isSlice ⊑× p₁ p₂)   =
  let ¬s₁ = typ-¬ₛ (_ isSlice p₁)
      ¬s₂ = typ-¬ₛ (_ isSlice p₂)
  in (¬s₁ .↓ × ¬s₂ .↓) isSlice ⊑× (¬s₁ .proof) (¬s₂ .proof)
typ-¬ₛ {τ₁ ⇒ τ₂} (□ isSlice ⊑□)                = (τ₁ ⇒ τ₂) isSlice ⊑⇒ ⊑.refl ⊑.refl
typ-¬ₛ {τ₁ ⇒ τ₂} ((_ ⇒ _) isSlice ⊑⇒ p₁ p₂)   =
  let ¬s₁ = typ-¬ₛ (_ isSlice p₁)
      ¬s₂ = typ-¬ₛ (_ isSlice p₂)
  in (¬s₁ .↓ ⇒ ¬s₂ .↓) isSlice ⊑⇒ (¬s₁ .proof) (¬s₂ .proof)
typ-¬ₛ {∀· τ}    (□ isSlice ⊑□)                = (∀· τ) isSlice ⊑∀ ⊑.refl
typ-¬ₛ {∀· τ}    ((∀· s) isSlice ⊑∀ p)         =
  let ¬s = typ-¬ₛ (s isSlice p)
  in (∀· (¬s .↓)) isSlice ⊑∀ (¬s .proof)

typ-⊔ₛ-complement : ∀ {τ : Typ} (s : ⌊ τ ⌋) → _≈ₛ_ (s ⊔ₛ typ-¬ₛ s) (⊤ₛ {a = τ})
typ-⊔ₛ-complement {□}       (□ isSlice ⊑□)              = refl
typ-⊔ₛ-complement {*}       (□ isSlice ⊑□)              = refl
typ-⊔ₛ-complement {*}       (* isSlice ⊑*)              = refl
typ-⊔ₛ-complement {⟨ _ ⟩}   (□ isSlice ⊑□)              = refl
typ-⊔ₛ-complement {⟨ _ ⟩}   (._ isSlice ⊑Var)           = refl
typ-⊔ₛ-complement {τ₁ + τ₂} (□ isSlice ⊑□)              = refl
typ-⊔ₛ-complement {τ₁ + τ₂} ((τ₁' + τ₂') isSlice ⊑+ p₁ p₂) =
  let ¬s₁ = typ-¬ₛ (τ₁' isSlice p₁)
      ¬s₂ = typ-¬ₛ (τ₂' isSlice p₂)
  in cong₂ _+_ (typ-⊔ₛ-complement (τ₁' isSlice p₁)) (typ-⊔ₛ-complement (τ₂' isSlice p₂))
typ-⊔ₛ-complement {τ₁ × τ₂} (□ isSlice ⊑□)              = refl
typ-⊔ₛ-complement {τ₁ × τ₂} ((τ₁' × τ₂') isSlice ⊑× p₁ p₂) =
  let ¬s₁ = typ-¬ₛ (τ₁' isSlice p₁)
      ¬s₂ = typ-¬ₛ (τ₂' isSlice p₂)
  in cong₂ _×_ (typ-⊔ₛ-complement (τ₁' isSlice p₁)) (typ-⊔ₛ-complement (τ₂' isSlice p₂))
typ-⊔ₛ-complement {τ₁ ⇒ τ₂} (□ isSlice ⊑□)              = refl
typ-⊔ₛ-complement {τ₁ ⇒ τ₂} ((τ₁' ⇒ τ₂') isSlice ⊑⇒ p₁ p₂) =
  let ¬s₁ = typ-¬ₛ (τ₁' isSlice p₁)
      ¬s₂ = typ-¬ₛ (τ₂' isSlice p₂)
  in cong₂ _⇒_ (typ-⊔ₛ-complement (τ₁' isSlice p₁)) (typ-⊔ₛ-complement (τ₂' isSlice p₂))
typ-⊔ₛ-complement {∀· τ}    (□ isSlice ⊑□)              = refl
typ-⊔ₛ-complement {∀· τ}    ((∀· τ') isSlice ⊑∀ p)       =
  cong ∀· (typ-⊔ₛ-complement (τ' isSlice p))

typ-¬ₛ-anti : ∀ {τ : Typ} {s₁ s₂ : ⌊ τ ⌋} → s₁ ⊑ₛ s₂ → typ-¬ₛ s₂ ⊑ₛ typ-¬ₛ s₁
typ-¬ₛ-anti {□}       {□ isSlice ⊑□}                {□ isSlice ⊑□}                ⊑□ = ⊑□
typ-¬ₛ-anti {*}       {□ isSlice ⊑□}                {□ isSlice ⊑□}                ⊑□ = ⊑*
typ-¬ₛ-anti {*}       {□ isSlice ⊑□}                {* isSlice ⊑*}                ⊑□ = ⊑□
typ-¬ₛ-anti {*}       {* isSlice ⊑*}                {* isSlice ⊑*}                ⊑* = ⊑□
typ-¬ₛ-anti {⟨ _ ⟩}   {□ isSlice ⊑□}                {□ isSlice ⊑□}                ⊑□ = ⊑Var
typ-¬ₛ-anti {⟨ _ ⟩}   {□ isSlice ⊑□}                {._ isSlice ⊑Var}             ⊑□ = ⊑□
typ-¬ₛ-anti {⟨ _ ⟩}   {._ isSlice ⊑Var}             {._ isSlice ⊑Var}             ⊑Var = ⊑□
typ-¬ₛ-anti {τ₁ + τ₂} {□ isSlice ⊑□}                {□ isSlice ⊑□}                ⊑□ =
  ⊑+ ⊑.refl ⊑.refl
typ-¬ₛ-anti {τ₁ + τ₂} {□ isSlice ⊑□}                {(_ + _) isSlice ⊑+ q₁ q₂}   ⊑□ =
  ⊑+ (typ-¬ₛ (_ isSlice q₁) .proof) (typ-¬ₛ (_ isSlice q₂) .proof)
typ-¬ₛ-anti {τ₁ + τ₂} {(_ + _) isSlice ⊑+ p₁ p₂}   {(_ + _) isSlice ⊑+ q₁ q₂}   (⊑+ h₁ h₂) =
  ⊑+ (typ-¬ₛ-anti {s₁ = _ isSlice p₁} {_ isSlice q₁} h₁)
     (typ-¬ₛ-anti {s₁ = _ isSlice p₂} {_ isSlice q₂} h₂)
typ-¬ₛ-anti {τ₁ × τ₂} {□ isSlice ⊑□}                {□ isSlice ⊑□}                ⊑□ =
  ⊑× ⊑.refl ⊑.refl
typ-¬ₛ-anti {τ₁ × τ₂} {□ isSlice ⊑□}                {(_ × _) isSlice ⊑× q₁ q₂}   ⊑□ =
  ⊑× (typ-¬ₛ (_ isSlice q₁) .proof) (typ-¬ₛ (_ isSlice q₂) .proof)
typ-¬ₛ-anti {τ₁ × τ₂} {(_ × _) isSlice ⊑× p₁ p₂}   {(_ × _) isSlice ⊑× q₁ q₂}   (⊑× h₁ h₂) =
  ⊑× (typ-¬ₛ-anti {s₁ = _ isSlice p₁} {_ isSlice q₁} h₁)
     (typ-¬ₛ-anti {s₁ = _ isSlice p₂} {_ isSlice q₂} h₂)
typ-¬ₛ-anti {τ₁ ⇒ τ₂} {□ isSlice ⊑□}                {□ isSlice ⊑□}                ⊑□ =
  ⊑⇒ ⊑.refl ⊑.refl
typ-¬ₛ-anti {τ₁ ⇒ τ₂} {□ isSlice ⊑□}                {(_ ⇒ _) isSlice ⊑⇒ q₁ q₂}   ⊑□ =
  ⊑⇒ (typ-¬ₛ (_ isSlice q₁) .proof) (typ-¬ₛ (_ isSlice q₂) .proof)
typ-¬ₛ-anti {τ₁ ⇒ τ₂} {(_ ⇒ _) isSlice ⊑⇒ p₁ p₂}   {(_ ⇒ _) isSlice ⊑⇒ q₁ q₂}   (⊑⇒ h₁ h₂) =
  ⊑⇒ (typ-¬ₛ-anti {s₁ = _ isSlice p₁} {_ isSlice q₁} h₁)
     (typ-¬ₛ-anti {s₁ = _ isSlice p₂} {_ isSlice q₂} h₂)
typ-¬ₛ-anti {∀· τ}    {□ isSlice ⊑□}                {□ isSlice ⊑□}                ⊑□ =
  ⊑∀ ⊑.refl
typ-¬ₛ-anti {∀· τ}    {□ isSlice ⊑□}                {(∀· _) isSlice ⊑∀ q}         ⊑□ =
  ⊑∀ (typ-¬ₛ (_ isSlice q) .proof)
typ-¬ₛ-anti {∀· τ}    {(∀· _) isSlice ⊑∀ p}         {(∀· _) isSlice ⊑∀ q}         (⊑∀ h) =
  ⊑∀ (typ-¬ₛ-anti {s₁ = _ isSlice p} {_ isSlice q} h)

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
    }

-- Heyting implication on type slices
typ-⇨ₛ : ∀ {τ : Typ} → ⌊ τ ⌋ → ⌊ τ ⌋ → ⌊ τ ⌋
typ-⇨ₛ               (□ isSlice ⊑□)     _                   = ⊤ₛ
typ-⇨ₛ               _                  (□ isSlice ⊑□)      = ↑ ⊑□
typ-⇨ₛ {*}           (* isSlice ⊑*)     (* isSlice ⊑*)      = ⊤ₛ
typ-⇨ₛ {⟨ _ ⟩}       (_ isSlice ⊑Var)   (_ isSlice ⊑Var)    = ⊤ₛ
typ-⇨ₛ {τ₁ + τ₂}     (_ isSlice ⊑+ p₁ p₂) (_ isSlice ⊑+ q₁ q₂) =
  let r₁ = typ-⇨ₛ (↑ p₁) (↑ q₁)
      r₂ = typ-⇨ₛ (↑ p₂) (↑ q₂)
  in ↑ (⊑+ (r₁ .proof) (r₂ .proof))
typ-⇨ₛ {τ₁ × τ₂}     (_ isSlice ⊑× p₁ p₂) (_ isSlice ⊑× q₁ q₂) =
  let r₁ = typ-⇨ₛ (↑ p₁) (↑ q₁)
      r₂ = typ-⇨ₛ (↑ p₂) (↑ q₂)
  in ↑ (⊑× (r₁ .proof) (r₂ .proof))
typ-⇨ₛ {τ₁ ⇒ τ₂}     (_ isSlice ⊑⇒ p₁ p₂) (_ isSlice ⊑⇒ q₁ q₂) =
  let r₁ = typ-⇨ₛ (↑ p₁) (↑ q₁)
      r₂ = typ-⇨ₛ (↑ p₂) (↑ q₂)
  in ↑ (⊑⇒ (r₁ .proof) (r₂ .proof))
typ-⇨ₛ {∀· τ}        (_ isSlice ⊑∀ p) (_ isSlice ⊑∀ q) =
  let r = typ-⇨ₛ (↑ p) (↑ q)
  in ↑ (⊑∀ (r .proof))

-- Co-Heyting subtraction on type slices (lifted from _\\t_)
typ-\\ₛ : ∀ {τ : Typ} → ⌊ τ ⌋ → ⌊ τ ⌋ → ⌊ τ ⌋
typ-\\ₛ s₁ s₂ = s₁ .↓ \\t s₂ .↓ isSlice \\t-closure (s₁ .proof) (s₂ .proof)

-- Exponential adjunctions for the bi-Heyting structure on type slices
private
  -- Heyting adjunction: forward direction (curry)
  ⇨-curry : ∀ {τ} (w x y : ⌊ τ ⌋) → w ⊓ₛ x ⊑ₛ y → w ⊑ₛ (typ-⇨ₛ x y)
  ⇨-curry (□ isSlice ⊑□) _ _ _ = ⊑□
  ⇨-curry w (□ isSlice ⊑□) _ _ = ⊤ₛ-max w
  ⇨-curry {*} (* isSlice ⊑*) (* isSlice ⊑*) (* isSlice ⊑*) _ = ⊑*
  ⇨-curry {⟨ n ⟩} (_ isSlice ⊑Var) (_ isSlice ⊑Var) (_ isSlice ⊑Var) _ = ⊑Var
  ⇨-curry {⟨ n ⟩} (_ isSlice ⊑Var) (_ isSlice ⊑Var) (□ isSlice ⊑□) h with n ≟ℕ n
  ... | yes refl  = case h of λ ()
  ... | no contra = ⊥-elim (contra refl)
  ⇨-curry {_ + _} (_ isSlice ⊑+ p₁ p₂) (_ isSlice ⊑+ q₁ q₂) (_ isSlice ⊑+ r₁ r₂) (⊑+ h₁ h₂) =
    ⊑+ (⇨-curry (_ isSlice p₁) (_ isSlice q₁) (_ isSlice r₁) h₁)
       (⇨-curry (_ isSlice p₂) (_ isSlice q₂) (_ isSlice r₂) h₂)
  ⇨-curry {_ × _} (_ isSlice ⊑× p₁ p₂) (_ isSlice ⊑× q₁ q₂) (_ isSlice ⊑× r₁ r₂) (⊑× h₁ h₂) =
    ⊑× (⇨-curry (_ isSlice p₁) (_ isSlice q₁) (_ isSlice r₁) h₁)
       (⇨-curry (_ isSlice p₂) (_ isSlice q₂) (_ isSlice r₂) h₂)
  ⇨-curry {_ ⇒ _} (_ isSlice ⊑⇒ p₁ p₂) (_ isSlice ⊑⇒ q₁ q₂) (_ isSlice ⊑⇒ r₁ r₂) (⊑⇒ h₁ h₂) =
    ⊑⇒ (⇨-curry (_ isSlice p₁) (_ isSlice q₁) (_ isSlice r₁) h₁)
       (⇨-curry (_ isSlice p₂) (_ isSlice q₂) (_ isSlice r₂) h₂)
  ⇨-curry {∀· _} (_ isSlice ⊑∀ p) (_ isSlice ⊑∀ q) (_ isSlice ⊑∀ r) (⊑∀ h) =
    ⊑∀ (⇨-curry (_ isSlice p) (_ isSlice q) (_ isSlice r) h)

  -- Heyting adjunction: reverse direction (uncurry)
  ⇨-uncurry : ∀ {τ} (w x y : ⌊ τ ⌋) → w ⊑ₛ (typ-⇨ₛ x y) → w ⊓ₛ x ⊑ₛ y
  ⇨-uncurry (□ isSlice ⊑□) x y _ rewrite □⊓-absorb (x .↓) = ⊑□
  ⇨-uncurry w (□ isSlice ⊑□) y _ rewrite ⊓□-absorb (w .↓) = ⊑□
  ⇨-uncurry {*} (* isSlice ⊑*) (* isSlice ⊑*) (* isSlice ⊑*) _ = ⊑*
  ⇨-uncurry {⟨ n ⟩} (_ isSlice ⊑Var) (_ isSlice ⊑Var) (_ isSlice ⊑Var) _ with n ≟ℕ n
  ... | yes refl  = ⊑Var
  ... | no contra = ⊥-elim (contra refl)
  ⇨-uncurry {_ + _} (_ isSlice ⊑+ p₁ p₂) (_ isSlice ⊑+ q₁ q₂) (_ isSlice ⊑+ r₁ r₂) (⊑+ h₁ h₂) =
    ⊑+ (⇨-uncurry (_ isSlice p₁) (_ isSlice q₁) (_ isSlice r₁) h₁)
       (⇨-uncurry (_ isSlice p₂) (_ isSlice q₂) (_ isSlice r₂) h₂)
  ⇨-uncurry {_ × _} (_ isSlice ⊑× p₁ p₂) (_ isSlice ⊑× q₁ q₂) (_ isSlice ⊑× r₁ r₂) (⊑× h₁ h₂) =
    ⊑× (⇨-uncurry (_ isSlice p₁) (_ isSlice q₁) (_ isSlice r₁) h₁)
       (⇨-uncurry (_ isSlice p₂) (_ isSlice q₂) (_ isSlice r₂) h₂)
  ⇨-uncurry {_ ⇒ _} (_ isSlice ⊑⇒ p₁ p₂) (_ isSlice ⊑⇒ q₁ q₂) (_ isSlice ⊑⇒ r₁ r₂) (⊑⇒ h₁ h₂) =
    ⊑⇒ (⇨-uncurry (_ isSlice p₁) (_ isSlice q₁) (_ isSlice r₁) h₁)
       (⇨-uncurry (_ isSlice p₂) (_ isSlice q₂) (_ isSlice r₂) h₂)
  ⇨-uncurry {∀· _} (_ isSlice ⊑∀ p) (_ isSlice ⊑∀ q) (_ isSlice ⊑∀ r) (⊑∀ h) =
    ⊑∀ (⇨-uncurry (_ isSlice p) (_ isSlice q) (_ isSlice r) h)

typ-⇨-exponential : ∀ {τ : Typ} → Exponential (_⊑ₛ_ {a = τ}) _⊓ₛ_ (typ-⇨ₛ {τ})
typ-⇨-exponential w x y = ⇨-curry w x y , ⇨-uncurry w x y

private
  -- Co-Heyting adjunction: forward direction (curry)
  -- y ⊑ w ⊔ x → y \\ x ⊑ w
  \\-curry : ∀ {τ} (w x y : ⌊ τ ⌋) → y ⊑ₛ (w ⊔ₛ x) → typ-\\ₛ y x ⊑ₛ w
  -- y = □: □ \\ x = □ ⊑ w
  \\-curry _ x (□ isSlice ⊑□) _ rewrite \\t-□ₗ (x .↓) = ⊑□
  -- w = □ (y non-□): hyp y ⊑ □ ⊔ x = x; goal y \\ x ⊑ □
  \\-curry (□ isSlice ⊑□) x y hyp
    rewrite ⊔-identityₗ (x .↓) | ⊑⇒\\t-≡-□ hyp = ⊑□
  -- x = □ (y, w non-□): hyp y ⊑ w ⊔ □ = w; goal y \\ □ = y ⊑ w
  \\-curry w (□ isSlice ⊑□) (* isSlice ⊑*) hyp
    rewrite ⊔-identityᵣ (w .↓) = hyp
  \\-curry {⟨ n ⟩} w (□ isSlice ⊑□) (_ isSlice ⊑Var) hyp
    rewrite ⊔-identityᵣ (w .↓) = hyp
  \\-curry w (□ isSlice ⊑□) ((_ + _) isSlice ⊑+ _ _) hyp
    rewrite ⊔-identityᵣ (w .↓) = hyp
  \\-curry w (□ isSlice ⊑□) ((_ × _) isSlice ⊑× _ _) hyp
    rewrite ⊔-identityᵣ (w .↓) = hyp
  \\-curry w (□ isSlice ⊑□) ((_ ⇒ _) isSlice ⊑⇒ _ _) hyp
    rewrite ⊔-identityᵣ (w .↓) = hyp
  \\-curry w (□ isSlice ⊑□) ((∀· _) isSlice ⊑∀ _) hyp
    rewrite ⊔-identityᵣ (w .↓) = hyp
  -- atoms: y = w = x = same atom (handled either via above ⊑□ cases or here)
  \\-curry {*} (* isSlice ⊑*) (* isSlice ⊑*) (* isSlice ⊑*) _ = ⊑□
  \\-curry {⟨ n ⟩} (_ isSlice ⊑Var) (_ isSlice ⊑Var) (_ isSlice ⊑Var) _ with n ≟ℕ n
  ... | yes refl  = ⊑□
  ... | no contra = ⊥-elim (contra refl)
  -- compound: recurse via c+-⊑/c×-⊑/c⇒-⊑/c∀-⊑
  \\-curry {_ + _} (_ isSlice ⊑+ r₁ r₂) (_ isSlice ⊑+ q₁ q₂) (_ isSlice ⊑+ p₁ p₂) (⊑+ h₁ h₂) =
    c+-⊑ _ _
      (\\-curry (_ isSlice r₁) (_ isSlice q₁) (_ isSlice p₁) h₁)
      (\\-curry (_ isSlice r₂) (_ isSlice q₂) (_ isSlice p₂) h₂)
  \\-curry {_ × _} (_ isSlice ⊑× r₁ r₂) (_ isSlice ⊑× q₁ q₂) (_ isSlice ⊑× p₁ p₂) (⊑× h₁ h₂) =
    c×-⊑ _ _
      (\\-curry (_ isSlice r₁) (_ isSlice q₁) (_ isSlice p₁) h₁)
      (\\-curry (_ isSlice r₂) (_ isSlice q₂) (_ isSlice p₂) h₂)
  \\-curry {_ ⇒ _} (_ isSlice ⊑⇒ r₁ r₂) (_ isSlice ⊑⇒ q₁ q₂) (_ isSlice ⊑⇒ p₁ p₂) (⊑⇒ h₁ h₂) =
    c⇒-⊑ _ _
      (\\-curry (_ isSlice r₁) (_ isSlice q₁) (_ isSlice p₁) h₁)
      (\\-curry (_ isSlice r₂) (_ isSlice q₂) (_ isSlice p₂) h₂)
  \\-curry {∀· _} (_ isSlice ⊑∀ r) (_ isSlice ⊑∀ q) (_ isSlice ⊑∀ p) (⊑∀ h) =
    c∀-⊑ _
      (\\-curry (_ isSlice r) (_ isSlice q) (_ isSlice p) h)

  -- Helper: invert ⊑ □ to extract the equality
  ⊑□⇒≡□ : ∀ {α} → α ⊑t □ → α ≡ □
  ⊑□⇒≡□ ⊑□ = refl

  -- Co-Heyting adjunction: reverse direction (uncurry)
  -- y \\ x ⊑ w → y ⊑ w ⊔ x
  \\-uncurry : ∀ {τ} (w x y : ⌊ τ ⌋) → typ-\\ₛ y x ⊑ₛ w → y ⊑ₛ (w ⊔ₛ x)
  -- y = □
  \\-uncurry _ _ (□ isSlice ⊑□) _ = ⊑□
  -- x = □ (y non-□): hyp y \\ □ = y ⊑ w; goal y ⊑ w ⊔ □ = w
  \\-uncurry w (□ isSlice ⊑□) (* isSlice ⊑*) hyp
    rewrite ⊔-identityᵣ (w .↓) = hyp
  \\-uncurry {⟨ n ⟩} w (□ isSlice ⊑□) (_ isSlice ⊑Var) hyp
    rewrite ⊔-identityᵣ (w .↓) = hyp
  \\-uncurry w (□ isSlice ⊑□) ((_ + _) isSlice ⊑+ _ _) hyp
    rewrite ⊔-identityᵣ (w .↓) = hyp
  \\-uncurry w (□ isSlice ⊑□) ((_ × _) isSlice ⊑× _ _) hyp
    rewrite ⊔-identityᵣ (w .↓) = hyp
  \\-uncurry w (□ isSlice ⊑□) ((_ ⇒ _) isSlice ⊑⇒ _ _) hyp
    rewrite ⊔-identityᵣ (w .↓) = hyp
  \\-uncurry w (□ isSlice ⊑□) ((∀· _) isSlice ⊑∀ _) hyp
    rewrite ⊔-identityᵣ (w .↓) = hyp
  -- w = □ (y, x non-□): hyp y \\ x ≡ □; goal y ⊑ □ ⊔ x = x
  \\-uncurry (□ isSlice ⊑□) x y hyp
    rewrite ⊔-identityₗ (x .↓) = \\t-≡-□⇒⊑ (y .↓) (x .↓) (⊑□⇒≡□ hyp)
  -- atoms: y = w = x = same atom, all non-□
  \\-uncurry {*} (* isSlice ⊑*) (* isSlice ⊑*) (* isSlice ⊑*) _ = ⊑*
  \\-uncurry {⟨ n ⟩} (_ isSlice ⊑Var) (_ isSlice ⊑Var) (_ isSlice ⊑Var) _ with n ≟ℕ n
  ... | yes refl  = ⊑Var
  ... | no contra = ⊥-elim (contra refl)
  -- compound: recurse using c+-⊑-inv/etc to extract sub-hypotheses
  \\-uncurry {_ + _} (_ isSlice ⊑+ r₁ r₂) (_ isSlice ⊑+ q₁ q₂) (_ isSlice ⊑+ p₁ p₂) hyp
    with c+-⊑-inv _ _ hyp
  ... | h₁ , h₂ = ⊑+
      (\\-uncurry (_ isSlice r₁) (_ isSlice q₁) (_ isSlice p₁) h₁)
      (\\-uncurry (_ isSlice r₂) (_ isSlice q₂) (_ isSlice p₂) h₂)
  \\-uncurry {_ × _} (_ isSlice ⊑× r₁ r₂) (_ isSlice ⊑× q₁ q₂) (_ isSlice ⊑× p₁ p₂) hyp
    with c×-⊑-inv _ _ hyp
  ... | h₁ , h₂ = ⊑×
      (\\-uncurry (_ isSlice r₁) (_ isSlice q₁) (_ isSlice p₁) h₁)
      (\\-uncurry (_ isSlice r₂) (_ isSlice q₂) (_ isSlice p₂) h₂)
  \\-uncurry {_ ⇒ _} (_ isSlice ⊑⇒ r₁ r₂) (_ isSlice ⊑⇒ q₁ q₂) (_ isSlice ⊑⇒ p₁ p₂) hyp
    with c⇒-⊑-inv _ _ hyp
  ... | h₁ , h₂ = ⊑⇒
      (\\-uncurry (_ isSlice r₁) (_ isSlice q₁) (_ isSlice p₁) h₁)
      (\\-uncurry (_ isSlice r₂) (_ isSlice q₂) (_ isSlice p₂) h₂)
  \\-uncurry {∀· _} (_ isSlice ⊑∀ r) (_ isSlice ⊑∀ q) (_ isSlice ⊑∀ p) hyp =
    ⊑∀ (\\-uncurry (_ isSlice r) (_ isSlice q) (_ isSlice p) (c∀-⊑-inv _ hyp))

typ-\\-exponential : ∀ {τ : Typ} → Exponential (λ x y → _⊑ₛ_ {a = τ} y x) _⊔ₛ_ (flip (typ-\\ₛ {τ}))
typ-\\-exponential w x y = \\-curry w x y , \\-uncurry w x y

instance
  typ-sliceBiHeyting : I.SliceBiHeyting Typ
  typ-sliceBiHeyting = record
    { _⇨ₛ_ = typ-⇨ₛ
    ; ⇨-exponential = typ-⇨-exponential
    ; _\\ₛ_ = typ-\\ₛ
    ; \\-exponential = typ-\\-exponential
    }
