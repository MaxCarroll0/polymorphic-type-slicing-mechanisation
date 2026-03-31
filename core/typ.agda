open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_,_; curry; uncurry)

open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

open import Relation.Binary using (Poset)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning

open import Relation.Nullary using (Dec; yes; no; ¬_; map′)
open import Relation.Nullary.Decidable using (_×-dec_)

module core.typ where

  -- Types
  data Typ : Set where
    ⟨_⟩ : ℕ → Typ  -- Type variables (nats)
    * : Typ
    □ : Typ
    _+_ : Typ → Typ → Typ
    _×_ : Typ → Typ → Typ
    _⇒_ : Typ → Typ → Typ
    ∀· : Typ → Typ
    
  infixl 23  _+_
  infixl 24  _×_
  infixr 25  _⇒_
 
  -- (Decidable) Equality
  _≟t_ : (τ τ' : Typ) → Dec (τ ≡ τ')
  *      ≟t *        = yes refl
  □      ≟t □        = yes refl
  ⟨ m ⟩  ≟t ⟨ n ⟩    = map′ (cong ⟨_⟩) (λ {refl → refl}) (m ≟ n)
  τ₁ + τ₂ ≟t τ₁' + τ₂' = map′ (uncurry (cong₂ _+_)) (λ {refl → refl , refl})
                            (τ₁ ≟t τ₁' ×-dec τ₂ ≟t τ₂') 
  τ₁ × τ₂ ≟t τ₁' × τ₂' = map′ (uncurry (cong₂ _×_)) (λ {refl → refl , refl})
                            (τ₁ ≟t τ₁' ×-dec τ₂ ≟t τ₂') 
  τ₁ ⇒ τ₂ ≟t τ₁' ⇒ τ₂' = map′ (uncurry (cong₂ _⇒_)) (λ {refl → refl , refl})
                            (τ₁ ≟t τ₁' ×-dec τ₂ ≟t τ₂') 
  ∀· τ   ≟t ∀· τ'    = map′ (cong ∀·) (λ {refl → refl}) (τ ≟t τ')
  -- This is sad :(
  *      ≟t □        = no λ ()
  *      ≟t ⟨ _ ⟩    = no λ ()
  *      ≟t _ + _    = no λ ()
  *      ≟t _ × _    = no λ ()
  *      ≟t _ ⇒ _    = no λ ()  
  *      ≟t ∀· _     = no λ ()
  □      ≟t *        = no λ ()
  □      ≟t ⟨ _ ⟩    = no λ ()
  □      ≟t _ + _    = no λ ()
  □      ≟t _ × _    = no λ ()
  □      ≟t _ ⇒ _    = no λ ()
  □      ≟t ∀· _     = no λ ()
  ⟨ _ ⟩  ≟t *        = no λ ()
  ⟨ _ ⟩  ≟t □        = no λ ()
  ⟨ _ ⟩  ≟t _ + _    = no λ ()
  ⟨ _ ⟩  ≟t _ × _    = no λ ()
  ⟨ _ ⟩  ≟t _ ⇒ _    = no λ ()
  ⟨ _ ⟩  ≟t ∀· _     = no λ ()
  _ + _  ≟t *        = no λ ()
  _ + _  ≟t □        = no λ ()
  _ + _  ≟t ⟨ _ ⟩    = no λ ()
  _ + _  ≟t _ × _    = no λ ()
  _ + _  ≟t _ ⇒ _    = no λ ()
  _ + _  ≟t ∀· _     = no λ ()
  _ × _  ≟t *        = no λ ()
  _ × _  ≟t □        = no λ ()
  _ × _  ≟t ⟨ _ ⟩    = no λ ()
  _ × _  ≟t _ + _    = no λ ()
  _ × _  ≟t _ ⇒ _    = no λ ()
  _ × _  ≟t ∀· _     = no λ ()
  _ ⇒ _  ≟t *        = no λ ()
  _ ⇒ _  ≟t □        = no λ ()
  _ ⇒ _  ≟t ⟨ _ ⟩    = no λ ()
  _ ⇒ _  ≟t _ + _    = no λ ()
  _ ⇒ _  ≟t _ × _    = no λ ()
  _ ⇒ _  ≟t ∀· _     = no λ ()
  ∀· _   ≟t *        = no λ ()
  ∀· _   ≟t □        = no λ ()
  ∀· _   ≟t ⟨ _ ⟩    = no λ ()
  ∀· _   ≟t _ + _    = no λ ()
  ∀· _   ≟t _ × _    = no λ ()
  ∀· _   ≟t _ ⇒ _    = no λ ()
  
  -- Type Consistency
  data _~_ : Typ → Typ → Set where
    ~* : * ~ *
    ~Var : ∀ {n} → ⟨ n ⟩ ~ ⟨ n ⟩
    ~?ᵣ : ∀ {τ} → τ ~ □
    ~?ₗ : ∀ {τ} → □ ~ τ
    ~+ : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ~ τ₁' → τ₂ ~ τ₂' → τ₁ + τ₂ ~ τ₁' + τ₂'
    ~× : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ~ τ₁' → τ₂ ~ τ₂' → τ₁ × τ₂ ~ τ₁' × τ₂'
    ~⇒ : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ~ τ₁' → τ₂ ~ τ₂' → τ₁ ⇒ τ₂ ~ τ₁' ⇒ τ₂'
    ~∀ : ∀ {τ τ'} → τ ~ τ' → ∀· τ ~ ∀· τ'

  _≁_ : (τ τ' : Typ) → Set
  _≁_ = λ (τ τ' : Typ) → ¬(τ ~ τ')
  
  -- Slices
  data _⊑t_ : Typ → Typ → Set where
    ⊑? : ∀ {τ} → □ ⊑t τ
    ⊑* : * ⊑t *
    ⊑Var : ∀ {n} → ⟨ n ⟩ ⊑t ⟨ n ⟩
    ⊑?ᵣ : ∀ {τ} → τ ⊑t □
    ⊑?ₗ : ∀ {τ} → □ ⊑t τ
    ⊑+ : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ + τ₂ ⊑t τ₁' + τ₂'
    ⊑× : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ × τ₂ ⊑t τ₁' × τ₂'
    ⊑⇒ : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ ⇒ τ₂ ⊑t τ₁' ⇒ τ₂'
    ⊑∀ : ∀ {τ τ'} → τ ⊑t τ' → ∀· τ ⊑t ∀· τ'

  -- Slices are preorders
  
  -- Slices are meet semi-lattices

  -- Slices OF a term are full lattices
