open import Data.Nat using (ℕ; _≟_)
open import Data.Maybe.Base
open import Data.Bool using (_∨_)
open import Data.Product using (_,_; ∃-syntax; curry; uncurry; proj₁; proj₂)

open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

open import Function using (_⇔_)

open import Relation.Binary using (Poset)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning

open import Relation.Nullary using (Dec; yes; no; ¬_; map′)
open import Relation.Nullary.Decidable using (_×-dec_)

module core.typ where

  -- Types
  data Typ : Set where
    ⟨_⟩ : ℕ → Typ  -- Type variables (nats)
    *   : Typ
    □   : Typ
    _+_ : Typ → Typ → Typ
    _×_ : Typ → Typ → Typ
    _⇒_ : Typ → Typ → Typ
    ∀·  : Typ → Typ
    
  infixl 23  _+_
  infixl 24  _×_
  infixr 25  _⇒_
 
  -- (Decidable) Equality
  data _same-kind_ : Typ → Typ → Set where 
    kindVar : ∀ m n →           ⟨ m ⟩   same-kind ⟨ n ⟩
    kind*   :                   *       same-kind *
    kind□   :                   □       same-kind □
    kind+   : ∀ τ₁ τ₂ τ₁' τ₂' → τ₁ + τ₂ same-kind τ₁' + τ₂'
    kind×   : ∀ τ₁ τ₂ τ₁' τ₂' → τ₁ × τ₂ same-kind τ₁' × τ₂'
    kind⇒   : ∀ τ₁ τ₂ τ₁' τ₂' → τ₁ ⇒ τ₂ same-kind τ₁' ⇒ τ₂'
    kind∀   : ∀ τ  τ'         → ∀· τ    same-kind ∀· τ' 

  diag : (τ τ' : Typ) → Maybe (τ same-kind τ')
  diag *          *          = just kind*
  diag □         □           = just kind□
  diag ⟨ m ⟩     ⟨ n ⟩       = just (kindVar m n)
  diag (τ₁ + τ₂) (τ₁' + τ₂') = just (kind+ τ₁ τ₂ τ₁' τ₂')
  diag (τ₁ × τ₂) (τ₁' × τ₂') = just (kind× τ₁ τ₂ τ₁' τ₂')
  diag (τ₁ ⇒ τ₂) (τ₁' ⇒ τ₂') = just (kind⇒ τ₁ τ₂ τ₁' τ₂')
  diag (∀· τ)    (∀· τ')     = just (kind∀ τ τ')
  diag _         _           = nothing

  shallow-disequality : (τ : Typ) → ¬(diag τ τ ≡ nothing)
  shallow-disequality ⟨ x ⟩    = λ ()
  shallow-disequality *        = λ ()
  shallow-disequality □        = λ ()
  shallow-disequality (τ + τ₁) = λ ()
  shallow-disequality (τ × τ₁) = λ ()
  shallow-disequality (τ ⇒ τ₁) = λ ()
  shallow-disequality (∀· τ)   = λ ()

  _≟t_ : (τ τ' : Typ) → Dec (τ ≡ τ')
  τ ≟t τ' with diag τ τ'                  | inspect (diag τ) τ'
  ...        | just kind*                 | _ = yes refl
  ...        | just kind□                 | _ = yes refl
  ...        | just (kindVar m n)         | _
               = map′ (cong ⟨_⟩) (λ {refl → refl}) (m ≟ n)
  ...        | just (kind+ τ₁ τ₂ τ₁' τ₂') | _
               = map′ (uncurry (cong₂ _+_)) (λ where refl → refl , refl)
                      (τ₁ ≟t τ₁' ×-dec τ₂ ≟t τ₂') 
  ...        | just (kind× τ₁ τ₂ τ₁' τ₂') | _
               = map′ (uncurry (cong₂ _×_)) (λ where refl → refl , refl)
                      (τ₁ ≟t τ₁' ×-dec τ₂ ≟t τ₂') 
  ...        | just (kind⇒ τ₁ τ₂ τ₁' τ₂') | _
               = map′ (uncurry (cong₂ _⇒_)) (λ where refl → refl , refl)
                            (τ₁ ≟t τ₁' ×-dec τ₂ ≟t τ₂') 
  ...        | just (kind∀ τ τ')          | _
               = map′ (cong ∀·) (λ where refl → refl) (τ ≟t τ')
  ...        | nothing                    | [ isnothing ]
               = no λ where refl → shallow-disequality τ isnothing 

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
