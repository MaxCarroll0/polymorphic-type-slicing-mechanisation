module Core.Typ.Consistency where

open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_,_; uncurry)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; inspect; [_])
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Nullary using (Dec; yes; no; ¬_; map′)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Core.Typ.Base
open import Core.Typ.Equality

-- Type Consistency
data _~_ : Typ → Typ → Set where
  ~*   :                                             *       ~ *
  ~Var : ∀ {n}             →                         ⟨ n ⟩   ~ ⟨ n ⟩
  ~?ᵣ   : ∀ {τ}             →                         τ       ~ □
  ~?ₗ   : ∀ {τ}             →                         □       ~ τ
  ~+   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ~ τ₁' → τ₂ ~ τ₂'  → τ₁ + τ₂ ~ τ₁' + τ₂'
  ~×   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ~ τ₁' → τ₂ ~ τ₂'  → τ₁ × τ₂ ~ τ₁' × τ₂'
  ~⇒   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ~ τ₁' → τ₂ ~ τ₂'  → τ₁ ⇒ τ₂ ~ τ₁' ⇒ τ₂'
  ~∀   : ∀ {τ τ'}          → τ ~ τ'                → ∀· τ    ~ ∀· τ'

_≁_ : (τ τ' : Typ) → Set
_≁_ = λ (τ τ' : Typ) → ¬(τ ~ τ')

shallow-inconsistency : {τ τ' : Typ} → (τ ~ τ') → (τ ≢ □) → (τ' ≢ □) → ¬(diag τ τ' ≡ diff)
shallow-inconsistency ~?ᵣ _ τ'≢□ _ = τ'≢□ refl
shallow-inconsistency ~?ₗ τ≢□ _ _ = τ≢□ refl

_~?_ : (τ τ' : Typ) → Dec(τ ~ τ')
τ ~? τ'         with diag τ τ' | inspect (diag τ) τ'
...                  | kind*   | _     = yes ~*
...                  | kind□   | _     = yes ~?ᵣ
⟨ m ⟩   ~? ⟨ n ⟩     | kindVar | _     = map′ (λ where refl → ~Var) (λ where ~Var → refl) (m ≟ℕ n)
τ₁ + τ₂ ~? τ₁' + τ₂' | kind+   | _     = map′ (uncurry ~+)
                                              (λ where (~+ τ₁~τ₁' τ₂~τ₂') → τ₁~τ₁' , τ₂~τ₂')
                                              (τ₁ ~? τ₁' ×-dec τ₂ ~? τ₂')
τ₁ × τ₂ ~? τ₁' × τ₂' | kind×   | _     = map′ (uncurry ~×)
                                              (λ where (~× τ₁~τ₁' τ₂~τ₂') → τ₁~τ₁' , τ₂~τ₂')
                                              (τ₁ ~? τ₁' ×-dec τ₂ ~? τ₂')
τ₁ ⇒ τ₂ ~? τ₁' ⇒ τ₂' | kind⇒   | _     = map′ (uncurry ~⇒)
                                              (λ where (~⇒ τ₁~τ₁' τ₂~τ₂') → τ₁~τ₁' , τ₂~τ₂')
                                              (τ₁ ~? τ₁' ×-dec τ₂ ~? τ₂')
∀· τ ~? ∀· τ'        | kind∀   | _     = map′ (~∀)
                                              (λ where (~∀ τ~τ') → τ~τ')
                                              (τ ~? τ')
...                  | diff    | [ as ] with τ ≟ □ | τ' ≟ □
...                                     | yes τ≡□ | _        rewrite τ≡□  = yes ~?ₗ
...                                     | _       | yes τ'≡□ rewrite τ'≡□ = yes ~?ᵣ
...                                     | no  τ≢□ | no  τ'≢□
                                          = no λ τ~τ' → shallow-inconsistency τ~τ' τ≢□ τ'≢□ as

-- Compatibility: reflexive and symmetric (but NOT transitive)
record IsCompatibility {A : Set} (_∼_ : A → A → Set) : Set where
  field
    reflexive  : Reflexive _∼_
    symmetric  : Symmetric _∼_

private
  ~-refl : Reflexive _~_
  ~-refl {⟨ _ ⟩}   = ~Var
  ~-refl {*}       = ~*
  ~-refl {□}       = ~?ᵣ
  ~-refl {_ + _}   = ~+ ~-refl ~-refl
  ~-refl {_ × _}   = ~× ~-refl ~-refl
  ~-refl {_ ⇒ _}   = ~⇒ ~-refl ~-refl
  ~-refl {∀· _}    = ~∀ ~-refl
  
  ~-sym : Symmetric _~_
  ~-sym ~*           = ~*
  ~-sym ~Var         = ~Var
  ~-sym ~?ᵣ          = ~?ₗ
  ~-sym ~?ₗ          = ~?ᵣ
  ~-sym (~+ p q)     = ~+ (~-sym p) (~-sym q)
  ~-sym (~× p q)     = ~× (~-sym p) (~-sym q)
  ~-sym (~⇒ p q)     = ~⇒ (~-sym p) (~-sym q)
  ~-sym (~∀ p)       = ~∀ (~-sym p)
  
~-isCompatibility : IsCompatibility _~_
~-isCompatibility = record { reflexive = ~-refl ; symmetric = ~-sym }

-- For fun: counterexample to transitivity: ⟨0⟩ ~ □ and □ ~ ⟨1⟩, but ⟨0⟩ ≁ ⟨1⟩
~-not-trans : ¬ Transitive _~_
~-not-trans trans with trans {⟨ 0 ⟩} {□} {⟨ 1 ⟩} ~?ᵣ ~?ₗ
... | ()
