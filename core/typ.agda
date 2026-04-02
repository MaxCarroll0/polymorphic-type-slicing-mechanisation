open import Data.Nat using (ℕ; _≟_)
open import Data.Maybe
open import Data.Sum
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
  -- Classify types by their 'kinds' i.e. the kind of their top-most constructor
  data _kind?_ : Typ → Typ → Set where 
    kindVar   : ∀ {m n}           → ⟨ m ⟩   kind? ⟨ n ⟩
    kind*     :                     *       kind? *
    kind□     :                     □       kind? □
    kind+     : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ + τ₂ kind? τ₁' + τ₂'
    kind×     : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ × τ₂ kind? τ₁' × τ₂'
    kind⇒     : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⇒ τ₂ kind? τ₁' ⇒ τ₂'
    kind∀     : ∀ {τ  τ'}         → ∀· τ    kind? ∀· τ'
    diff : ∀ {τ  τ'}              → τ       kind? τ'

  diag : (τ τ' : Typ) → τ kind? τ'
  diag *          *          = kind*
  diag □         □           = kind□
  diag ⟨ m ⟩     ⟨ n ⟩       = kindVar
  diag (τ₁ + τ₂) (τ₁' + τ₂') = kind+
  diag (τ₁ × τ₂) (τ₁' × τ₂') = kind×
  diag (τ₁ ⇒ τ₂) (τ₁' ⇒ τ₂') = kind⇒
  diag (∀· τ)    (∀· τ')     = kind∀
  diag τ         τ'          = diff

  shallow-disequality : {τ : Typ} → ¬(diag τ τ ≡ diff)
  shallow-disequality {⟨ x ⟩}    = λ ()
  shallow-disequality {*}        = λ ()
  shallow-disequality {□}        = λ ()
  shallow-disequality {(τ + τ₁)} = λ ()
  shallow-disequality {(τ × τ₁)} = λ ()
  shallow-disequality {(τ ⇒ τ₁)} = λ ()
  shallow-disequality {(∀· τ)}   = λ ()

  _≟t_ : (τ τ' : Typ) → Dec (τ ≡ τ')
  τ       ≟t τ' with diag τ τ'   | inspect (diag τ) τ'
  ...                  | kind*   | _     = yes refl
  ...                  | kind□   | _     = yes refl
  ⟨ m ⟩   ≟t ⟨ n ⟩     | kindVar | _     = map′ (cong ⟨_⟩)
                                                (λ where refl → refl) (m ≟ n)
  τ₁ + τ₂ ≟t τ₁' + τ₂' | kind+   | _     = map′ (uncurry (cong₂ _+_))
                                                (λ where refl → refl , refl)
                                                (τ₁ ≟t τ₁' ×-dec τ₂ ≟t τ₂') 
  τ₁ × τ₂ ≟t τ₁' × τ₂' | kind×   | _     = map′ (uncurry (cong₂ _×_))
                                                (λ where refl → refl , refl)
                                                (τ₁ ≟t τ₁' ×-dec τ₂ ≟t τ₂') 
  τ₁ ⇒ τ₂ ≟t τ₁' ⇒ τ₂' | kind⇒   | _     = map′ (uncurry (cong₂ _⇒_))
                                                (λ where refl → refl , refl)
                                                (τ₁ ≟t τ₁' ×-dec τ₂ ≟t τ₂') 
  ∀· τ    ≟t ∀· τ'     | kind∀   | _     = map′ (cong ∀·)
                                                (λ where refl → refl) (τ ≟t τ')
  ...                  | diff    | [ as ] = no λ where refl → shallow-disequality as

  -- (Decidable) Type Consistency
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

  shallow-inconsistency : {τ τ' : Typ} → (τ ~ τ') → (τ ≢ □) → (τ' ≢ □) → ¬(diag τ τ' ≡ diff)
  shallow-inconsistency ~?ᵣ _ τ'≢□ _ = τ'≢□ refl
  shallow-inconsistency ~?ₗ τ≢□ _ _ = τ≢□ refl

  _~?_ : (τ τ' : Typ) → Dec(τ ~ τ')
  τ ~? τ'         with diag τ τ' | inspect (diag τ) τ'
  ...                  | kind*   | _     = yes ~*
  ...                  | kind□   | _     = yes ~?ᵣ
  ⟨ m ⟩   ~? ⟨ n ⟩     | kindVar | _     = map′ (λ where refl → ~Var) (λ where ~Var → refl) (m ≟ n)
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
  ...                  | diff    | [ as ] with τ ≟t □ | τ' ≟t □
  ...                                     | yes τ≡□ | _        rewrite τ≡□  = yes ~?ₗ
  ...                                     | _       | yes τ'≡□ rewrite τ'≡□ = yes ~?ᵣ
  ...                                     | no  τ≢□ | no  τ'≢□
                                            = no λ τ~τ' → shallow-inconsistency τ~τ' τ≢□ τ'≢□ as 
 
  -- Consistency is an equivalence relation

  -- Slices (Precision)
  data _⊑t_ : Typ → Typ → Set where
    ⊑?   : ∀ {τ}                                     → □       ⊑t τ
    ⊑*   :                                             *       ⊑t *
    ⊑Var : ∀ {n}                                     → ⟨ n ⟩   ⊑t ⟨ n ⟩
    ⊑+   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ + τ₂ ⊑t τ₁' + τ₂'
    ⊑×   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ × τ₂ ⊑t τ₁' × τ₂'
    ⊑⇒   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ ⇒ τ₂ ⊑t τ₁' ⇒ τ₂'
    ⊑∀   : ∀ {τ τ'}          → τ  ⊑t τ'              → ∀· τ    ⊑t ∀· τ'

  infix 4 _⊑t_

  -- Slices form a partial order
  -- TODO

  -- Slices OF a term
  -- Slice property irrelevant to equality
  record SliceOf (τ : Typ) : Set where
    constructor _isSlice_
    field
      ↓     : Typ
      proof : ↓ ⊑t τ

  syntax SliceOf τ = ⌊ τ ⌋
  infix 3 _isSlice_

  open SliceOf

  -- Lifted precision on slices of the same type
  _⊑tₛ_ : ∀ {τ} → ⌊ τ ⌋ → ⌊ τ ⌋ → Set
  υ₁ ⊑tₛ υ₂ = υ₁ .↓ ⊑t υ₂ .↓

  -- Slices can be weakened by transitivity
  ⊑tₛ-weaken : ∀ {τ τ'} → τ' ⊑t τ → ⌊ τ' ⌋ → ⌊ τ ⌋
  ⊑tₛ-weaken τ'⊑τ = λ υ' → υ' .↓ isSlice {!!}

  ⊑tₛ-weaken-identity : ∀ {τ' τ} → {υ : ⌊ τ' ⌋} → {p : τ' ⊑t τ}
                        → (⊑tₛ-weaken p υ) .↓ ≡ υ .↓
  ⊑tₛ-weaken-identity = refl


  infix 4 _⊑ₛ_

  -- Slice are consistent
  ⊑to~1 : ∀ {τ τ'} → τ ⊑t τ' → τ ~ τ'
  ⊑to~1 ⊑? = ~?ₗ
  ⊑to~1 ⊑* = ~*
  ⊑to~1 ⊑Var = ~Var
  ⊑to~1 (⊑+ τ⊑tτ' τ⊑tτ'') = ~+ (⊑to~1 τ⊑tτ') (⊑to~1 τ⊑tτ'')
  ⊑to~1 (⊑× τ⊑tτ' τ⊑tτ'') = ~× (⊑to~1 τ⊑tτ') (⊑to~1 τ⊑tτ'')
  ⊑to~1 (⊑⇒ τ⊑tτ' τ⊑tτ'') = ~⇒ (⊑to~1 τ⊑tτ') (⊑to~1 τ⊑tτ'')
  ⊑to~1 (⊑∀ τ⊑tτ') = ~∀ (⊑to~1 τ⊑tτ')

  -- Meets. Note: order theoretic. NOT necessarily type consistent
  _⊓t_ : Typ → Typ → Typ
  τ₁ + τ₂ ⊓t τ₁' + τ₂' = (τ₁ ⊓t τ₁') + (τ₂ ⊓t τ₂')
  τ₁ × τ₂ ⊓t τ₁' × τ₂' = (τ₁ ⊓t τ₁') × (τ₂ ⊓t τ₂')
  τ₁ ⇒ τ₂ ⊓t τ₁' ⇒ τ₂' = (τ₁ ⊓t τ₁') ⇒ (τ₂ ⊓t τ₂')
  ∀· τ₂   ⊓t ∀· τ₂'    = ∀· (τ₂ ⊓t τ₂')
  τ       ⊓t τ'        with τ ≟t τ'
  ...                      | yes τ≡τ' = τ
  ...                      | no τ≢τ' = □

  infixl 6 _⊓t_

  -- Meets preserve precision
  ⊓t-preserves-⊑ : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁' ⊑t τ₁ → τ₂' ⊑t τ₂ → τ₁' ⊓t τ₂' ⊑t τ₁ ⊓t τ₂
  ⊓t-preserves-⊑ s1 s2 = {!!}

  -- In particular when τ₁ = τ₂ then we get the same notion as the slice joins below
  ⊓t-preserves-⊑-spec : ∀ {τ₁ τ₂ τ : Typ} → τ₁ ⊑t τ → τ₂ ⊑t τ → τ₁ ⊓t τ₂ ⊑t τ
  ⊓t-preserves-⊑-spec = {!!}

  -- Inconsistent Types have trivial meets
  ⊓t-consistent : ∀ {τ τ'} → τ ⊓t τ' ≢ □ → τ ~ τ'
  ⊓t-consistent neq = {!!}

  -- contrapositive
  ⊓t-inconsistent : ∀ {τ τ'} → τ ≁ τ' → τ ⊓t τ' ≡ □
  ⊓t-inconsistent incon = {!!}

  -- Meets form a bounded semi-lattice
  -- TODO

  -- Joins. Note: only valid for consistent types
  _⊔t_ : Typ → Typ → Typ
  τ₁ + τ₂ ⊔t τ₁' + τ₂' = (τ₁ ⊔t τ₁') + (τ₂ ⊔t τ₂')
  τ₁ × τ₂ ⊔t τ₁' × τ₂' = (τ₁ ⊔t τ₁') × (τ₂ ⊔t τ₂')
  τ₁ ⇒ τ₂ ⊔t τ₁' ⇒ τ₂' = (τ₁ ⊔t τ₁') ⇒ (τ₂ ⊔t τ₂')
  ∀· τ₂   ⊔t ∀· τ₂'    = ∀· (τ₂ ⊔t τ₂')
  τ       ⊔t τ'        = τ

  -- LUB property

  -- Meets (of slices of some type)
  open SliceOf

  _⊓tₛ_ : ∀ {τ} → ⌊ τ ⌋ → ⌊ τ ⌋ → ⌊ τ ⌋
  υ ⊓tₛ υ' = υ .↓ ⊓t υ' .↓ isSlice ⊓t-preserves-⊑-spec (υ .proof) (υ' .proof)

  infixl 6 _⊓tₛ_

  -- Joins (of slices of some type)
  _⊔tₛ_ : ∀ {τ} → ⌊ τ ⌋ → ⌊ τ ⌋ → ⌊ τ ⌋
  (τ₁ + τ₂ isSlice s) ⊔tₛ (τ₁' + τ₂' isSlice s') = {!!} isSlice {!!}
  (τ₁ × τ₂ isSlice s) ⊔tₛ (τ₁' × τ₂' isSlice s') = {!!} isSlice {!!}
  (τ₁ ⇒ τ₂ isSlice s) ⊔tₛ (τ₁' ⇒ τ₂' isSlice s') = {!!} isSlice {!!}
  (∀· τ₂ isSlice s)   ⊔tₛ (∀· τ₂' isSlice s')    = {!!} isSlice {!!}
  υ ⊔tₛ υ' with υ .↓ ≟t υ' .↓
  ...         | yes τ≡τ' = υ
  ...         | no τ≢τ' = υ -- Impossible case, maybe difficult to prove in this particular layout

  infixl 7 _⊔tₛ_

  -- Consistent types have joins

  -- Meets & Joins (of slices of some type) form a bounded lattice
  -- TODO
  
