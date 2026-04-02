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
  -- Classify types by their 'kinds' i.e. the kind of their top-most constructor
  data _kind?_ : Typ → Typ → Set where 
    kindVar   : ∀ {m n}           → ⟨ m ⟩   kind? ⟨ n ⟩
    kind*     :                     *       kind? *
    kind□     :                     □       kind? □
    kind+     : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ + τ₂ kind? τ₁' + τ₂'
    kind×     : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ × τ₂ kind? τ₁' × τ₂'
    kind⇒     : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⇒ τ₂ kind? τ₁' ⇒ τ₂'
    kind∀     : ∀ {τ  τ'}         → ∀· τ    kind? ∀· τ'
    diff : ∀ {τ  τ'}         → τ       kind? τ'

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

  -- Consistency is an equivalence relation

  -- Slices (Precision)
  data _⊑t_ : Typ → Typ → Set where
    ⊑? : ∀ {τ} → □ ⊑t τ
    ⊑* : * ⊑t *
    ⊑Var : ∀ {n} → ⟨ n ⟩ ⊑t ⟨ n ⟩
    ⊑+ : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ + τ₂ ⊑t τ₁' + τ₂'
    ⊑× : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ × τ₂ ⊑t τ₁' × τ₂'
    ⊑⇒ : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ ⇒ τ₂ ⊑t τ₁' ⇒ τ₂'
    ⊑∀ : ∀ {τ τ'} → τ ⊑t τ' → ∀· τ ⊑t ∀· τ'

  infix 4 _⊑t_

  -- Slices form a partial order
  -- TODO

  -- Slices OF a term
  ⌊_⌋ : Typ → Set
  ⌊ τ ⌋ = ∃[ τ' ] τ' ⊑t τ

  _↓ : ∀ {τ} → ⌊ τ ⌋ → Typ
  υ ↓ = proj₁ υ

  infix 50 _↓

  _slice : ∀ {τ} → (υ : ⌊ τ ⌋) → υ ↓ ⊑t τ
  υ slice = proj₂ υ

  -- Relating consistency and precision
  ~to⊑1 : ∀ {τ τ'} → τ ~ τ' → τ ⊑t τ'
  ~to⊑1 cons = {!!}
  ~to⊑2 : ∀ {τ τ'} → τ ~ τ' → τ' ⊑t τ'
  ~to⊑2 cons = {!!}
  ⊑to~1 : ∀ {τ τ'} → τ ⊑t τ' → τ ~ τ'
  ⊑to~1 cons = {!!}
  ⊑to~2 : ∀ {τ τ'} → τ' ⊑t τ → τ ~ τ'
  ⊑to~2 cons = {!!}

  -- Meets. Note: order theoretic. NOT necessarily type consistent
  _⊓t_ : Typ → Typ → Typ
  τ₁ + τ₂ ⊓t τ₁' + τ₂' = (τ₁ ⊓t τ₁') + (τ₂ ⊓t τ₂')
  τ₁ × τ₂ ⊓t τ₁' × τ₂' = (τ₁ ⊓t τ₁') × (τ₂ ⊓t τ₂')
  τ₁ ⇒ τ₂ ⊓t τ₁' ⇒ τ₂' = (τ₁ ⊓t τ₁') ⇒ (τ₂ ⊓t τ₂')
  ∀· τ₂ ⊓t ∀· τ₂' = ∀· (τ₂ ⊓t τ₂')
  τ ⊓t τ' with τ ≟t τ'
  ...    | yes τ≡τ' = τ
  ...    | no τ≢τ' = □

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

  -- Meets (of slices of some type)
  _⊓tₛ_ : ∀ {τ} → ⌊ τ ⌋ → ⌊ τ ⌋ → ⌊ τ ⌋
  υ ⊓tₛ υ' = υ ↓ ⊓t υ' ↓ , ⊓t-preserves-⊑-spec (υ slice) (υ' slice)

  infixl 6 _⊓tₛ_

  -- Joins (of slices of some type)
  _⊔tₛ_ : ∀ {τ} → ⌊ τ ⌋ → ⌊ τ ⌋ → ⌊ τ ⌋
  (τ₁ + τ₂ , s) ⊔tₛ (τ₁' + τ₂' , s') = {!!} , {!!}
  (τ₁ × τ₂ , s) ⊔tₛ (τ₁' × τ₂' , s') = {!!} , {!!}
  (τ₁ ⇒ τ₂ , s) ⊔tₛ (τ₁' ⇒ τ₂' , s') = {!!} , {!!}
  (∀· τ₂ , s) ⊔tₛ (∀· τ₂' , s') = {!!} , {!!}
  υ ⊔tₛ υ' with υ ↓ ≟t υ' ↓
  ...    | yes τ≡τ' = υ
  ...    | no τ≢τ' = {!!} -- Impossible case, maybe difficult to prove in this particular layout

  infixl 7 _⊔tₛ_

  -- Meets & Joins (of slices of some type) form a bounded lattice
  -- TODO
  
