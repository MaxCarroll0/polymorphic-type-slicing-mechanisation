open import Data.Nat using (ℕ; _≟_)
open import Data.Maybe
open import Data.Sum
open import Data.Bool using (_∨_)
open import Data.Product using (_,_; ∃-syntax; curry; uncurry; proj₁; proj₂)

open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

open import Function using (_⇔_; _on_)

open import Relation.Binary using (Poset; IsPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive; Antisymmetric)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning

open import Relation.Nullary using (Dec; yes; no; ¬_; map′)
open import Relation.Nullary.Decidable using (_×-dec_)

module core.typ where

  -- Types
  data Typ : Set where
    ⟨_⟩ : ℕ → Typ  -- Type variables (nats: de Bruijn)
    *   : Typ
    □   : Typ
    _+_ : Typ → Typ → Typ
    _×_ : Typ → Typ → Typ
    _⇒_ : Typ → Typ → Typ
    ∀·  : Typ → Typ

  infixl 23 _+_
  infixl 24 _×_
  infixr 25 _⇒_

  -- (Decidable) Equality
  -- Classify types by their 'kinds' i.e. the kind of their top-most constructor
  data _kind?_ : Typ → Typ → Set where
    kindVar : ∀ {m n}           → ⟨ m ⟩   kind? ⟨ n ⟩
    kind*   :                     *       kind? *
    kind□   :                     □       kind? □
    kind+   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ + τ₂ kind? τ₁' + τ₂'
    kind×   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ × τ₂ kind? τ₁' × τ₂'
    kind⇒   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⇒ τ₂ kind? τ₁' ⇒ τ₂'
    kind∀   : ∀ {τ τ'}          → ∀· τ    kind? ∀· τ'
    diff    : ∀ {τ τ'}          → τ       kind? τ'

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
    ~*   :                                             *       ~ *
    ~Var : ∀ {n}             →                         ⟨ n ⟩   ~ ⟨ n ⟩
    ~?ᵣ  : ∀ {τ}             →                         τ       ~ □
    ~?ₗ  : ∀ {τ}             →                         □       ~ τ
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

  -- Compatibility: reflexive and symmetric (but NOT transitive)
  record IsCompatibility {A : Set} (_∼_ : A → A → Set) : Set where
    field
      reflexive  : Reflexive _∼_
      symmetric  : Symmetric _∼_

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

  -- Slices (Precision)
  data _⊑t_ : Typ → Typ → Set where
    ⊑?   : ∀ {τ}             →                         □       ⊑t τ
    ⊑*   :                                             *       ⊑t *
    ⊑Var : ∀ {n}             →                         ⟨ n ⟩   ⊑t ⟨ n ⟩
    ⊑+   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ + τ₂ ⊑t τ₁' + τ₂'
    ⊑×   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ × τ₂ ⊑t τ₁' × τ₂'
    ⊑⇒   : ∀ {τ₁ τ₂ τ₁' τ₂'} → τ₁ ⊑t τ₁' → τ₂ ⊑t τ₂' → τ₁ ⇒ τ₂ ⊑t τ₁' ⇒ τ₂'
    ⊑∀   : ∀ {τ τ'}          → τ ⊑t τ'               → ∀· τ    ⊑t ∀· τ'

  infix 4 _⊑t_

  -- Slices form a partial order
  ⊑t-refl : Reflexive _⊑t_
  ⊑t-refl {⟨ _ ⟩}   = ⊑Var
  ⊑t-refl {*}       = ⊑*
  ⊑t-refl {□}       = ⊑?
  ⊑t-refl {_ + _}   = ⊑+ ⊑t-refl ⊑t-refl
  ⊑t-refl {_ × _}   = ⊑× ⊑t-refl ⊑t-refl
  ⊑t-refl {_ ⇒ _}   = ⊑⇒ ⊑t-refl ⊑t-refl
  ⊑t-refl {∀· _}    = ⊑∀ ⊑t-refl

  ⊑t-trans : Transitive _⊑t_
  ⊑t-trans ⊑? _              = ⊑?
  ⊑t-trans ⊑* ⊑*             = ⊑*
  ⊑t-trans ⊑Var ⊑Var         = ⊑Var
  ⊑t-trans (⊑+ p q) (⊑+ r s) = ⊑+ (⊑t-trans p r) (⊑t-trans q s)
  ⊑t-trans (⊑× p q) (⊑× r s) = ⊑× (⊑t-trans p r) (⊑t-trans q s)
  ⊑t-trans (⊑⇒ p q) (⊑⇒ r s) = ⊑⇒ (⊑t-trans p r) (⊑t-trans q s)
  ⊑t-trans (⊑∀ p) (⊑∀ q)     = ⊑∀ (⊑t-trans p q)

  ⊑t-antisym : Antisymmetric _≡_ _⊑t_
  ⊑t-antisym ⊑? ⊑?             = refl
  ⊑t-antisym ⊑* ⊑*             = refl
  ⊑t-antisym ⊑Var ⊑Var         = refl
  ⊑t-antisym (⊑+ p q) (⊑+ r s) = cong₂ _+_ (⊑t-antisym p r) (⊑t-antisym q s)
  ⊑t-antisym (⊑× p q) (⊑× r s) = cong₂ _×_ (⊑t-antisym p r) (⊑t-antisym q s)
  ⊑t-antisym (⊑⇒ p q) (⊑⇒ r s) = cong₂ _⇒_ (⊑t-antisym p r) (⊑t-antisym q s)
  ⊑t-antisym (⊑∀ p) (⊑∀ q)     = cong ∀· (⊑t-antisym p q)

  ⊑t-isPartialOrder : IsPartialOrder _≡_ _⊑t_
  ⊑t-isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ where refl → ⊑t-refl
      ; trans = ⊑t-trans
      }
    ; antisym = ⊑t-antisym
    }

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
  ⊑tₛ-weaken τ'⊑τ = λ υ' → υ' .↓ isSlice ⊑t-trans (υ' .proof) τ'⊑τ

  ⊑tₛ-weaken-identity : ∀ {τ' τ} → {υ : ⌊ τ' ⌋} → {p : τ' ⊑t τ}
                        → (⊑tₛ-weaken p υ) .↓ ≡ υ .↓
  ⊑tₛ-weaken-identity = refl

  infix 4 _⊑tₛ_

  -- Lifted partial order on slices of a type
  ⊑tₛ-refl : ∀ {τ} → Reflexive (_⊑tₛ_ {τ})
  ⊑tₛ-refl = ⊑t-refl

  ⊑tₛ-trans : ∀ {τ} → Transitive (_⊑tₛ_ {τ})
  ⊑tₛ-trans = ⊑t-trans

  ⊑tₛ-antisym : ∀ {τ} → Antisymmetric (_≡_ on ↓) (_⊑tₛ_ {τ})
  ⊑tₛ-antisym = ⊑t-antisym

  ⊑tₛ-isPartialOrder : ∀ {τ} → IsPartialOrder (_≡_ on ↓) (_⊑tₛ_ {τ})
  ⊑tₛ-isPartialOrder = record
    { isPreorder = record
      { isEquivalence = record
        { refl = refl ; sym = sym ; trans = trans }
      ; reflexive = λ where refl → ⊑t-refl
      ; trans = λ {τ''} {τ'} {τ} → ⊑t-trans
      }
    ; antisym = λ {τ'} {τ} → ⊑t-antisym
    }

  -- Slices are consistent
  ⊑to~ : ∀ {τ τ'} → τ ⊑t τ' → τ ~ τ'
  ⊑to~ ⊑?         = ~?ₗ
  ⊑to~ ⊑*         = ~*
  ⊑to~ ⊑Var       = ~Var
  ⊑to~ (⊑+ p₁ p₂) = ~+ (⊑to~ p₁) (⊑to~ p₂)
  ⊑to~ (⊑× p₁ p₂) = ~× (⊑to~ p₁) (⊑to~ p₂)
  ⊑to~ (⊑⇒ p₁ p₂) = ~⇒ (⊑to~ p₁) (⊑to~ p₂)
  ⊑to~ (⊑∀ p)     = ~∀ (⊑to~ p)

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

