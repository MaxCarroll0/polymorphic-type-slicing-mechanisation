open import Data.Nat using (ℕ; _≟_)
open import Data.Maybe
open import Data.Sum
open import Data.Empty
open import Data.Bool using (_∨_)
open import Data.Product using (_,_; ∃-syntax; curry; uncurry; proj₁; proj₂)

open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
  
open import Function using (_⇔_; _on_)

open import Relation.Binary using (Poset; IsPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive; Antisymmetric; Maximum; Minimum)
open import Relation.Binary.Lattice.Structures using (IsMeetSemilattice; IsJoinSemilattice; IsLattice; IsBoundedLattice)
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning

open import Relation.Nullary using (Dec; yes; no; ¬_; map′)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Data.Empty using (⊥-elim)

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
  τ ⊓t τ' with diag τ τ'
  ...        | diff  = □
  ...        | kind□  = □
  ...        | kind* = *
  ...        | kind+ {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊓t τ₁') + (τ₂ ⊓t τ₂')
  ...        | kind× {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊓t τ₁') × (τ₂ ⊓t τ₂')
  ...        | kind⇒ {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊓t τ₁') ⇒ (τ₂ ⊓t τ₂')
  ...        | kind∀ {τ} {τ'} = ∀· (τ ⊓t τ')
  ...        | kindVar {m} {n} with m ≟ n
  ...                          | yes _ = ⟨ m ⟩
  ...                          | no  _ = □
  
  infixl 6 _⊓t_

  -- Inconsistent Types have trivial meets
  ⊓t-consistent : ∀ {τ τ'} → τ ⊓t τ' ≢ □ → τ ~ τ'
  ⊓t-consistent neq = {!!}

  -- contrapositive
  ⊓t-inconsistent : ∀ {τ τ'} → τ ≁ τ' → τ ⊓t τ' ≡ □
  ⊓t-inconsistent incon = {!!}

  -- Meets form a bounded semi-lattice (GLB property)
  ⊓t-lb₁ : ∀ τ₁ τ₂ → τ₁ ⊓t τ₂ ⊑t τ₁
  ⊓t-lb₁ τ       τ'         with diag τ τ'
  ⊓t-lb₁ (τ₁ + τ₂) (τ₁' + τ₂') | kind+ = ⊑+ (⊓t-lb₁ τ₁ τ₁') (⊓t-lb₁ τ₂ τ₂')
  ⊓t-lb₁ (τ₁ × τ₂) (τ₁' × τ₂') | kind× = ⊑× (⊓t-lb₁ τ₁ τ₁') (⊓t-lb₁ τ₂ τ₂')
  ⊓t-lb₁ (τ₁ ⇒ τ₂) (τ₁' ⇒ τ₂') | kind⇒ = ⊑⇒ (⊓t-lb₁ τ₁ τ₁') (⊓t-lb₁ τ₂ τ₂')
  ⊓t-lb₁ (∀· τ)    (∀· τ')     | kind∀ = ⊑∀ (⊓t-lb₁ τ τ')
  ⊓t-lb₁ ⟨ m ⟩     ⟨ n ⟩       | kindVar with m ≟ n
  ...                                | yes _ = ⊑Var
  ...                                | no  _ = ⊑?
  ⊓t-lb₁ *         *           | kind* = ⊑*
  ⊓t-lb₁ □         □           | kind□ = ⊑?
  ⊓t-lb₁ _         _           | diff = ⊑?

  ⊓t-lb₂ : ∀ τ₁ τ₂ → τ₁ ⊓t τ₂ ⊑t τ₂
  ⊓t-lb₂ τ       τ'        with diag τ τ'
  ⊓t-lb₂ (τ₁ + τ₂) (τ₁' + τ₂') | kind+ = ⊑+ (⊓t-lb₂ τ₁ τ₁') (⊓t-lb₂ τ₂ τ₂')
  ⊓t-lb₂ (τ₁ × τ₂) (τ₁' × τ₂') | kind× = ⊑× (⊓t-lb₂ τ₁ τ₁') (⊓t-lb₂ τ₂ τ₂')
  ⊓t-lb₂ (τ₁ ⇒ τ₂) (τ₁' ⇒ τ₂') | kind⇒ = ⊑⇒ (⊓t-lb₂ τ₁ τ₁') (⊓t-lb₂ τ₂ τ₂')
  ⊓t-lb₂ (∀· τ)    (∀· τ')     | kind∀ = ⊑∀ (⊓t-lb₂ τ τ')
  ⊓t-lb₂ ⟨ m ⟩     ⟨ n ⟩       | kindVar with m ≟ n
  ...                                | yes refl = ⊑Var
  ...                                | no  _ = ⊑?
  ⊓t-lb₂ *         *           | kind* = ⊑*
  ⊓t-lb₂ □         □           | kind□ = ⊑?
  ⊓t-lb₂ _         _           | diff  = ⊑?

  ⊓t-glb : ∀ {τ τ₁ τ₂} → τ ⊑t τ₁ → τ ⊑t τ₂ → τ ⊑t τ₁ ⊓t τ₂
  ⊓t-glb ⊑? _                   = ⊑?
  ⊓t-glb ⊑* ⊑*                  = ⊑*
  ⊓t-glb (⊑Var {m}) (⊑Var {m}) with m ≟ m
  ... | yes _ = ⊑Var
  ... | no contr = ⊥-elim (contr refl) -- not automatic sadly
  ⊓t-glb (⊑+ p₁ p₂) (⊑+ q₁ q₂) = ⊑+ (⊓t-glb p₁ q₁) (⊓t-glb p₂ q₂)
  ⊓t-glb (⊑× p₁ p₂) (⊑× q₁ q₂) = ⊑× (⊓t-glb p₁ q₁) (⊓t-glb p₂ q₂)
  ⊓t-glb (⊑⇒ p₁ p₂) (⊑⇒ q₁ q₂) = ⊑⇒ (⊓t-glb p₁ q₁) (⊓t-glb p₂ q₂)
  ⊓t-glb (⊑∀ p)     (⊑∀ q)     = ⊑∀ (⊓t-glb p q)

  -- Meets preserve precision
  ⊓t-preserves-⊑ : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁' ⊑t τ₁ → τ₂' ⊑t τ₂ → τ₁' ⊓t τ₂' ⊑t τ₁ ⊓t τ₂
  ⊓t-preserves-⊑ {_} {τ₁'} {_} {τ₂'} lb₁ lb₂ = ⊓t-glb (⊑t-trans (⊓t-lb₁ τ₁' τ₂') lb₁) (⊑t-trans (⊓t-lb₂ τ₁' τ₂') lb₂)

  -- In particular when τ₁ = τ₂ then we get the same notion as the slice joins below
  ⊓t-preserves-⊑-spec : ∀ {τ₁ τ₂ τ : Typ} → τ₁ ⊑t τ → τ₂ ⊑t τ → τ₁ ⊓t τ₂ ⊑t τ
  ⊓t-preserves-⊑-spec p₁ p₂ = ⊑t-trans (⊓t-lb₁ _ _) p₁

  -- Meet is greatest lower bound
  ⊓t-infimum : Infimum _⊑t_ _⊓t_
  ⊓t-infimum τ₁ τ₂ = ⊓t-lb₁ τ₁ τ₂ , ⊓t-lb₂ τ₁ τ₂ , λ τ → ⊓t-glb {τ} {τ₁} {τ₂}

  -- Meet semilattice structure
  ⊓t-isMeetSemilattice : IsMeetSemilattice _≡_ _⊑t_ _⊓t_
  ⊓t-isMeetSemilattice = record
    { isPartialOrder = ⊑t-isPartialOrder
    ; infimum        = ⊓t-infimum
    }

  -- Joins. Note: only valid for consistent types
  _⊔t_ : Typ → Typ → Typ
  τ ⊔t τ' with diag τ τ'
  ...        | kind□  = □
  ...        | kind* = *
  ...        | kind+ {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊔t τ₁') + (τ₂ ⊔t τ₂')
  ...        | kind× {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊔t τ₁') × (τ₂ ⊔t τ₂')
  ...        | kind⇒ {τ₁} {τ₂} {τ₁'} {τ₂'} = (τ₁ ⊔t τ₁') ⇒ (τ₂ ⊔t τ₂')
  ...        | kind∀ {τ} {τ'} = ∀· (τ ⊔t τ')
  ...        | kindVar {m} {n} = ⟨ m ⟩
  -- Using decidability over pattern matching simplifies proofs. But adding 3 types of 'diff' for τ diff □ and □ diff τ' might be cleaner
  τ ⊔t τ'    | diff with τ ≟t □
  ...                  | yes _  = τ'
  ...                  | no  _  = τ

  infixl 6 _⊔t_

  -- Join identity lemmas
  ⊔t-identityₗ : ∀ τ → □ ⊔t τ ≡ τ
  ⊔t-identityₗ τ with diag □ τ
  ⊔t-identityₗ □         | kind□ = refl
  ⊔t-identityₗ _         | diff = refl

  ⊔t-identityᵣ : ∀ τ → τ ⊔t □ ≡ τ
  ⊔t-identityᵣ τ with diag τ □
  ⊔t-identityᵣ □         | kind□ = refl
  ⊔t-identityᵣ τ         | diff with τ ≟t □
  ...                           | yes refl = refl
  ...                           | no  _    = refl

  -- Least upper bound (if consist)
  ⊔t-ub₁ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → τ₁ ⊑t τ₁ ⊔t τ₂
  ⊔t-ub₁ ~*               = ⊑*
  ⊔t-ub₁ ~Var             = ⊑Var
  ⊔t-ub₁ (~?ᵣ {τ})        rewrite ⊔t-identityᵣ τ = ⊑t-refl
  ⊔t-ub₁ ~?ₗ              = ⊑?
  ⊔t-ub₁ (~+ c₁ c₂)       = ⊑+ (⊔t-ub₁ c₁) (⊔t-ub₁ c₂)
  ⊔t-ub₁ (~× c₁ c₂)       = ⊑× (⊔t-ub₁ c₁) (⊔t-ub₁ c₂)
  ⊔t-ub₁ (~⇒ c₁ c₂)       = ⊑⇒ (⊔t-ub₁ c₁) (⊔t-ub₁ c₂)
  ⊔t-ub₁ (~∀ c)           = ⊑∀ (⊔t-ub₁ c)

  ⊔t-ub₂ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → τ₂ ⊑t τ₁ ⊔t τ₂
  ⊔t-ub₂ ~*               = ⊑*
  ⊔t-ub₂ ~Var             = ⊑Var
  ⊔t-ub₂ ~?ᵣ              = ⊑?
  ⊔t-ub₂ (~?ₗ {τ})        rewrite ⊔t-identityₗ τ = ⊑t-refl
  ⊔t-ub₂ (~+ c₁ c₂)       = ⊑+ (⊔t-ub₂ c₁) (⊔t-ub₂ c₂)
  ⊔t-ub₂ (~× c₁ c₂)       = ⊑× (⊔t-ub₂ c₁) (⊔t-ub₂ c₂)
  ⊔t-ub₂ (~⇒ c₁ c₂)       = ⊑⇒ (⊔t-ub₂ c₁) (⊔t-ub₂ c₂)
  ⊔t-ub₂ (~∀ c)           = ⊑∀ (⊔t-ub₂ c)

  ⊔t-lub : ∀ {τ τ₁ τ₂} → τ₁ ~ τ₂ → τ₁ ⊑t τ → τ₂ ⊑t τ → τ₁ ⊔t τ₂ ⊑t τ
  ⊔t-lub ~*               ⊑*         ⊑*         = ⊑*
  ⊔t-lub ~Var             ⊑Var       ⊑Var       = ⊑Var
  ⊔t-lub (~?ᵣ {τ₁})       p          ⊑?         rewrite ⊔t-identityᵣ τ₁ = p
  ⊔t-lub (~?ₗ {τ₂})       ⊑?         q          rewrite ⊔t-identityₗ τ₂ = q
  ⊔t-lub (~+ c₁ c₂)       (⊑+ p₁ p₂) (⊑+ q₁ q₂) = ⊑+ (⊔t-lub c₁ p₁ q₁) (⊔t-lub c₂ p₂ q₂)
  ⊔t-lub (~× c₁ c₂)       (⊑× p₁ p₂) (⊑× q₁ q₂) = ⊑× (⊔t-lub c₁ p₁ q₁) (⊔t-lub c₂ p₂ q₂)
  ⊔t-lub (~⇒ c₁ c₂)       (⊑⇒ p₁ p₂) (⊑⇒ q₁ q₂) = ⊑⇒ (⊔t-lub c₁ p₁ q₁) (⊔t-lub c₂ p₂ q₂)
  ⊔t-lub (~∀ c)           (⊑∀ p)     (⊑∀ q)     = ⊑∀ (⊔t-lub c p q)

  -- Slices of the same type are consistent
  ⊑t-consistent : ∀ {τ₁ τ₂ τ} → τ₁ ⊑t τ → τ₂ ⊑t τ → τ₁ ~ τ₂
  ⊑t-consistent ⊑?             _              = ~?ₗ
  ⊑t-consistent _              ⊑?             = ~?ᵣ
  ⊑t-consistent ⊑*             ⊑*             = ~*
  ⊑t-consistent ⊑Var           ⊑Var           = ~Var
  ⊑t-consistent (⊑+ p₁ p₂)     (⊑+ q₁ q₂)     = ~+ (⊑t-consistent p₁ q₁) (⊑t-consistent p₂ q₂)
  ⊑t-consistent (⊑× p₁ p₂)     (⊑× q₁ q₂)     = ~× (⊑t-consistent p₁ q₁) (⊑t-consistent p₂ q₂)
  ⊑t-consistent (⊑⇒ p₁ p₂)     (⊑⇒ q₁ q₂)     = ~⇒ (⊑t-consistent p₁ q₁) (⊑t-consistent p₂ q₂)
  ⊑t-consistent (⊑∀ p)         (⊑∀ q)         = ~∀ (⊑t-consistent p q)

  -- Joins preserve precision (for consistent types)
  ⊔t-preserves-⊑ : ∀ {τ₁ τ₂ τ} → τ₁ ⊑t τ → τ₂ ⊑t τ → τ₁ ⊔t τ₂ ⊑t τ
  ⊔t-preserves-⊑ p q = ⊔t-lub (⊑t-consistent p q) p q

  -- Meets (of slices of some type)
  open SliceOf

  _⊓tₛ_ : ∀ {τ} → ⌊ τ ⌋ → ⌊ τ ⌋ → ⌊ τ ⌋
  υ ⊓tₛ υ' = υ .↓ ⊓t υ' .↓ isSlice ⊓t-preserves-⊑-spec (υ .proof) (υ' .proof)

  infixl 6 _⊓tₛ_

  -- Joins (of slices of some type)
  _⊔tₛ_ : ∀ {τ} → ⌊ τ ⌋ → ⌊ τ ⌋ → ⌊ τ ⌋
  υ ⊔tₛ υ' = υ .↓ ⊔t υ' .↓ isSlice ⊔t-preserves-⊑ (υ .proof) (υ' .proof)

  infixl 7 _⊔tₛ_

  -- Slice meet is lower bound
  ⊓tₛ-lb₁ : ∀ {τ} (υ₁ υ₂ : ⌊ τ ⌋) → υ₁ ⊓tₛ υ₂ ⊑tₛ υ₁
  ⊓tₛ-lb₁ υ₁ υ₂ = ⊓t-lb₁ (υ₁ .↓) (υ₂ .↓)

  ⊓tₛ-lb₂ : ∀ {τ} (υ₁ υ₂ : ⌊ τ ⌋) → υ₁ ⊓tₛ υ₂ ⊑tₛ υ₂
  ⊓tₛ-lb₂ υ₁ υ₂ = ⊓t-lb₂ (υ₁ .↓) (υ₂ .↓)

  ⊓tₛ-glb : ∀ {τ} {υ υ₁ υ₂ : ⌊ τ ⌋} → υ ⊑tₛ υ₁ → υ ⊑tₛ υ₂ → υ ⊑tₛ υ₁ ⊓tₛ υ₂
  ⊓tₛ-glb = ⊓t-glb

  -- Slice join is upper bound
  ⊔tₛ-ub₁ : ∀ {τ} (υ₁ υ₂ : ⌊ τ ⌋) → υ₁ ⊑tₛ υ₁ ⊔tₛ υ₂
  ⊔tₛ-ub₁ υ₁ υ₂ = ⊔t-ub₁ (⊑t-consistent (υ₁ .proof) (υ₂ .proof))

  ⊔tₛ-ub₂ : ∀ {τ} (υ₁ υ₂ : ⌊ τ ⌋) → υ₂ ⊑tₛ υ₁ ⊔tₛ υ₂
  ⊔tₛ-ub₂ υ₁ υ₂ = ⊔t-ub₂ (⊑t-consistent (υ₁ .proof) (υ₂ .proof))

  ⊔tₛ-lub : ∀ {τ} {υ υ₁ υ₂ : ⌊ τ ⌋} → υ₁ ⊑tₛ υ → υ₂ ⊑tₛ υ → υ₁ ⊔tₛ υ₂ ⊑tₛ υ
  ⊔tₛ-lub {_} {υ} {υ₁} {υ₂} p q = ⊔t-lub (⊑t-consistent (υ₁ .proof) (υ₂ .proof)) p q

  -- Slice infimum and supremum
  ⊓tₛ-infimum : ∀ {τ} → Infimum (_⊑tₛ_ {τ}) _⊓tₛ_
  ⊓tₛ-infimum υ₁ υ₂ = ⊓tₛ-lb₁ υ₁ υ₂ , ⊓tₛ-lb₂ υ₁ υ₂ , λ υ → ⊓tₛ-glb {υ = υ} {υ₁} {υ₂}

  ⊔tₛ-supremum : ∀ {τ} → Supremum (_⊑tₛ_ {τ}) _⊔tₛ_
  ⊔tₛ-supremum υ₁ υ₂ = ⊔tₛ-ub₁ υ₁ υ₂ , ⊔tₛ-ub₂ υ₁ υ₂ , λ υ → ⊔tₛ-lub {υ = υ} {υ₁} {υ₂}

  -- Slice meet semilattice
  ⊓tₛ-isMeetSemilattice : ∀ {τ} → IsMeetSemilattice (_≡_ on ↓) (_⊑tₛ_ {τ}) _⊓tₛ_
  ⊓tₛ-isMeetSemilattice = record
    { isPartialOrder = ⊑tₛ-isPartialOrder
    ; infimum        = ⊓tₛ-infimum
    }

  -- Slice join semilattice
  ⊔tₛ-isJoinSemilattice : ∀ {τ} → IsJoinSemilattice (_≡_ on ↓) (_⊑tₛ_ {τ}) _⊔tₛ_
  ⊔tₛ-isJoinSemilattice = record
    { isPartialOrder = ⊑tₛ-isPartialOrder
    ; supremum       = ⊔tₛ-supremum
    }

  -- Full lattice on slices of a type
  ⊑tₛ-isLattice : ∀ {τ} → IsLattice (_≡_ on ↓) (_⊑tₛ_ {τ}) _⊔tₛ_ _⊓tₛ_
  ⊑tₛ-isLattice = record
    { isPartialOrder = ⊑tₛ-isPartialOrder
    ; supremum       = ⊔tₛ-supremum
    ; infimum        = ⊓tₛ-infimum
    }

  -- Bounded lattice: □ is bottom, τ is top
  ⊤ₛ : ∀ {τ} → ⌊ τ ⌋
  ⊤ₛ {τ} = τ isSlice ⊑t-refl

  ⊥ₛ : ∀ {τ} → ⌊ τ ⌋
  ⊥ₛ {τ} = □ isSlice ⊑?

  ⊤ₛ-maximum : ∀ {τ} → Maximum (_⊑tₛ_ {τ}) ⊤ₛ
  ⊤ₛ-maximum υ = υ .proof

  ⊥ₛ-minimum : ∀ {τ} → Minimum (_⊑tₛ_ {τ}) ⊥ₛ
  ⊥ₛ-minimum υ = ⊑?

  -- Bounded lattice on slices of a type
  ⊑tₛ-isBoundedLattice : ∀ {τ} → IsBoundedLattice (_≡_ on ↓) (_⊑tₛ_ {τ}) _⊔tₛ_ _⊓tₛ_ ⊤ₛ ⊥ₛ
  ⊑tₛ-isBoundedLattice = record
    { isLattice = ⊑tₛ-isLattice
    ; maximum   = ⊤ₛ-maximum
    ; minimum   = ⊥ₛ-minimum
    }

