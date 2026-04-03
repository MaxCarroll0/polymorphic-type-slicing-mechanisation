module core.Ctx.Lattice where

open import Data.Product using (_,_)
open import Relation.Binary using (IsPartialOrder)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Maximum; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans)
open import Relation.Binary.Lattice.Structures using (IsMeetSemilattice; IsJoinSemilattice; IsLattice; IsBoundedLattice)
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum)
open import Function using (_on_)

open import core.Typ using (Typ; _⊑t_; ⊑t-refl; ⊑t-trans;
                            _⊓t_; ⊓t-lb₁; ⊓t-lb₂; ⊓t-glb;
                            _⊔t_; ⊔t-ub₁; ⊔t-ub₂; ⊔t-preserves-⊑; ⊑t-consistent)
open import core.Exp using (Exp; _⊑e_; ⊑e-refl; ⊑e-trans;
                            _⊓e_; ⊓e-lb₁; ⊓e-lb₂; ⊓e-glb;
                            _⊔e_; ⊔e-ub₁; ⊔e-ub₂; ⊔e-preserves-⊑)
open import core.Ctx.Base
open import core.Ctx.Precision

-- Instantiate generic Slice module for contexts
open import Slice _⊑Ctx_ □Ctx □Ctx-min □Ctx-min-slice ⊑Ctx-refl ⊑Ctx-trans public
  renaming (SliceOf to SliceOfCtx; _⊑ₛ_ to _⊑Ctxₛ_; ⊤ₛ to ⊤Ctxₛ; ⊥ₛ to ⊥Ctxₛ;
            weaken to ⊑Ctxₛ-weaken; weaken-identity to ⊑Ctxₛ-weaken-identity;
            ⊥ₛ-min to ⊥Ctxₛ-min')

-- Lifted partial order on slices of a context
⊑Ctxₛ-refl : ∀ {C} → Reflexive (_⊑Ctxₛ_ {C})
⊑Ctxₛ-refl = ⊑Ctx-refl

⊑Ctxₛ-trans : ∀ {C} → Transitive (_⊑Ctxₛ_ {C})
⊑Ctxₛ-trans = ⊑Ctx-trans

⊑Ctxₛ-antisym : ∀ {C} → Antisymmetric (_≡_ on ↓) (_⊑Ctxₛ_ {C})
⊑Ctxₛ-antisym = ⊑Ctx-antisym

⊑Ctxₛ-isPartialOrder : ∀ {C} → IsPartialOrder (_≡_ on ↓) (_⊑Ctxₛ_ {C})
⊑Ctxₛ-isPartialOrder = record
  { isPreorder = record
    { isEquivalence = record
      { refl = refl ; sym = sym ; trans = trans }
    ; reflexive = λ where refl → ⊑Ctx-refl
    ; trans = λ {C''} {C'} {C} → ⊑Ctx-trans
    }
  ; antisym = λ {C'} {C} → ⊑Ctx-antisym
  }

-- Meets: only valid for same-constructor contexts (used in slice operations)
-- For different constructors, there is no lower bound in the partial order
_⊓Ctx_ : Ctx → Ctx → Ctx
○             ⊓Ctx ○             = ○
(λ· τ ⇒ C)    ⊓Ctx (λ· τ' ⇒ C')  = λ· (τ ⊓t τ') ⇒ (C ⊓Ctx C')
(C ∘ₗ e)      ⊓Ctx (C' ∘ₗ e')    = (C ⊓Ctx C') ∘ₗ (e ⊓e e')
(e ∘ᵣ C)      ⊓Ctx (e' ∘ᵣ C')    = (e ⊓e e') ∘ᵣ (C ⊓Ctx C')
(C &ₗ e)      ⊓Ctx (C' &ₗ e')    = (C ⊓Ctx C') &ₗ (e ⊓e e')
(e &ᵣ C)      ⊓Ctx (e' &ᵣ C')    = (e ⊓e e') &ᵣ (C ⊓Ctx C')
ιₗ C          ⊓Ctx ιₗ C'         = ιₗ (C ⊓Ctx C')
ιᵣ C          ⊓Ctx ιᵣ C'         = ιᵣ (C ⊓Ctx C')
Λ C           ⊓Ctx Λ C'          = Λ (C ⊓Ctx C')
(def C ⊢ₗ e)  ⊓Ctx (def C' ⊢ₗ e') = def (C ⊓Ctx C') ⊢ₗ (e ⊓e e')
(def e ⊢ᵣ C)  ⊓Ctx (def e' ⊢ᵣ C') = def (e ⊓e e') ⊢ᵣ (C ⊓Ctx C')
-- Incomparable cases: return the first operand as a fallback
C             ⊓Ctx _             = C

infixl 6 _⊓Ctx_

-- Joins: only valid for same-constructor contexts
_⊔Ctx_ : Ctx → Ctx → Ctx
○             ⊔Ctx ○             = ○
(λ· τ ⇒ C)    ⊔Ctx (λ· τ' ⇒ C')  = λ· (τ ⊔t τ') ⇒ (C ⊔Ctx C')
(C ∘ₗ e)      ⊔Ctx (C' ∘ₗ e')    = (C ⊔Ctx C') ∘ₗ (e ⊔e e')
(e ∘ᵣ C)      ⊔Ctx (e' ∘ᵣ C')    = (e ⊔e e') ∘ᵣ (C ⊔Ctx C')
(C &ₗ e)      ⊔Ctx (C' &ₗ e')    = (C ⊔Ctx C') &ₗ (e ⊔e e')
(e &ᵣ C)      ⊔Ctx (e' &ᵣ C')    = (e ⊔e e') &ᵣ (C ⊔Ctx C')
ιₗ C          ⊔Ctx ιₗ C'         = ιₗ (C ⊔Ctx C')
ιᵣ C          ⊔Ctx ιᵣ C'         = ιᵣ (C ⊔Ctx C')
Λ C           ⊔Ctx Λ C'          = Λ (C ⊔Ctx C')
(def C ⊢ₗ e)  ⊔Ctx (def C' ⊢ₗ e') = def (C ⊔Ctx C') ⊢ₗ (e ⊔e e')
(def e ⊢ᵣ C)  ⊔Ctx (def e' ⊢ᵣ C') = def (e ⊔e e') ⊢ᵣ (C ⊔Ctx C')
-- Incomparable: return first operand
C             ⊔Ctx _             = C

infixl 7 _⊔Ctx_

-- Meet GLB (for slices of the same context, where both have same constructor)
⊓Ctx-glb : ∀ {C C₁ C₂} → C ⊑Ctx C₁ → C ⊑Ctx C₂ → C ⊑Ctx C₁ ⊓Ctx C₂
⊓Ctx-glb ⊑○ ⊑○                       = ⊑○
⊓Ctx-glb (⊑λ p q) (⊑λ r s)           = ⊑λ (⊓t-glb p r) (⊓Ctx-glb q s)
⊓Ctx-glb (⊑∘ₗ p q) (⊑∘ₗ r s)         = ⊑∘ₗ (⊓Ctx-glb p r) (⊓e-glb q s)
⊓Ctx-glb (⊑∘ᵣ p q) (⊑∘ᵣ r s)         = ⊑∘ᵣ (⊓e-glb p r) (⊓Ctx-glb q s)
⊓Ctx-glb (⊑&ₗ p q) (⊑&ₗ r s)         = ⊑&ₗ (⊓Ctx-glb p r) (⊓e-glb q s)
⊓Ctx-glb (⊑&ᵣ p q) (⊑&ᵣ r s)         = ⊑&ᵣ (⊓e-glb p r) (⊓Ctx-glb q s)
⊓Ctx-glb (⊑ιₗ p) (⊑ιₗ q)             = ⊑ιₗ (⊓Ctx-glb p q)
⊓Ctx-glb (⊑ιᵣ p) (⊑ιᵣ q)             = ⊑ιᵣ (⊓Ctx-glb p q)
⊓Ctx-glb (⊑Λ p) (⊑Λ q)               = ⊑Λ (⊓Ctx-glb p q)
⊓Ctx-glb (⊑defₗ p q) (⊑defₗ r s)     = ⊑defₗ (⊓Ctx-glb p r) (⊓e-glb q s)
⊓Ctx-glb (⊑defᵣ p q) (⊑defᵣ r s)     = ⊑defᵣ (⊓e-glb p r) (⊓Ctx-glb q s)

-- Meet lower bounds (for slices of the same context)
⊓Ctx-lb₁' : ∀ {C₁ C₂ C} → C₁ ⊑Ctx C → C₂ ⊑Ctx C → C₁ ⊓Ctx C₂ ⊑Ctx C₁
⊓Ctx-lb₁' ⊑○ ⊑○                                             = ⊑○
⊓Ctx-lb₁' (⊑λ {τ₁} p q) (⊑λ {τ₂} r s)                       = ⊑λ (⊓t-lb₁ τ₁ τ₂) (⊓Ctx-lb₁' q s)
⊓Ctx-lb₁' (⊑∘ₗ {e = e₁} p q) (⊑∘ₗ {e = e₂} r s)             = ⊑∘ₗ (⊓Ctx-lb₁' p r) (⊓e-lb₁ e₁ e₂)
⊓Ctx-lb₁' (⊑∘ᵣ {e₁} p q) (⊑∘ᵣ {e₂} r s)                     = ⊑∘ᵣ (⊓e-lb₁ e₁ e₂) (⊓Ctx-lb₁' q s)
⊓Ctx-lb₁' (⊑&ₗ {e = e₁} p q) (⊑&ₗ {e = e₂} r s)             = ⊑&ₗ (⊓Ctx-lb₁' p r) (⊓e-lb₁ e₁ e₂)
⊓Ctx-lb₁' (⊑&ᵣ {e₁} p q) (⊑&ᵣ {e₂} r s)                     = ⊑&ᵣ (⊓e-lb₁ e₁ e₂) (⊓Ctx-lb₁' q s)
⊓Ctx-lb₁' (⊑ιₗ p) (⊑ιₗ q)                                   = ⊑ιₗ (⊓Ctx-lb₁' p q)
⊓Ctx-lb₁' (⊑ιᵣ p) (⊑ιᵣ q)                                   = ⊑ιᵣ (⊓Ctx-lb₁' p q)
⊓Ctx-lb₁' (⊑Λ p) (⊑Λ q)                                     = ⊑Λ (⊓Ctx-lb₁' p q)
⊓Ctx-lb₁' (⊑defₗ {e = e₁} p q) (⊑defₗ {e = e₂} r s)         = ⊑defₗ (⊓Ctx-lb₁' p r) (⊓e-lb₁ e₁ e₂)
⊓Ctx-lb₁' (⊑defᵣ {e₁} p q) (⊑defᵣ {e₂} r s)                 = ⊑defᵣ (⊓e-lb₁ e₁ e₂) (⊓Ctx-lb₁' q s)

⊓Ctx-lb₂' : ∀ {C₁ C₂ C} → C₁ ⊑Ctx C → C₂ ⊑Ctx C → C₁ ⊓Ctx C₂ ⊑Ctx C₂
⊓Ctx-lb₂' ⊑○ ⊑○                                             = ⊑○
⊓Ctx-lb₂' (⊑λ {τ₁} p q) (⊑λ {τ₂} r s)                       = ⊑λ (⊓t-lb₂ τ₁ τ₂) (⊓Ctx-lb₂' q s)
⊓Ctx-lb₂' (⊑∘ₗ {e = e₁} p q) (⊑∘ₗ {e = e₂} r s)             = ⊑∘ₗ (⊓Ctx-lb₂' p r) (⊓e-lb₂ e₁ e₂)
⊓Ctx-lb₂' (⊑∘ᵣ {e₁} p q) (⊑∘ᵣ {e₂} r s)                     = ⊑∘ᵣ (⊓e-lb₂ e₁ e₂) (⊓Ctx-lb₂' q s)
⊓Ctx-lb₂' (⊑&ₗ {e = e₁} p q) (⊑&ₗ {e = e₂} r s)             = ⊑&ₗ (⊓Ctx-lb₂' p r) (⊓e-lb₂ e₁ e₂)
⊓Ctx-lb₂' (⊑&ᵣ {e₁} p q) (⊑&ᵣ {e₂} r s)                     = ⊑&ᵣ (⊓e-lb₂ e₁ e₂) (⊓Ctx-lb₂' q s)
⊓Ctx-lb₂' (⊑ιₗ p) (⊑ιₗ q)                                   = ⊑ιₗ (⊓Ctx-lb₂' p q)
⊓Ctx-lb₂' (⊑ιᵣ p) (⊑ιᵣ q)                                   = ⊑ιᵣ (⊓Ctx-lb₂' p q)
⊓Ctx-lb₂' (⊑Λ p) (⊑Λ q)                                     = ⊑Λ (⊓Ctx-lb₂' p q)
⊓Ctx-lb₂' (⊑defₗ {e = e₁} p q) (⊑defₗ {e = e₂} r s)         = ⊑defₗ (⊓Ctx-lb₂' p r) (⊓e-lb₂ e₁ e₂)
⊓Ctx-lb₂' (⊑defᵣ {e₁} p q) (⊑defᵣ {e₂} r s)                 = ⊑defᵣ (⊓e-lb₂ e₁ e₂) (⊓Ctx-lb₂' q s)

-- Meet preserves precision (for slices of the same context)
⊓Ctx-preserves-⊑ : ∀ {C₁ C₂ C : Ctx} → C₁ ⊑Ctx C → C₂ ⊑Ctx C → C₁ ⊓Ctx C₂ ⊑Ctx C
⊓Ctx-preserves-⊑ p q = ⊑Ctx-trans (⊓Ctx-lb₁' p q) p

-- Join upper bounds (for slices of the same context)
⊔Ctx-ub₁' : ∀ {C₁ C₂ C} → C₁ ⊑Ctx C → C₂ ⊑Ctx C → C₁ ⊑Ctx C₁ ⊔Ctx C₂
⊔Ctx-ub₁' ⊑○ ⊑○                       = ⊑○
⊔Ctx-ub₁' (⊑λ p q) (⊑λ r s)           = ⊑λ (⊔t-ub₁ (⊑t-consistent p r)) (⊔Ctx-ub₁' q s)
⊔Ctx-ub₁' (⊑∘ₗ p q) (⊑∘ₗ r s)         = ⊑∘ₗ (⊔Ctx-ub₁' p r) (⊔e-ub₁ q s)
⊔Ctx-ub₁' (⊑∘ᵣ p q) (⊑∘ᵣ r s)         = ⊑∘ᵣ (⊔e-ub₁ p r) (⊔Ctx-ub₁' q s)
⊔Ctx-ub₁' (⊑&ₗ p q) (⊑&ₗ r s)         = ⊑&ₗ (⊔Ctx-ub₁' p r) (⊔e-ub₁ q s)
⊔Ctx-ub₁' (⊑&ᵣ p q) (⊑&ᵣ r s)         = ⊑&ᵣ (⊔e-ub₁ p r) (⊔Ctx-ub₁' q s)
⊔Ctx-ub₁' (⊑ιₗ p) (⊑ιₗ q)             = ⊑ιₗ (⊔Ctx-ub₁' p q)
⊔Ctx-ub₁' (⊑ιᵣ p) (⊑ιᵣ q)             = ⊑ιᵣ (⊔Ctx-ub₁' p q)
⊔Ctx-ub₁' (⊑Λ p) (⊑Λ q)               = ⊑Λ (⊔Ctx-ub₁' p q)
⊔Ctx-ub₁' (⊑defₗ p q) (⊑defₗ r s)     = ⊑defₗ (⊔Ctx-ub₁' p r) (⊔e-ub₁ q s)
⊔Ctx-ub₁' (⊑defᵣ p q) (⊑defᵣ r s)     = ⊑defᵣ (⊔e-ub₁ p r) (⊔Ctx-ub₁' q s)

⊔Ctx-ub₂' : ∀ {C₁ C₂ C} → C₁ ⊑Ctx C → C₂ ⊑Ctx C → C₂ ⊑Ctx C₁ ⊔Ctx C₂
⊔Ctx-ub₂' ⊑○ ⊑○                       = ⊑○
⊔Ctx-ub₂' (⊑λ p q) (⊑λ r s)           = ⊑λ (⊔t-ub₂ (⊑t-consistent p r)) (⊔Ctx-ub₂' q s)
⊔Ctx-ub₂' (⊑∘ₗ p q) (⊑∘ₗ r s)         = ⊑∘ₗ (⊔Ctx-ub₂' p r) (⊔e-ub₂ q s)
⊔Ctx-ub₂' (⊑∘ᵣ p q) (⊑∘ᵣ r s)         = ⊑∘ᵣ (⊔e-ub₂ p r) (⊔Ctx-ub₂' q s)
⊔Ctx-ub₂' (⊑&ₗ p q) (⊑&ₗ r s)         = ⊑&ₗ (⊔Ctx-ub₂' p r) (⊔e-ub₂ q s)
⊔Ctx-ub₂' (⊑&ᵣ p q) (⊑&ᵣ r s)         = ⊑&ᵣ (⊔e-ub₂ p r) (⊔Ctx-ub₂' q s)
⊔Ctx-ub₂' (⊑ιₗ p) (⊑ιₗ q)             = ⊑ιₗ (⊔Ctx-ub₂' p q)
⊔Ctx-ub₂' (⊑ιᵣ p) (⊑ιᵣ q)             = ⊑ιᵣ (⊔Ctx-ub₂' p q)
⊔Ctx-ub₂' (⊑Λ p) (⊑Λ q)               = ⊑Λ (⊔Ctx-ub₂' p q)
⊔Ctx-ub₂' (⊑defₗ p q) (⊑defₗ r s)     = ⊑defₗ (⊔Ctx-ub₂' p r) (⊔e-ub₂ q s)
⊔Ctx-ub₂' (⊑defᵣ p q) (⊑defᵣ r s)     = ⊑defᵣ (⊔e-ub₂ p r) (⊔Ctx-ub₂' q s)

-- Join preserves precision (for slices of the same context)
⊔Ctx-preserves-⊑ : ∀ {C₁ C₂ C} → C₁ ⊑Ctx C → C₂ ⊑Ctx C → C₁ ⊔Ctx C₂ ⊑Ctx C
⊔Ctx-preserves-⊑ ⊑○ ⊑○                       = ⊑○
⊔Ctx-preserves-⊑ (⊑λ p q) (⊑λ r s)           = ⊑λ (⊔t-preserves-⊑ p r) (⊔Ctx-preserves-⊑ q s)
⊔Ctx-preserves-⊑ (⊑∘ₗ p q) (⊑∘ₗ r s)         = ⊑∘ₗ (⊔Ctx-preserves-⊑ p r) (⊔e-preserves-⊑ q s)
⊔Ctx-preserves-⊑ (⊑∘ᵣ p q) (⊑∘ᵣ r s)         = ⊑∘ᵣ (⊔e-preserves-⊑ p r) (⊔Ctx-preserves-⊑ q s)
⊔Ctx-preserves-⊑ (⊑&ₗ p q) (⊑&ₗ r s)         = ⊑&ₗ (⊔Ctx-preserves-⊑ p r) (⊔e-preserves-⊑ q s)
⊔Ctx-preserves-⊑ (⊑&ᵣ p q) (⊑&ᵣ r s)         = ⊑&ᵣ (⊔e-preserves-⊑ p r) (⊔Ctx-preserves-⊑ q s)
⊔Ctx-preserves-⊑ (⊑ιₗ p) (⊑ιₗ q)             = ⊑ιₗ (⊔Ctx-preserves-⊑ p q)
⊔Ctx-preserves-⊑ (⊑ιᵣ p) (⊑ιᵣ q)             = ⊑ιᵣ (⊔Ctx-preserves-⊑ p q)
⊔Ctx-preserves-⊑ (⊑Λ p) (⊑Λ q)               = ⊑Λ (⊔Ctx-preserves-⊑ p q)
⊔Ctx-preserves-⊑ (⊑defₗ p q) (⊑defₗ r s)     = ⊑defₗ (⊔Ctx-preserves-⊑ p r) (⊔e-preserves-⊑ q s)
⊔Ctx-preserves-⊑ (⊑defᵣ p q) (⊑defᵣ r s)     = ⊑defᵣ (⊔e-preserves-⊑ p r) (⊔Ctx-preserves-⊑ q s)

-- Slice meet/join operations
_⊓Ctxₛ_ : ∀ {C} → ⌊ C ⌋ → ⌊ C ⌋ → ⌊ C ⌋
υ ⊓Ctxₛ υ' = υ .↓ ⊓Ctx υ' .↓ isSlice ⊓Ctx-preserves-⊑ (υ .proof) (υ' .proof)

infixl 6 _⊓Ctxₛ_

_⊔Ctxₛ_ : ∀ {C} → ⌊ C ⌋ → ⌊ C ⌋ → ⌊ C ⌋
υ ⊔Ctxₛ υ' = υ .↓ ⊔Ctx υ' .↓ isSlice ⊔Ctx-preserves-⊑ (υ .proof) (υ' .proof)

infixl 7 _⊔Ctxₛ_

-- Slice meet lower bounds
⊓Ctxₛ-lb₁ : ∀ {C} (υ₁ υ₂ : ⌊ C ⌋) → υ₁ ⊓Ctxₛ υ₂ ⊑Ctxₛ υ₁
⊓Ctxₛ-lb₁ υ₁ υ₂ = ⊓Ctx-lb₁' (υ₁ .proof) (υ₂ .proof)

⊓Ctxₛ-lb₂ : ∀ {C} (υ₁ υ₂ : ⌊ C ⌋) → υ₁ ⊓Ctxₛ υ₂ ⊑Ctxₛ υ₂
⊓Ctxₛ-lb₂ υ₁ υ₂ = ⊓Ctx-lb₂' (υ₁ .proof) (υ₂ .proof)

⊓Ctxₛ-glb : ∀ {C} {υ υ₁ υ₂ : ⌊ C ⌋} → υ ⊑Ctxₛ υ₁ → υ ⊑Ctxₛ υ₂ → υ ⊑Ctxₛ υ₁ ⊓Ctxₛ υ₂
⊓Ctxₛ-glb = ⊓Ctx-glb

-- Slice join upper bounds
⊔Ctxₛ-ub₁ : ∀ {C} (υ₁ υ₂ : ⌊ C ⌋) → υ₁ ⊑Ctxₛ υ₁ ⊔Ctxₛ υ₂
⊔Ctxₛ-ub₁ υ₁ υ₂ = ⊔Ctx-ub₁' (υ₁ .proof) (υ₂ .proof)

⊔Ctxₛ-ub₂ : ∀ {C} (υ₁ υ₂ : ⌊ C ⌋) → υ₂ ⊑Ctxₛ υ₁ ⊔Ctxₛ υ₂
⊔Ctxₛ-ub₂ υ₁ υ₂ = ⊔Ctx-ub₂' (υ₁ .proof) (υ₂ .proof)

⊔Ctxₛ-lub : ∀ {C} {υ υ₁ υ₂ : ⌊ C ⌋} → υ₁ ⊑Ctxₛ υ → υ₂ ⊑Ctxₛ υ → υ₁ ⊔Ctxₛ υ₂ ⊑Ctxₛ υ
⊔Ctxₛ-lub {_} {υ} {υ₁} {υ₂} p q = ⊔Ctx-preserves-⊑ p q

-- Slice infimum and supremum
⊓Ctxₛ-infimum : ∀ {C} → Infimum (_⊑Ctxₛ_ {C}) _⊓Ctxₛ_
⊓Ctxₛ-infimum υ₁ υ₂ = ⊓Ctxₛ-lb₁ υ₁ υ₂ , ⊓Ctxₛ-lb₂ υ₁ υ₂ , λ υ → ⊓Ctxₛ-glb {υ = υ} {υ₁} {υ₂}

⊔Ctxₛ-supremum : ∀ {C} → Supremum (_⊑Ctxₛ_ {C}) _⊔Ctxₛ_
⊔Ctxₛ-supremum υ₁ υ₂ = ⊔Ctxₛ-ub₁ υ₁ υ₂ , ⊔Ctxₛ-ub₂ υ₁ υ₂ , λ υ → ⊔Ctxₛ-lub {υ = υ} {υ₁} {υ₂}

-- Slice meet semilattice
⊓Ctxₛ-isMeetSemilattice : ∀ {C} → IsMeetSemilattice (_≡_ on ↓) (_⊑Ctxₛ_ {C}) _⊓Ctxₛ_
⊓Ctxₛ-isMeetSemilattice = record
  { isPartialOrder = ⊑Ctxₛ-isPartialOrder
  ; infimum        = ⊓Ctxₛ-infimum
  }

-- Slice join semilattice
⊔Ctxₛ-isJoinSemilattice : ∀ {C} → IsJoinSemilattice (_≡_ on ↓) (_⊑Ctxₛ_ {C}) _⊔Ctxₛ_
⊔Ctxₛ-isJoinSemilattice = record
  { isPartialOrder = ⊑Ctxₛ-isPartialOrder
  ; supremum       = ⊔Ctxₛ-supremum
  }

-- Full lattice on slices of a context
⊑Ctxₛ-isLattice : ∀ {C} → IsLattice (_≡_ on ↓) (_⊑Ctxₛ_ {C}) _⊔Ctxₛ_ _⊓Ctxₛ_
⊑Ctxₛ-isLattice = record
  { isPartialOrder = ⊑Ctxₛ-isPartialOrder
  ; supremum       = ⊔Ctxₛ-supremum
  ; infimum        = ⊓Ctxₛ-infimum
  }

-- Bounded lattice: □Ctx C is bottom, C is top
⊤Ctxₛ-maximum : ∀ {C} → Maximum (_⊑Ctxₛ_ {C}) ⊤Ctxₛ
⊤Ctxₛ-maximum υ = υ .proof

⊥Ctxₛ-minimum : ∀ {C} → Minimum (_⊑Ctxₛ_ {C}) ⊥Ctxₛ
⊥Ctxₛ-minimum υ = □Ctx-min-slice (υ .proof)

-- Bounded lattice on slices of a context
⊑Ctxₛ-isBoundedLattice : ∀ {C} → IsBoundedLattice (_≡_ on ↓) (_⊑Ctxₛ_ {C}) _⊔Ctxₛ_ _⊓Ctxₛ_ ⊤Ctxₛ ⊥Ctxₛ
⊑Ctxₛ-isBoundedLattice = record
  { isLattice = ⊑Ctxₛ-isLattice
  ; maximum   = ⊤Ctxₛ-maximum
  ; minimum   = ⊥Ctxₛ-minimum
  }
