module Core.Ctx.Lattice where

open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary using (IsPartialOrder)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Maximum; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Relation.Binary.Lattice.Structures using (IsMeetSemilattice; IsJoinSemilattice; IsLattice; IsBoundedLattice; IsDistributiveLattice)
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum)
open import Function using (_on_)

open import Core.Typ using (Typ)
  renaming (⊑□ to ⊑t□; _⊑_ to _⊑t_; _⊓_ to _⊓t_; _⊔_ to _⊔t_;
            module ⊑ₛLat to ⊑tₛLat; module ⊑ to ⊑t; module ⊑ₛ to ⊑tₛ;
            _isSlice_ to _isSlicet_; ↑ to ↑t)
open import Core.Exp using (Exp)
  renaming (⊑□ to ⊑e□; _⊑_ to _⊑e_; _⊓_ to _⊓e_; _⊔_ to _⊔e_;
            module ⊑ₛLat to ⊑eₛLat; module ⊑ to ⊑e; module ⊑ₛ to ⊑eₛ;
            _isSlice_ to _isSlicee_; ↑ to ↑e)
open import Core.Ctx.Base
open import Core.Ctx.Equality using () renaming (_≟_ to _≟Ctx_)
open import Core.Ctx.Precision renaming (⊤ₛ to ⊤ₛ')

-- Meet operator
-- TODO: consider returning Maybe Ctx to distinguish meet failure from ○
_⊓_ : Ctx → Ctx → Ctx
C ⊓ C' with diag C C'
...       | diff                                   = ○
...       | kind○                                  = ○
...       | kindλ  {τ} {τ'} {C₁} {C₁'}             = λ: (τ ⊓t τ') ⇒ (C₁ ⊓ C₁')
...       | kindλu {C₁} {C₁'}                      = λ⇒ (C₁ ⊓ C₁')
...       | kind∘₁ {C₁} {C₁'} {e} {e'}             = (C₁ ⊓ C₁') ∘₁ (e ⊓e e')
...       | kind∘₂ {e} {e'} {C₁} {C₁'}             = (e ⊓e e') ∘₂ (C₁ ⊓ C₁')
...       | kind<>₁ {C₁} {C₁'} {τ} {τ'}            = (C₁ ⊓ C₁') < (τ ⊓t τ') >₁
...       | kind&₁ {C₁} {C₁'} {e} {e'}             = (C₁ ⊓ C₁') &₁ (e ⊓e e')
...       | kind&₂ {e} {e'} {C₁} {C₁'}             = (e ⊓e e') &₂ (C₁ ⊓ C₁')
...       | kindι₁ {C₁} {C₁'}                      = ι₁ (C₁ ⊓ C₁')
...       | kindι₂ {C₁} {C₁'}                      = ι₂ (C₁ ⊓ C₁')
...       | kindcase₁ {e} {e'} {C₁} {C₁'} {f} {f'} = case (e ⊓e e') of (C₁ ⊓ C₁') ·₁ (f ⊓e f')
...       | kindcase₂ {e} {e'} {f} {f'} {C₁} {C₁'} = case (e ⊓e e') of₂ (f ⊓e f') · (C₁ ⊓ C₁')
...       | kindπ₁ {C₁} {C₁'}                      = π₁ (C₁ ⊓ C₁')
...       | kindπ₂ {C₁} {C₁'}                      = π₂ (C₁ ⊓ C₁')
...       | kindΛ  {C₁} {C₁'}                      = Λ (C₁ ⊓ C₁')
...       | kinddef₁ {C₁} {C₁'} {e} {e'}           = def (C₁ ⊓ C₁') ⊢₁ (e ⊓e e')
...       | kinddef₂ {e} {e'} {C₁} {C₁'}           = def (e ⊓e e') ⊢₂ (C₁ ⊓ C₁')

infixl 6 _⊓_

-- Join operator
_⊔_ : Ctx → Ctx → Ctx
C ⊔ C' with diag C C'
...       | kind○                                  = ○
...       | kindλ  {τ} {τ'} {C₁} {C₁'}             = λ: (τ ⊔t τ') ⇒ (C₁ ⊔ C₁')
...       | kindλu {C₁} {C₁'}                      = λ⇒ (C₁ ⊔ C₁')
...       | kind∘₁ {C₁} {C₁'} {e} {e'}             = (C₁ ⊔ C₁') ∘₁ (e ⊔e e')
...       | kind∘₂ {e} {e'} {C₁} {C₁'}             = (e ⊔e e') ∘₂ (C₁ ⊔ C₁')
...       | kind<>₁ {C₁} {C₁'} {τ} {τ'}            = (C₁ ⊔ C₁') < (τ ⊔t τ') >₁
...       | kind&₁ {C₁} {C₁'} {e} {e'}             = (C₁ ⊔ C₁') &₁ (e ⊔e e')
...       | kind&₂ {e} {e'} {C₁} {C₁'}             = (e ⊔e e') &₂ (C₁ ⊔ C₁')
...       | kindι₁ {C₁} {C₁'}                      = ι₁ (C₁ ⊔ C₁')
...       | kindι₂ {C₁} {C₁'}                      = ι₂ (C₁ ⊔ C₁')
...       | kindcase₁ {e} {e'} {C₁} {C₁'} {f} {f'} = case (e ⊔e e') of (C₁ ⊔ C₁') ·₁ (f ⊔e f')
...       | kindcase₂ {e} {e'} {f} {f'} {C₁} {C₁'} = case (e ⊔e e') of₂ (f ⊔e f') · (C₁ ⊔ C₁')
...       | kindπ₁ {C₁} {C₁'}                      = π₁ (C₁ ⊔ C₁')
...       | kindπ₂ {C₁} {C₁'}                      = π₂ (C₁ ⊔ C₁')
...       | kindΛ  {C₁} {C₁'}                      = Λ (C₁ ⊔ C₁')
...       | kinddef₁ {C₁} {C₁'} {e} {e'}           = def (C₁ ⊔ C₁') ⊢₁ (e ⊔e e')
...       | kinddef₂ {e} {e'} {C₁} {C₁'}           = def (e ⊔e e') ⊢₂ (C₁ ⊔ C₁')
...       | diff                                   = ○

infixl 6 _⊔_

private
  -- Meet lower bounds (bounded hypotheses since no global bottom)
  ⊓-lb₁ : ∀ {C₁ C₂ C} → C₁ ⊑ C → C₂ ⊑ C → C₁ ⊓ C₂ ⊑ C₁
  ⊓-lb₁ ⊑○ ⊑○                                     = ⊑○
  ⊓-lb₁ (⊑λ p₁ q₁)       (⊑λ p₂ q₂)               = ⊑λ (⊑tₛLat.x⊓ₛy⊑ₛx (↑t p₁) (↑t p₂)) (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑λu q₁)         (⊑λu q₂)                 = ⊑λu (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑∘₁ q₁ p₁)      (⊑∘₁ q₂ p₂)              = ⊑∘₁ (⊓-lb₁ q₁ q₂) (⊑eₛLat.x⊓ₛy⊑ₛx (↑e p₁) (↑e p₂))
  ⊓-lb₁ (⊑∘₂ p₁ q₁)      (⊑∘₂ p₂ q₂)              = ⊑∘₂ (⊑eₛLat.x⊓ₛy⊑ₛx (↑e p₁) (↑e p₂)) (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑<>₁ q₁ p₁)     (⊑<>₁ q₂ p₂)             = ⊑<>₁ (⊓-lb₁ q₁ q₂) (⊑tₛLat.x⊓ₛy⊑ₛx (↑t p₁) (↑t p₂))
  ⊓-lb₁ (⊑&₁ q₁ p₁)      (⊑&₁ q₂ p₂)              = ⊑&₁ (⊓-lb₁ q₁ q₂) (⊑eₛLat.x⊓ₛy⊑ₛx (↑e p₁) (↑e p₂))
  ⊓-lb₁ (⊑&₂ p₁ q₁)      (⊑&₂ p₂ q₂)              = ⊑&₂ (⊑eₛLat.x⊓ₛy⊑ₛx (↑e p₁) (↑e p₂)) (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑ι₁ q₁)         (⊑ι₁ q₂)                 = ⊑ι₁ (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑ι₂ q₁)         (⊑ι₂ q₂)                 = ⊑ι₂ (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂)       = ⊑case₁ (⊑eₛLat.x⊓ₛy⊑ₛx (↑e p₁) (↑e p₂)) (⊓-lb₁ q₁ q₂) (⊑eₛLat.x⊓ₛy⊑ₛx (↑e r₁) (↑e r₂))
  ⊓-lb₁ (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂)       = ⊑case₂ (⊑eₛLat.x⊓ₛy⊑ₛx (↑e p₁) (↑e p₂)) (⊑eₛLat.x⊓ₛy⊑ₛx (↑e r₁) (↑e r₂)) (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑π₁ q₁)         (⊑π₁ q₂)                 = ⊑π₁ (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑π₂ q₁)         (⊑π₂ q₂)                 = ⊑π₂ (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑Λ q₁)          (⊑Λ q₂)                  = ⊑Λ (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑def₁ q₁ p₁)    (⊑def₁ q₂ p₂)            = ⊑def₁ (⊓-lb₁ q₁ q₂) (⊑eₛLat.x⊓ₛy⊑ₛx (↑e p₁) (↑e p₂))
  ⊓-lb₁ (⊑def₂ p₁ q₁)    (⊑def₂ p₂ q₂)            = ⊑def₂ (⊑eₛLat.x⊓ₛy⊑ₛx (↑e p₁) (↑e p₂)) (⊓-lb₁ q₁ q₂)

  ⊓-lb₂ : ∀ {C₁ C₂ C} → C₁ ⊑ C → C₂ ⊑ C → C₁ ⊓ C₂ ⊑ C₂
  ⊓-lb₂ ⊑○ ⊑○                                     = ⊑○
  ⊓-lb₂ (⊑λ p₁ q₁)       (⊑λ p₂ q₂)               = ⊑λ (⊑tₛLat.x⊓ₛy⊑ₛy (↑t p₁) (↑t p₂)) (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑λu q₁)         (⊑λu q₂)                 = ⊑λu (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑∘₁ q₁ p₁)      (⊑∘₁ q₂ p₂)              = ⊑∘₁ (⊓-lb₂ q₁ q₂) (⊑eₛLat.x⊓ₛy⊑ₛy (↑e p₁) (↑e p₂))
  ⊓-lb₂ (⊑∘₂ p₁ q₁)      (⊑∘₂ p₂ q₂)              = ⊑∘₂ (⊑eₛLat.x⊓ₛy⊑ₛy (↑e p₁) (↑e p₂)) (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑<>₁ q₁ p₁)     (⊑<>₁ q₂ p₂)             = ⊑<>₁ (⊓-lb₂ q₁ q₂) (⊑tₛLat.x⊓ₛy⊑ₛy (↑t p₁) (↑t p₂))
  ⊓-lb₂ (⊑&₁ q₁ p₁)      (⊑&₁ q₂ p₂)              = ⊑&₁ (⊓-lb₂ q₁ q₂) (⊑eₛLat.x⊓ₛy⊑ₛy (↑e p₁) (↑e p₂))
  ⊓-lb₂ (⊑&₂ p₁ q₁)      (⊑&₂ p₂ q₂)              = ⊑&₂ (⊑eₛLat.x⊓ₛy⊑ₛy (↑e p₁) (↑e p₂)) (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑ι₁ q₁)         (⊑ι₁ q₂)                 = ⊑ι₁ (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑ι₂ q₁)         (⊑ι₂ q₂)                 = ⊑ι₂ (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂)       = ⊑case₁ (⊑eₛLat.x⊓ₛy⊑ₛy (↑e p₁) (↑e p₂)) (⊓-lb₂ q₁ q₂) (⊑eₛLat.x⊓ₛy⊑ₛy (↑e r₁) (↑e r₂))
  ⊓-lb₂ (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂)       = ⊑case₂ (⊑eₛLat.x⊓ₛy⊑ₛy (↑e p₁) (↑e p₂)) (⊑eₛLat.x⊓ₛy⊑ₛy (↑e r₁) (↑e r₂)) (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑π₁ q₁)         (⊑π₁ q₂)                 = ⊑π₁ (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑π₂ q₁)         (⊑π₂ q₂)                 = ⊑π₂ (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑Λ q₁)          (⊑Λ q₂)                  = ⊑Λ (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑def₁ q₁ p₁)    (⊑def₁ q₂ p₂)            = ⊑def₁ (⊓-lb₂ q₁ q₂) (⊑eₛLat.x⊓ₛy⊑ₛy (↑e p₁) (↑e p₂))
  ⊓-lb₂ (⊑def₂ p₁ q₁)    (⊑def₂ p₂ q₂)            = ⊑def₂ (⊑eₛLat.x⊓ₛy⊑ₛy (↑e p₁) (↑e p₂)) (⊓-lb₂ q₁ q₂)

  -- Meet is greatest lower bound
  ⊓-glb : ∀ {C C₁ C₂ C'} → C₁ ⊑ C' → C₂ ⊑ C' → C ⊑ C₁ → C ⊑ C₂ → C ⊑ C₁ ⊓ C₂
  ⊓-glb ⊑○               ⊑○               ⊑○              ⊑○              = ⊑○
  ⊓-glb (⊑λ p₁' q₁')    (⊑λ p₂' q₂')    (⊑λ p₁ q₁)     (⊑λ p₂ q₂)
    = ⊑λ (⊑tₛLat.⊓ₛ-greatest {x = ↑t (⊑t.trans p₁ p₁')} {↑t p₁'} {↑t p₂'} p₁ p₂)
         (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑λu q₁')       (⊑λu q₂')       (⊑λu q₁)       (⊑λu q₂)       = ⊑λu (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑∘₁ q₁' p₁')   (⊑∘₁ q₂' p₂')   (⊑∘₁ q₁ p₁)    (⊑∘₁ q₂ p₂)
    = ⊑∘₁ (⊓-glb q₁' q₂' q₁ q₂)
          (⊑eₛLat.⊓ₛ-greatest {x = ↑e (⊑e.trans p₁ p₁')} {↑e p₁'} {↑e p₂'} p₁ p₂)
  ⊓-glb (⊑∘₂ p₁' q₁')   (⊑∘₂ p₂' q₂')   (⊑∘₂ p₁ q₁)    (⊑∘₂ p₂ q₂)
    = ⊑∘₂ (⊑eₛLat.⊓ₛ-greatest {x = ↑e (⊑e.trans p₁ p₁')} {↑e p₁'} {↑e p₂'} p₁ p₂)
          (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑<>₁ q₁' p₁')  (⊑<>₁ q₂' p₂')  (⊑<>₁ q₁ p₁)   (⊑<>₁ q₂ p₂)
    = ⊑<>₁ (⊓-glb q₁' q₂' q₁ q₂)
           (⊑tₛLat.⊓ₛ-greatest {x = ↑t (⊑t.trans p₁ p₁')} {↑t p₁'} {↑t p₂'} p₁ p₂)
  ⊓-glb (⊑&₁ q₁' p₁')   (⊑&₁ q₂' p₂')   (⊑&₁ q₁ p₁)    (⊑&₁ q₂ p₂)
    = ⊑&₁ (⊓-glb q₁' q₂' q₁ q₂)
          (⊑eₛLat.⊓ₛ-greatest {x = ↑e (⊑e.trans p₁ p₁')} {↑e p₁'} {↑e p₂'} p₁ p₂)
  ⊓-glb (⊑&₂ p₁' q₁')   (⊑&₂ p₂' q₂')   (⊑&₂ p₁ q₁)    (⊑&₂ p₂ q₂)
    = ⊑&₂ (⊑eₛLat.⊓ₛ-greatest {x = ↑e (⊑e.trans p₁ p₁')} {↑e p₁'} {↑e p₂'} p₁ p₂)
          (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑ι₁ q₁')       (⊑ι₁ q₂')       (⊑ι₁ q₁)       (⊑ι₁ q₂)       = ⊑ι₁ (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑ι₂ q₁')       (⊑ι₂ q₂')       (⊑ι₂ q₁)       (⊑ι₂ q₂)       = ⊑ι₂ (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑case₁ p₁' q₁' r₁') (⊑case₁ p₂' q₂' r₂') (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂)
    = ⊑case₁ (⊑eₛLat.⊓ₛ-greatest {x = ↑e (⊑e.trans p₁ p₁')} {↑e p₁'} {↑e p₂'} p₁ p₂)
             (⊓-glb q₁' q₂' q₁ q₂)
             (⊑eₛLat.⊓ₛ-greatest {x = ↑e (⊑e.trans r₁ r₁')} {↑e r₁'} {↑e r₂'} r₁ r₂)
  ⊓-glb (⊑case₂ p₁' r₁' q₁') (⊑case₂ p₂' r₂' q₂') (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂)
    = ⊑case₂ (⊑eₛLat.⊓ₛ-greatest {x = ↑e (⊑e.trans p₁ p₁')} {↑e p₁'} {↑e p₂'} p₁ p₂)
             (⊑eₛLat.⊓ₛ-greatest {x = ↑e (⊑e.trans r₁ r₁')} {↑e r₁'} {↑e r₂'} r₁ r₂)
             (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑π₁ q₁')       (⊑π₁ q₂')       (⊑π₁ q₁)       (⊑π₁ q₂)       = ⊑π₁ (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑π₂ q₁')       (⊑π₂ q₂')       (⊑π₂ q₁)       (⊑π₂ q₂)       = ⊑π₂ (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑Λ q₁')        (⊑Λ q₂')        (⊑Λ q₁)        (⊑Λ q₂)        = ⊑Λ (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑def₁ q₁' p₁') (⊑def₁ q₂' p₂') (⊑def₁ q₁ p₁)  (⊑def₁ q₂ p₂)
    = ⊑def₁ (⊓-glb q₁' q₂' q₁ q₂)
            (⊑eₛLat.⊓ₛ-greatest {x = ↑e (⊑e.trans p₁ p₁')} {↑e p₁'} {↑e p₂'} p₁ p₂)
  ⊓-glb (⊑def₂ p₁' q₁') (⊑def₂ p₂' q₂') (⊑def₂ p₁ q₁)  (⊑def₂ p₂ q₂)
    = ⊑def₂ (⊑eₛLat.⊓ₛ-greatest {x = ↑e (⊑e.trans p₁ p₁')} {↑e p₁'} {↑e p₂'} p₁ p₂)
            (⊓-glb q₁' q₂' q₁ q₂)

  -- Join upper bounds
  ⊔-ub₁ : ∀ {C₁ C₂ C} → C₁ ⊑ C → C₂ ⊑ C → C₁ ⊑ C₁ ⊔ C₂
  ⊔-ub₁ ⊑○ ⊑○                                     = ⊑○
  ⊔-ub₁ (⊑λ p₁ q₁)       (⊑λ p₂ q₂)               = ⊑λ (⊑tₛLat.x⊑ₛx⊔ₛy (↑t p₁) (↑t p₂)) (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑λu q₁)         (⊑λu q₂)                 = ⊑λu (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑∘₁ q₁ p₁)      (⊑∘₁ q₂ p₂)              = ⊑∘₁ (⊔-ub₁ q₁ q₂) (⊑eₛLat.x⊑ₛx⊔ₛy (↑e p₁) (↑e p₂))
  ⊔-ub₁ (⊑∘₂ p₁ q₁)      (⊑∘₂ p₂ q₂)              = ⊑∘₂ (⊑eₛLat.x⊑ₛx⊔ₛy (↑e p₁) (↑e p₂)) (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑<>₁ q₁ p₁)     (⊑<>₁ q₂ p₂)             = ⊑<>₁ (⊔-ub₁ q₁ q₂) (⊑tₛLat.x⊑ₛx⊔ₛy (↑t p₁) (↑t p₂))
  ⊔-ub₁ (⊑&₁ q₁ p₁)      (⊑&₁ q₂ p₂)              = ⊑&₁ (⊔-ub₁ q₁ q₂) (⊑eₛLat.x⊑ₛx⊔ₛy (↑e p₁) (↑e p₂))
  ⊔-ub₁ (⊑&₂ p₁ q₁)      (⊑&₂ p₂ q₂)              = ⊑&₂ (⊑eₛLat.x⊑ₛx⊔ₛy (↑e p₁) (↑e p₂)) (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑ι₁ q₁)         (⊑ι₁ q₂)                 = ⊑ι₁ (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑ι₂ q₁)         (⊑ι₂ q₂)                 = ⊑ι₂ (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂)       = ⊑case₁ (⊑eₛLat.x⊑ₛx⊔ₛy (↑e p₁) (↑e p₂)) (⊔-ub₁ q₁ q₂) (⊑eₛLat.x⊑ₛx⊔ₛy (↑e r₁) (↑e r₂))
  ⊔-ub₁ (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂)       = ⊑case₂ (⊑eₛLat.x⊑ₛx⊔ₛy (↑e p₁) (↑e p₂)) (⊑eₛLat.x⊑ₛx⊔ₛy (↑e r₁) (↑e r₂)) (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑π₁ q₁)         (⊑π₁ q₂)                 = ⊑π₁ (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑π₂ q₁)         (⊑π₂ q₂)                 = ⊑π₂ (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑Λ q₁)          (⊑Λ q₂)                  = ⊑Λ (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑def₁ q₁ p₁)    (⊑def₁ q₂ p₂)            = ⊑def₁ (⊔-ub₁ q₁ q₂) (⊑eₛLat.x⊑ₛx⊔ₛy (↑e p₁) (↑e p₂))
  ⊔-ub₁ (⊑def₂ p₁ q₁)    (⊑def₂ p₂ q₂)            = ⊑def₂ (⊑eₛLat.x⊑ₛx⊔ₛy (↑e p₁) (↑e p₂)) (⊔-ub₁ q₁ q₂)

  ⊔-ub₂ : ∀ {C₁ C₂ C} → C₁ ⊑ C → C₂ ⊑ C → C₂ ⊑ C₁ ⊔ C₂
  ⊔-ub₂ ⊑○ ⊑○                                     = ⊑○
  ⊔-ub₂ (⊑λ p₁ q₁)       (⊑λ p₂ q₂)               = ⊑λ (⊑tₛLat.y⊑ₛx⊔ₛy (↑t p₁) (↑t p₂)) (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑λu q₁)         (⊑λu q₂)                 = ⊑λu (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑∘₁ q₁ p₁)      (⊑∘₁ q₂ p₂)              = ⊑∘₁ (⊔-ub₂ q₁ q₂) (⊑eₛLat.y⊑ₛx⊔ₛy (↑e p₁) (↑e p₂))
  ⊔-ub₂ (⊑∘₂ p₁ q₁)      (⊑∘₂ p₂ q₂)              = ⊑∘₂ (⊑eₛLat.y⊑ₛx⊔ₛy (↑e p₁) (↑e p₂)) (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑<>₁ q₁ p₁)     (⊑<>₁ q₂ p₂)             = ⊑<>₁ (⊔-ub₂ q₁ q₂) (⊑tₛLat.y⊑ₛx⊔ₛy (↑t p₁) (↑t p₂))
  ⊔-ub₂ (⊑&₁ q₁ p₁)      (⊑&₁ q₂ p₂)              = ⊑&₁ (⊔-ub₂ q₁ q₂) (⊑eₛLat.y⊑ₛx⊔ₛy (↑e p₁) (↑e p₂))
  ⊔-ub₂ (⊑&₂ p₁ q₁)      (⊑&₂ p₂ q₂)              = ⊑&₂ (⊑eₛLat.y⊑ₛx⊔ₛy (↑e p₁) (↑e p₂)) (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑ι₁ q₁)         (⊑ι₁ q₂)                 = ⊑ι₁ (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑ι₂ q₁)         (⊑ι₂ q₂)                 = ⊑ι₂ (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂)       = ⊑case₁ (⊑eₛLat.y⊑ₛx⊔ₛy (↑e p₁) (↑e p₂)) (⊔-ub₂ q₁ q₂) (⊑eₛLat.y⊑ₛx⊔ₛy (↑e r₁) (↑e r₂))
  ⊔-ub₂ (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂)       = ⊑case₂ (⊑eₛLat.y⊑ₛx⊔ₛy (↑e p₁) (↑e p₂)) (⊑eₛLat.y⊑ₛx⊔ₛy (↑e r₁) (↑e r₂)) (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑π₁ q₁)         (⊑π₁ q₂)                 = ⊑π₁ (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑π₂ q₁)         (⊑π₂ q₂)                 = ⊑π₂ (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑Λ q₁)          (⊑Λ q₂)                  = ⊑Λ (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑def₁ q₁ p₁)    (⊑def₁ q₂ p₂)            = ⊑def₁ (⊔-ub₂ q₁ q₂) (⊑eₛLat.y⊑ₛx⊔ₛy (↑e p₁) (↑e p₂))
  ⊔-ub₂ (⊑def₂ p₁ q₁)    (⊑def₂ p₂ q₂)            = ⊑def₂ (⊑eₛLat.y⊑ₛx⊔ₛy (↑e p₁) (↑e p₂)) (⊔-ub₂ q₁ q₂)

  ⊔-lub : ∀ {C₁ C₂ C} → C₁ ⊑ C → C₂ ⊑ C → C₁ ⊔ C₂ ⊑ C
  ⊔-lub ⊑○ ⊑○                                     = ⊑○
  ⊔-lub (⊑λ p₁ q₁)       (⊑λ p₂ q₂)               = ⊑λ (⊑tₛLat.⊔ₛ-least {x = ↑t p₁} {↑t p₂} {⊑tₛLat.⊤ₛ} p₁ p₂) (⊔-lub q₁ q₂)
  ⊔-lub (⊑λu q₁)         (⊑λu q₂)                 = ⊑λu (⊔-lub q₁ q₂)
  ⊔-lub (⊑∘₁ q₁ p₁)      (⊑∘₁ q₂ p₂)              = ⊑∘₁ (⊔-lub q₁ q₂) (⊑eₛLat.⊔ₛ-least {x = ↑e p₁} {↑e p₂} {⊑eₛLat.⊤ₛ} p₁ p₂)
  ⊔-lub (⊑∘₂ p₁ q₁)      (⊑∘₂ p₂ q₂)              = ⊑∘₂ (⊑eₛLat.⊔ₛ-least {x = ↑e p₁} {↑e p₂} {⊑eₛLat.⊤ₛ} p₁ p₂) (⊔-lub q₁ q₂)
  ⊔-lub (⊑<>₁ q₁ p₁)     (⊑<>₁ q₂ p₂)             = ⊑<>₁ (⊔-lub q₁ q₂) (⊑tₛLat.⊔ₛ-least {x = ↑t p₁} {↑t p₂} {⊑tₛLat.⊤ₛ} p₁ p₂)
  ⊔-lub (⊑&₁ q₁ p₁)      (⊑&₁ q₂ p₂)              = ⊑&₁ (⊔-lub q₁ q₂) (⊑eₛLat.⊔ₛ-least {x = ↑e p₁} {↑e p₂} {⊑eₛLat.⊤ₛ} p₁ p₂)
  ⊔-lub (⊑&₂ p₁ q₁)      (⊑&₂ p₂ q₂)              = ⊑&₂ (⊑eₛLat.⊔ₛ-least {x = ↑e p₁} {↑e p₂} {⊑eₛLat.⊤ₛ} p₁ p₂) (⊔-lub q₁ q₂)
  ⊔-lub (⊑ι₁ q₁)         (⊑ι₁ q₂)                 = ⊑ι₁ (⊔-lub q₁ q₂)
  ⊔-lub (⊑ι₂ q₁)         (⊑ι₂ q₂)                 = ⊑ι₂ (⊔-lub q₁ q₂)
  ⊔-lub (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂)       = ⊑case₁ (⊑eₛLat.⊔ₛ-least {x = ↑e p₁} {↑e p₂} {⊑eₛLat.⊤ₛ} p₁ p₂) (⊔-lub q₁ q₂) (⊑eₛLat.⊔ₛ-least {x = ↑e r₁} {↑e r₂} {⊑eₛLat.⊤ₛ} r₁ r₂)
  ⊔-lub (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂)       = ⊑case₂ (⊑eₛLat.⊔ₛ-least {x = ↑e p₁} {↑e p₂} {⊑eₛLat.⊤ₛ} p₁ p₂) (⊑eₛLat.⊔ₛ-least {x = ↑e r₁} {↑e r₂} {⊑eₛLat.⊤ₛ} r₁ r₂) (⊔-lub q₁ q₂)
  ⊔-lub (⊑π₁ q₁)         (⊑π₁ q₂)                 = ⊑π₁ (⊔-lub q₁ q₂)
  ⊔-lub (⊑π₂ q₁)         (⊑π₂ q₂)                 = ⊑π₂ (⊔-lub q₁ q₂)
  ⊔-lub (⊑Λ q₁)          (⊑Λ q₂)                  = ⊑Λ (⊔-lub q₁ q₂)
  ⊔-lub (⊑def₁ q₁ p₁)    (⊑def₁ q₂ p₂)            = ⊑def₁ (⊔-lub q₁ q₂) (⊑eₛLat.⊔ₛ-least {x = ↑e p₁} {↑e p₂} {⊑eₛLat.⊤ₛ} p₁ p₂)
  ⊔-lub (⊑def₂ p₁ q₁)    (⊑def₂ p₂ q₂)            = ⊑def₂ (⊑eₛLat.⊔ₛ-least {x = ↑e p₁} {↑e p₂} {⊑eₛLat.⊤ₛ} p₁ p₂) (⊔-lub q₁ q₂)

-- Lifting to slices (manual, not via LiftMeetSemilattice since no global bottom)
_⊓ₛ_ : ∀ {C} → ⌊ C ⌋ → ⌊ C ⌋ → ⌊ C ⌋
γ ⊓ₛ γ' = _ isSlice ⊑.trans (⊓-lb₁ (γ .proof) (γ' .proof)) (γ .proof)

infixl 6 _⊓ₛ_

_⊔ₛ_ : ∀ {C} → ⌊ C ⌋ → ⌊ C ⌋ → ⌊ C ⌋
γ ⊔ₛ γ' = γ .↓ ⊔ γ' .↓ isSlice ⊔-lub (γ .proof) (γ' .proof)

infixl 7 _⊔ₛ_

private
  ⊓ₛ-lb₁ : ∀ {C} (γ₁ γ₂ : ⌊ C ⌋) → γ₁ ⊓ₛ γ₂ ⊑ₛ γ₁
  ⊓ₛ-lb₁ γ₁ γ₂ = ⊓-lb₁ (γ₁ .proof) (γ₂ .proof)

  ⊓ₛ-lb₂ : ∀ {C} (γ₁ γ₂ : ⌊ C ⌋) → γ₁ ⊓ₛ γ₂ ⊑ₛ γ₂
  ⊓ₛ-lb₂ γ₁ γ₂ = ⊓-lb₂ (γ₁ .proof) (γ₂ .proof)

  ⊓ₛ-glb : ∀ {C} {γ : ⌊ C ⌋} (γ₁ γ₂ : ⌊ C ⌋) → γ ⊑ₛ γ₁ → γ ⊑ₛ γ₂ → γ ⊑ₛ γ₁ ⊓ₛ γ₂
  ⊓ₛ-glb γ₁ γ₂ = ⊓-glb (γ₁ .proof) (γ₂ .proof)

  ⊓ₛ-infimum : ∀ {C} → Infimum (_⊑ₛ_ {C}) _⊓ₛ_
  ⊓ₛ-infimum γ₁ γ₂ = ⊓ₛ-lb₁ γ₁ γ₂ , ⊓ₛ-lb₂ γ₁ γ₂ , λ γ → ⊓ₛ-glb {γ = γ} γ₁ γ₂

  ⊔ₛ-ub₁ : ∀ {C} (γ₁ γ₂ : ⌊ C ⌋) → γ₁ ⊑ₛ γ₁ ⊔ₛ γ₂
  ⊔ₛ-ub₁ γ₁ γ₂ = ⊔-ub₁ (γ₁ .proof) (γ₂ .proof)

  ⊔ₛ-ub₂ : ∀ {C} (γ₁ γ₂ : ⌊ C ⌋) → γ₂ ⊑ₛ γ₁ ⊔ₛ γ₂
  ⊔ₛ-ub₂ γ₁ γ₂ = ⊔-ub₂ (γ₁ .proof) (γ₂ .proof)

  ⊔ₛ-lub : ∀ {C} {γ : ⌊ C ⌋} (γ₁ γ₂ : ⌊ C ⌋) → γ₁ ⊑ₛ γ → γ₂ ⊑ₛ γ → γ₁ ⊔ₛ γ₂ ⊑ₛ γ
  ⊔ₛ-lub {γ} γ₁ γ₂ p q = ⊔-lub p q

  ⊔ₛ-supremum : ∀ {C} → Supremum (_⊑ₛ_ {C}) _⊔ₛ_
  ⊔ₛ-supremum γ₁ γ₂ = ⊔ₛ-ub₁ γ₁ γ₂ , ⊔ₛ-ub₂ γ₁ γ₂ , λ γ → ⊔ₛ-lub {γ = γ} γ₁ γ₂

  □-⊑ : ∀ C → □ C ⊑ C
  □-⊑ ○                    = ⊑○
  □-⊑ (λ: τ ⇒ C)           = ⊑λ ⊑t□ (□-⊑ C)
  □-⊑ (λ⇒ C)               = ⊑λu (□-⊑ C)
  □-⊑ (C ∘₁ e)             = ⊑∘₁ (□-⊑ C) ⊑e□
  □-⊑ (e ∘₂ C)             = ⊑∘₂ ⊑e□ (□-⊑ C)
  □-⊑ (C < τ >₁)           = ⊑<>₁ (□-⊑ C) ⊑t□
  □-⊑ (C &₁ e)             = ⊑&₁ (□-⊑ C) ⊑e□
  □-⊑ (e &₂ C)             = ⊑&₂ ⊑e□ (□-⊑ C)
  □-⊑ (ι₁ C)               = ⊑ι₁ (□-⊑ C)
  □-⊑ (ι₂ C)               = ⊑ι₂ (□-⊑ C)
  □-⊑ (case e of C ·₁ f)   = ⊑case₁ ⊑e□ (□-⊑ C) ⊑e□
  □-⊑ (case e of₂ f · C)   = ⊑case₂ ⊑e□ ⊑e□ (□-⊑ C)
  □-⊑ (π₁ C)               = ⊑π₁ (□-⊑ C)
  □-⊑ (π₂ C)               = ⊑π₂ (□-⊑ C)
  □-⊑ (Λ C)                = ⊑Λ (□-⊑ C)
  □-⊑ (def C ⊢₁ e)         = ⊑def₁ (□-⊑ C) ⊑e□
  □-⊑ (def e ⊢₂ C)         = ⊑def₂ ⊑e□ (□-⊑ C)

  ⊥ₛ' : ∀ {C} → ⌊ C ⌋
  ⊥ₛ' {C} = □ C isSlice □-⊑ C

  ⊥ₛ-min : ∀ {C} → Minimum (_⊑ₛ_ {C}) ⊥ₛ'
  ⊥ₛ-min (_ isSlice ⊑○)              = ⊑○
  ⊥ₛ-min (_ isSlice ⊑λ p q)          = ⊑λ ⊑t□ (⊥ₛ-min (_ isSlice q))
  ⊥ₛ-min (_ isSlice ⊑λu q)           = ⊑λu (⊥ₛ-min (_ isSlice q))
  ⊥ₛ-min (_ isSlice ⊑∘₁ q p)         = ⊑∘₁ (⊥ₛ-min (_ isSlice q)) ⊑e□
  ⊥ₛ-min (_ isSlice ⊑∘₂ p q)         = ⊑∘₂ ⊑e□ (⊥ₛ-min (_ isSlice q))
  ⊥ₛ-min (_ isSlice ⊑<>₁ q p)        = ⊑<>₁ (⊥ₛ-min (_ isSlice q)) ⊑t□
  ⊥ₛ-min (_ isSlice ⊑&₁ q p)         = ⊑&₁ (⊥ₛ-min (_ isSlice q)) ⊑e□
  ⊥ₛ-min (_ isSlice ⊑&₂ p q)         = ⊑&₂ ⊑e□ (⊥ₛ-min (_ isSlice q))
  ⊥ₛ-min (_ isSlice ⊑ι₁ q)           = ⊑ι₁ (⊥ₛ-min (_ isSlice q))
  ⊥ₛ-min (_ isSlice ⊑ι₂ q)           = ⊑ι₂ (⊥ₛ-min (_ isSlice q))
  ⊥ₛ-min (_ isSlice ⊑case₁ p q r)    = ⊑case₁ ⊑e□ (⊥ₛ-min (_ isSlice q)) ⊑e□
  ⊥ₛ-min (_ isSlice ⊑case₂ p r q)    = ⊑case₂ ⊑e□ ⊑e□ (⊥ₛ-min (_ isSlice q))
  ⊥ₛ-min (_ isSlice ⊑π₁ q)           = ⊑π₁ (⊥ₛ-min (_ isSlice q))
  ⊥ₛ-min (_ isSlice ⊑π₂ q)           = ⊑π₂ (⊥ₛ-min (_ isSlice q))
  ⊥ₛ-min (_ isSlice ⊑Λ q)            = ⊑Λ (⊥ₛ-min (_ isSlice q))
  ⊥ₛ-min (_ isSlice ⊑def₁ q p)       = ⊑def₁ (⊥ₛ-min (_ isSlice q)) ⊑e□
  ⊥ₛ-min (_ isSlice ⊑def₂ p q)       = ⊑def₂ ⊑e□ (⊥ₛ-min (_ isSlice q))

  ⊤ₛ-maximum : ∀ {C} → Maximum (_⊑ₛ_ {C}) ⊤ₛ'
  ⊤ₛ-maximum γ = γ .proof

  ⊑ₛ-isMeetSemilattice : ∀ {C} → IsMeetSemilattice (_≡_ on ↓) (_⊑ₛ_ {C}) _⊓ₛ_
  ⊑ₛ-isMeetSemilattice = record
                         { isPartialOrder = ⊑ₛ.isPartialOrder
                         ; infimum        = ⊓ₛ-infimum
                         }

  ⊑ₛ-isJoinSemilattice : ∀ {C} → IsJoinSemilattice (_≡_ on ↓) (_⊑ₛ_ {C}) _⊔ₛ_
  ⊑ₛ-isJoinSemilattice = record
                         { isPartialOrder = ⊑ₛ.isPartialOrder
                         ; supremum       = ⊔ₛ-supremum
                         }

  ⊑ₛ-isLattice : ∀ {C} → IsLattice (_≡_ on ↓) (_⊑ₛ_ {C}) _⊔ₛ_ _⊓ₛ_
  ⊑ₛ-isLattice = record
                 { isPartialOrder = ⊑ₛ.isPartialOrder
                 ; supremum       = ⊔ₛ-supremum
                 ; infimum        = ⊓ₛ-infimum
                 }

  ⊑ₛ-isBoundedLattice : ∀ {C} → IsBoundedLattice (_≡_ on ↓) (_⊑ₛ_ {C}) _⊔ₛ_ _⊓ₛ_ ⊤ₛ' ⊥ₛ'
  ⊑ₛ-isBoundedLattice = record
                        { isLattice = ⊑ₛ-isLattice
                        ; maximum   = ⊤ₛ-maximum
                        ; minimum   = ⊥ₛ-min
                        }

  -- Distributivity
  dist : ∀ {C C₁ C₂ C₃} → C₁ ⊑ C → C₂ ⊑ C → C₃ ⊑ C
       → C₁ ⊓ (C₂ ⊔ C₃) ≡ (C₁ ⊓ C₂) ⊔ (C₁ ⊓ C₃)
  dist ⊑○ ⊑○ ⊑○ = refl
  dist (⊑λ p₁ q₁) (⊑λ p₂ q₂) (⊑λ p₃ q₃)
    = cong₂ λ:_⇒_ (⊑tₛLat.⊓ₛ-distribˡ-⊔ₛ (↑t p₁) (↑t p₂) (↑t p₃)) (dist q₁ q₂ q₃)
  dist (⊑λu q₁) (⊑λu q₂) (⊑λu q₃)
    = cong λ⇒_ (dist q₁ q₂ q₃)
  dist (⊑∘₁ q₁ p₁) (⊑∘₁ q₂ p₂) (⊑∘₁ q₃ p₃)
    = cong₂ _∘₁_ (dist q₁ q₂ q₃) (⊑eₛLat.⊓ₛ-distribˡ-⊔ₛ (↑e p₁) (↑e p₂) (↑e p₃))
  dist (⊑∘₂ p₁ q₁) (⊑∘₂ p₂ q₂) (⊑∘₂ p₃ q₃)
    = cong₂ _∘₂_ (⊑eₛLat.⊓ₛ-distribˡ-⊔ₛ (↑e p₁) (↑e p₂) (↑e p₃)) (dist q₁ q₂ q₃)
  dist (⊑<>₁ q₁ p₁) (⊑<>₁ q₂ p₂) (⊑<>₁ q₃ p₃)
    = cong₂ _<_>₁ (dist q₁ q₂ q₃) (⊑tₛLat.⊓ₛ-distribˡ-⊔ₛ (↑t p₁) (↑t p₂) (↑t p₃))
  dist (⊑&₁ q₁ p₁) (⊑&₁ q₂ p₂) (⊑&₁ q₃ p₃)
    = cong₂ _&₁_ (dist q₁ q₂ q₃) (⊑eₛLat.⊓ₛ-distribˡ-⊔ₛ (↑e p₁) (↑e p₂) (↑e p₃))
  dist (⊑&₂ p₁ q₁) (⊑&₂ p₂ q₂) (⊑&₂ p₃ q₃)
    = cong₂ _&₂_ (⊑eₛLat.⊓ₛ-distribˡ-⊔ₛ (↑e p₁) (↑e p₂) (↑e p₃)) (dist q₁ q₂ q₃)
  dist (⊑ι₁ q₁) (⊑ι₁ q₂) (⊑ι₁ q₃)
    = cong ι₁ (dist q₁ q₂ q₃)
  dist (⊑ι₂ q₁) (⊑ι₂ q₂) (⊑ι₂ q₃)
    = cong ι₂ (dist q₁ q₂ q₃)
  dist (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂) (⊑case₁ p₃ q₃ r₃)
    = case₁-cong (⊑eₛLat.⊓ₛ-distribˡ-⊔ₛ (↑e p₁) (↑e p₂) (↑e p₃))
                 (dist q₁ q₂ q₃)
                 (⊑eₛLat.⊓ₛ-distribˡ-⊔ₛ (↑e r₁) (↑e r₂) (↑e r₃))
    where
    case₁-cong : ∀ {a a' : Exp} {b b' : Ctx} {c c' : Exp}
               → a ≡ a' → b ≡ b' → c ≡ c'
               → case a of b ·₁ c ≡ case a' of b' ·₁ c'
    case₁-cong refl refl refl = refl
  dist (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂) (⊑case₂ p₃ r₃ q₃)
    = case₂-cong (⊑eₛLat.⊓ₛ-distribˡ-⊔ₛ (↑e p₁) (↑e p₂) (↑e p₃))
                 (⊑eₛLat.⊓ₛ-distribˡ-⊔ₛ (↑e r₁) (↑e r₂) (↑e r₃))
                 (dist q₁ q₂ q₃)
    where
    case₂-cong : ∀ {a a' : Exp} {b b' : Exp} {c c' : Ctx}
               → a ≡ a' → b ≡ b' → c ≡ c'
               → case a of₂ b · c ≡ case a' of₂ b' · c'
    case₂-cong refl refl refl = refl
  dist (⊑π₁ q₁) (⊑π₁ q₂) (⊑π₁ q₃)
    = cong π₁ (dist q₁ q₂ q₃)
  dist (⊑π₂ q₁) (⊑π₂ q₂) (⊑π₂ q₃)
    = cong π₂ (dist q₁ q₂ q₃)
  dist (⊑Λ q₁) (⊑Λ q₂) (⊑Λ q₃)
    = cong Λ (dist q₁ q₂ q₃)
  dist (⊑def₁ q₁ p₁) (⊑def₁ q₂ p₂) (⊑def₁ q₃ p₃)
    = cong₂ def_⊢₁_ (dist q₁ q₂ q₃) (⊑eₛLat.⊓ₛ-distribˡ-⊔ₛ (↑e p₁) (↑e p₂) (↑e p₃))
  dist (⊑def₂ p₁ q₁) (⊑def₂ p₂ q₂) (⊑def₂ p₃ q₃)
    = cong₂ def_⊢₂_ (⊑eₛLat.⊓ₛ-distribˡ-⊔ₛ (↑e p₁) (↑e p₂) (↑e p₃)) (dist q₁ q₂ q₃)

  ⊓ₛ-distribˡ-⊔ₛ : ∀ {C} (γ₁ γ₂ γ₃ : ⌊ C ⌋) → (γ₁ ⊓ₛ (γ₂ ⊔ₛ γ₃)) ≈ₛ ((γ₁ ⊓ₛ γ₂) ⊔ₛ (γ₁ ⊓ₛ γ₃))
  ⊓ₛ-distribˡ-⊔ₛ γ₁ γ₂ γ₃ = dist (γ₁ .proof) (γ₂ .proof) (γ₃ .proof)

  ⊑ₛ-isDistributiveLattice : ∀ {C} → IsDistributiveLattice (_≡_ on ↓) (_⊑ₛ_ {C}) _⊔ₛ_ _⊓ₛ_
  ⊑ₛ-isDistributiveLattice = record
                             { isLattice    = ⊑ₛ-isLattice
                             ; ∧-distribˡ-∨ = ⊓ₛ-distribˡ-⊔ₛ
                             }

module ⊑ₛLat {C} where
  open IsBoundedLattice (⊑ₛ-isBoundedLattice {C}) public
    using (infimum; supremum; maximum; minimum;
           isBoundedJoinSemilattice; isBoundedMeetSemilattice; isJoinSemilattice; isMeetSemilattice; isLattice)
    renaming (x∧y≤x to x⊓ₛy⊑ₛx; x∧y≤y to x⊓ₛy⊑ₛy; x≤x∨y to x⊑ₛx⊔ₛy; y≤x∨y to y⊑ₛx⊔ₛy;
              ∧-greatest to ⊓ₛ-greatest; ∨-least to ⊔ₛ-least)

  ⊤ₛ = ⊤ₛ'
  ⊥ₛ = ⊥ₛ'

  isBoundedLattice = ⊑ₛ-isBoundedLattice

  open IsDistributiveLattice (⊑ₛ-isDistributiveLattice {C}) public
    using () renaming (∧-distribˡ-∨ to ⊓ₛ-distribˡ-⊔ₛ)

  isDistributiveLattice = ⊑ₛ-isDistributiveLattice

import Core.Instances as I
instance
  ctx-meet : I.HasMeet Ctx
  ctx-meet = record { _⊓_ = _⊓_ }
  ctx-join : I.HasJoin Ctx
  ctx-join = record { _⊔_ = _⊔_ }
  ctx-sliceLattice : I.SliceLattice SliceOf ↓
  ctx-sliceLattice = record
    { _⊑ₛ_ = _⊑ₛ_ ; _⊓ₛ_ = _⊓ₛ_ ; _⊔ₛ_ = _⊔ₛ_
    ; ⊤ₛ = ⊤ₛ' ; ⊥ₛ = ⊥ₛ'
    ; isBoundedLattice = ⊑ₛ-isBoundedLattice
    ; isDistributiveLattice = ⊑ₛ-isDistributiveLattice
    }
