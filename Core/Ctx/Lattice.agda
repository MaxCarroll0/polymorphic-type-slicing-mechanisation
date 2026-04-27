module Core.Ctx.Lattice where

open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary using (IsPartialOrder)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Maximum; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Relation.Binary.Lattice.Structures using (IsMeetSemilattice; IsJoinSemilattice; IsLattice; IsBoundedLattice; IsDistributiveLattice)
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum)
open import Function using (_on_)

open import Core.Instances
open import Core.Typ hiding (□)
open import Core.Exp hiding (□)
open import Core.Ctx.Base
open import Core.Ctx.Equality
open import Core.Ctx.Precision

-- Meet operator
-- TODO: consider returning Maybe Ctx to distinguish meet failure from ○
private
  _⊓c_ : Ctx → Ctx → Ctx
  C ⊓c C' with diag C C'
  ...       | diff                                   = ○
  ...       | kind○                                  = ○
  ...       | kindλ  {τ} {τ'} {C₁} {C₁'}             = λ: (τ ⊓ τ') ⇒ (C₁ ⊓c C₁')
  ...       | kindλu {C₁} {C₁'}                      = λ⇒ (C₁ ⊓c C₁')
  ...       | kind∘₁ {C₁} {C₁'} {e} {e'}             = (C₁ ⊓c C₁') ∘₁ (e ⊓ e')
  ...       | kind∘₂ {e} {e'} {C₁} {C₁'}             = (e ⊓ e') ∘₂ (C₁ ⊓c C₁')
  ...       | kind<>₁ {C₁} {C₁'} {τ} {τ'}            = (C₁ ⊓c C₁') < (τ ⊓ τ') >₁
  ...       | kind&₁ {C₁} {C₁'} {e} {e'}             = (C₁ ⊓c C₁') &₁ (e ⊓ e')
  ...       | kind&₂ {e} {e'} {C₁} {C₁'}             = (e ⊓ e') &₂ (C₁ ⊓c C₁')
  ...       | kindι₁ {C₁} {C₁'}                      = ι₁ (C₁ ⊓c C₁')
  ...       | kindι₂ {C₁} {C₁'}                      = ι₂ (C₁ ⊓c C₁')
  ...       | kindcase₁ {e} {e'} {C₁} {C₁'} {f} {f'} = case (e ⊓ e') of (C₁ ⊓c C₁') ·₁ (f ⊓ f')
  ...       | kindcase₂ {e} {e'} {f} {f'} {C₁} {C₁'} = case (e ⊓ e') of₂ (f ⊓ f') · (C₁ ⊓c C₁')
  ...       | kindπ₁ {C₁} {C₁'}                      = π₁ (C₁ ⊓c C₁')
  ...       | kindπ₂ {C₁} {C₁'}                      = π₂ (C₁ ⊓c C₁')
  ...       | kindΛ  {C₁} {C₁'}                      = Λ (C₁ ⊓c C₁')
  ...       | kinddef₁ {C₁} {C₁'} {e} {e'}           = def (C₁ ⊓c C₁') ⊢₁ (e ⊓ e')
  ...       | kinddef₂ {e} {e'} {C₁} {C₁'}           = def (e ⊓ e') ⊢₂ (C₁ ⊓c C₁')

  infixl 6 _⊓c_

  -- Join operator
  _⊔c_ : Ctx → Ctx → Ctx
  C ⊔c C' with diag C C'
  ...       | kind○                                  = ○
  ...       | kindλ  {τ} {τ'} {C₁} {C₁'}             = λ: (τ ⊔ τ') ⇒ (C₁ ⊔c C₁')
  ...       | kindλu {C₁} {C₁'}                      = λ⇒ (C₁ ⊔c C₁')
  ...       | kind∘₁ {C₁} {C₁'} {e} {e'}             = (C₁ ⊔c C₁') ∘₁ (e ⊔ e')
  ...       | kind∘₂ {e} {e'} {C₁} {C₁'}             = (e ⊔ e') ∘₂ (C₁ ⊔c C₁')
  ...       | kind<>₁ {C₁} {C₁'} {τ} {τ'}            = (C₁ ⊔c C₁') < (τ ⊔ τ') >₁
  ...       | kind&₁ {C₁} {C₁'} {e} {e'}             = (C₁ ⊔c C₁') &₁ (e ⊔ e')
  ...       | kind&₂ {e} {e'} {C₁} {C₁'}             = (e ⊔ e') &₂ (C₁ ⊔c C₁')
  ...       | kindι₁ {C₁} {C₁'}                      = ι₁ (C₁ ⊔c C₁')
  ...       | kindι₂ {C₁} {C₁'}                      = ι₂ (C₁ ⊔c C₁')
  ...       | kindcase₁ {e} {e'} {C₁} {C₁'} {f} {f'} = case (e ⊔ e') of (C₁ ⊔c C₁') ·₁ (f ⊔ f')
  ...       | kindcase₂ {e} {e'} {f} {f'} {C₁} {C₁'} = case (e ⊔ e') of₂ (f ⊔ f') · (C₁ ⊔c C₁')
  ...       | kindπ₁ {C₁} {C₁'}                      = π₁ (C₁ ⊔c C₁')
  ...       | kindπ₂ {C₁} {C₁'}                      = π₂ (C₁ ⊔c C₁')
  ...       | kindΛ  {C₁} {C₁'}                      = Λ (C₁ ⊔c C₁')
  ...       | kinddef₁ {C₁} {C₁'} {e} {e'}           = def (C₁ ⊔c C₁') ⊢₁ (e ⊔ e')
  ...       | kinddef₂ {e} {e'} {C₁} {C₁'}           = def (e ⊔ e') ⊢₂ (C₁ ⊔c C₁')
  ...       | diff                                   = ○

  infixl 6 _⊔c_

  -- Meet lower bounds (bounded hypotheses since no global bottom)
  ⊓-lb₁ : ∀ {C₁ C₂ C} → C₁ ⊑ C → C₂ ⊑ C → C₁ ⊓c C₂ ⊑ C₁
  ⊓-lb₁ ⊑○ ⊑○                                     = ⊑○
  ⊓-lb₁ (⊑λ p₁ q₁)       (⊑λ p₂ q₂)               = ⊑λ (⊑ₛLat.x⊓ₛy⊑ₛx (↑ p₁) (↑ p₂)) (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑λu q₁)         (⊑λu q₂)                 = ⊑λu (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑∘₁ q₁ p₁)      (⊑∘₁ q₂ p₂)              = ⊑∘₁ (⊓-lb₁ q₁ q₂) (⊑ₛLat.x⊓ₛy⊑ₛx (↑ p₁) (↑ p₂))
  ⊓-lb₁ (⊑∘₂ p₁ q₁)      (⊑∘₂ p₂ q₂)              = ⊑∘₂ (⊑ₛLat.x⊓ₛy⊑ₛx (↑ p₁) (↑ p₂)) (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑<>₁ q₁ p₁)     (⊑<>₁ q₂ p₂)             = ⊑<>₁ (⊓-lb₁ q₁ q₂) (⊑ₛLat.x⊓ₛy⊑ₛx (↑ p₁) (↑ p₂))
  ⊓-lb₁ (⊑&₁ q₁ p₁)      (⊑&₁ q₂ p₂)              = ⊑&₁ (⊓-lb₁ q₁ q₂) (⊑ₛLat.x⊓ₛy⊑ₛx (↑ p₁) (↑ p₂))
  ⊓-lb₁ (⊑&₂ p₁ q₁)      (⊑&₂ p₂ q₂)              = ⊑&₂ (⊑ₛLat.x⊓ₛy⊑ₛx (↑ p₁) (↑ p₂)) (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑ι₁ q₁)         (⊑ι₁ q₂)                 = ⊑ι₁ (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑ι₂ q₁)         (⊑ι₂ q₂)                 = ⊑ι₂ (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂)       = ⊑case₁ (⊑ₛLat.x⊓ₛy⊑ₛx (↑ p₁) (↑ p₂)) (⊓-lb₁ q₁ q₂) (⊑ₛLat.x⊓ₛy⊑ₛx (↑ r₁) (↑ r₂))
  ⊓-lb₁ (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂)       = ⊑case₂ (⊑ₛLat.x⊓ₛy⊑ₛx (↑ p₁) (↑ p₂)) (⊑ₛLat.x⊓ₛy⊑ₛx (↑ r₁) (↑ r₂)) (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑π₁ q₁)         (⊑π₁ q₂)                 = ⊑π₁ (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑π₂ q₁)         (⊑π₂ q₂)                 = ⊑π₂ (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑Λ q₁)          (⊑Λ q₂)                  = ⊑Λ (⊓-lb₁ q₁ q₂)
  ⊓-lb₁ (⊑def₁ q₁ p₁)    (⊑def₁ q₂ p₂)            = ⊑def₁ (⊓-lb₁ q₁ q₂) (⊑ₛLat.x⊓ₛy⊑ₛx (↑ p₁) (↑ p₂))
  ⊓-lb₁ (⊑def₂ p₁ q₁)    (⊑def₂ p₂ q₂)            = ⊑def₂ (⊑ₛLat.x⊓ₛy⊑ₛx (↑ p₁) (↑ p₂)) (⊓-lb₁ q₁ q₂)

  ⊓-lb₂ : ∀ {C₁ C₂ C} → C₁ ⊑ C → C₂ ⊑ C → C₁ ⊓c C₂ ⊑ C₂
  ⊓-lb₂ ⊑○ ⊑○                                     = ⊑○
  ⊓-lb₂ (⊑λ p₁ q₁)       (⊑λ p₂ q₂)               = ⊑λ (⊑ₛLat.x⊓ₛy⊑ₛy (↑ p₁) (↑ p₂)) (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑λu q₁)         (⊑λu q₂)                 = ⊑λu (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑∘₁ q₁ p₁)      (⊑∘₁ q₂ p₂)              = ⊑∘₁ (⊓-lb₂ q₁ q₂) (⊑ₛLat.x⊓ₛy⊑ₛy (↑ p₁) (↑ p₂))
  ⊓-lb₂ (⊑∘₂ p₁ q₁)      (⊑∘₂ p₂ q₂)              = ⊑∘₂ (⊑ₛLat.x⊓ₛy⊑ₛy (↑ p₁) (↑ p₂)) (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑<>₁ q₁ p₁)     (⊑<>₁ q₂ p₂)             = ⊑<>₁ (⊓-lb₂ q₁ q₂) (⊑ₛLat.x⊓ₛy⊑ₛy (↑ p₁) (↑ p₂))
  ⊓-lb₂ (⊑&₁ q₁ p₁)      (⊑&₁ q₂ p₂)              = ⊑&₁ (⊓-lb₂ q₁ q₂) (⊑ₛLat.x⊓ₛy⊑ₛy (↑ p₁) (↑ p₂))
  ⊓-lb₂ (⊑&₂ p₁ q₁)      (⊑&₂ p₂ q₂)              = ⊑&₂ (⊑ₛLat.x⊓ₛy⊑ₛy (↑ p₁) (↑ p₂)) (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑ι₁ q₁)         (⊑ι₁ q₂)                 = ⊑ι₁ (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑ι₂ q₁)         (⊑ι₂ q₂)                 = ⊑ι₂ (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂)       = ⊑case₁ (⊑ₛLat.x⊓ₛy⊑ₛy (↑ p₁) (↑ p₂)) (⊓-lb₂ q₁ q₂) (⊑ₛLat.x⊓ₛy⊑ₛy (↑ r₁) (↑ r₂))
  ⊓-lb₂ (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂)       = ⊑case₂ (⊑ₛLat.x⊓ₛy⊑ₛy (↑ p₁) (↑ p₂)) (⊑ₛLat.x⊓ₛy⊑ₛy (↑ r₁) (↑ r₂)) (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑π₁ q₁)         (⊑π₁ q₂)                 = ⊑π₁ (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑π₂ q₁)         (⊑π₂ q₂)                 = ⊑π₂ (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑Λ q₁)          (⊑Λ q₂)                  = ⊑Λ (⊓-lb₂ q₁ q₂)
  ⊓-lb₂ (⊑def₁ q₁ p₁)    (⊑def₁ q₂ p₂)            = ⊑def₁ (⊓-lb₂ q₁ q₂) (⊑ₛLat.x⊓ₛy⊑ₛy (↑ p₁) (↑ p₂))
  ⊓-lb₂ (⊑def₂ p₁ q₁)    (⊑def₂ p₂ q₂)            = ⊑def₂ (⊑ₛLat.x⊓ₛy⊑ₛy (↑ p₁) (↑ p₂)) (⊓-lb₂ q₁ q₂)

  -- Meet is greatest lower bound
  ⊓-glb : ∀ {C C₁ C₂ C'} → C₁ ⊑ C' → C₂ ⊑ C' → C ⊑ C₁ → C ⊑ C₂ → C ⊑ C₁ ⊓c C₂
  ⊓-glb ⊑○               ⊑○               ⊑○              ⊑○              = ⊑○
  ⊓-glb (⊑λ p₁' q₁')    (⊑λ p₂' q₂')    (⊑λ p₁ q₁)     (⊑λ p₂ q₂)
    = ⊑λ (⊑ₛLat.⊓ₛ-greatest {x = ↑(⊑.trans {A = Typ} p₁ p₁')} {↑ p₁'} {↑ p₂'} p₁ p₂)
         (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑λu q₁')       (⊑λu q₂')       (⊑λu q₁)       (⊑λu q₂)       = ⊑λu (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑∘₁ q₁' p₁')   (⊑∘₁ q₂' p₂')   (⊑∘₁ q₁ p₁)    (⊑∘₁ q₂ p₂)
    = ⊑∘₁ (⊓-glb q₁' q₂' q₁ q₂)
          (⊑ₛLat.⊓ₛ-greatest {x = ↑(⊑.trans {A = Exp} p₁ p₁')} {↑ p₁'} {↑ p₂'} p₁ p₂)
  ⊓-glb (⊑∘₂ p₁' q₁')   (⊑∘₂ p₂' q₂')   (⊑∘₂ p₁ q₁)    (⊑∘₂ p₂ q₂)
    = ⊑∘₂ (⊑ₛLat.⊓ₛ-greatest {x = ↑(⊑.trans {A = Exp} p₁ p₁')} {↑ p₁'} {↑ p₂'} p₁ p₂)
          (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑<>₁ q₁' p₁')  (⊑<>₁ q₂' p₂')  (⊑<>₁ q₁ p₁)   (⊑<>₁ q₂ p₂)
    = ⊑<>₁ (⊓-glb q₁' q₂' q₁ q₂)
           (⊑ₛLat.⊓ₛ-greatest {x = ↑(⊑.trans {A = Typ} p₁ p₁')} {↑ p₁'} {↑ p₂'} p₁ p₂)
  ⊓-glb (⊑&₁ q₁' p₁')   (⊑&₁ q₂' p₂')   (⊑&₁ q₁ p₁)    (⊑&₁ q₂ p₂)
    = ⊑&₁ (⊓-glb q₁' q₂' q₁ q₂)
          (⊑ₛLat.⊓ₛ-greatest {x = ↑(⊑.trans {A = Exp} p₁ p₁')} {↑ p₁'} {↑ p₂'} p₁ p₂)
  ⊓-glb (⊑&₂ p₁' q₁')   (⊑&₂ p₂' q₂')   (⊑&₂ p₁ q₁)    (⊑&₂ p₂ q₂)
    = ⊑&₂ (⊑ₛLat.⊓ₛ-greatest {x = ↑(⊑.trans {A = Exp} p₁ p₁')} {↑ p₁'} {↑ p₂'} p₁ p₂)
          (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑ι₁ q₁')       (⊑ι₁ q₂')       (⊑ι₁ q₁)       (⊑ι₁ q₂)       = ⊑ι₁ (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑ι₂ q₁')       (⊑ι₂ q₂')       (⊑ι₂ q₁)       (⊑ι₂ q₂)       = ⊑ι₂ (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑case₁ p₁' q₁' r₁') (⊑case₁ p₂' q₂' r₂') (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂)
    = ⊑case₁ (⊑ₛLat.⊓ₛ-greatest {x = ↑(⊑.trans {A = Exp} p₁ p₁')} {↑ p₁'} {↑ p₂'} p₁ p₂)
             (⊓-glb q₁' q₂' q₁ q₂)
             (⊑ₛLat.⊓ₛ-greatest {x = ↑(⊑.trans {A = Exp} r₁ r₁')} {↑ r₁'} {↑ r₂'} r₁ r₂)
  ⊓-glb (⊑case₂ p₁' r₁' q₁') (⊑case₂ p₂' r₂' q₂') (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂)
    = ⊑case₂ (⊑ₛLat.⊓ₛ-greatest {x = ↑(⊑.trans {A = Exp} p₁ p₁')} {↑ p₁'} {↑ p₂'} p₁ p₂)
             (⊑ₛLat.⊓ₛ-greatest {x = ↑(⊑.trans {A = Exp} r₁ r₁')} {↑ r₁'} {↑ r₂'} r₁ r₂)
             (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑π₁ q₁')       (⊑π₁ q₂')       (⊑π₁ q₁)       (⊑π₁ q₂)       = ⊑π₁ (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑π₂ q₁')       (⊑π₂ q₂')       (⊑π₂ q₁)       (⊑π₂ q₂)       = ⊑π₂ (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑Λ q₁')        (⊑Λ q₂')        (⊑Λ q₁)        (⊑Λ q₂)        = ⊑Λ (⊓-glb q₁' q₂' q₁ q₂)
  ⊓-glb (⊑def₁ q₁' p₁') (⊑def₁ q₂' p₂') (⊑def₁ q₁ p₁)  (⊑def₁ q₂ p₂)
    = ⊑def₁ (⊓-glb q₁' q₂' q₁ q₂)
            (⊑ₛLat.⊓ₛ-greatest {x = ↑(⊑.trans {A = Exp} p₁ p₁')} {↑ p₁'} {↑ p₂'} p₁ p₂)
  ⊓-glb (⊑def₂ p₁' q₁') (⊑def₂ p₂' q₂') (⊑def₂ p₁ q₁)  (⊑def₂ p₂ q₂)
    = ⊑def₂ (⊑ₛLat.⊓ₛ-greatest {x = ↑(⊑.trans {A = Exp} p₁ p₁')} {↑ p₁'} {↑ p₂'} p₁ p₂)
            (⊓-glb q₁' q₂' q₁ q₂)

  -- Join upper bounds
  ⊔-ub₁ : ∀ {C₁ C₂ C} → C₁ ⊑ C → C₂ ⊑ C → C₁ ⊑ C₁ ⊔c C₂
  ⊔-ub₁ ⊑○ ⊑○                                     = ⊑○
  ⊔-ub₁ (⊑λ p₁ q₁)       (⊑λ p₂ q₂)               = ⊑λ (⊑ₛLat.x⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑λu q₁)         (⊑λu q₂)                 = ⊑λu (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑∘₁ q₁ p₁)      (⊑∘₁ q₂ p₂)              = ⊑∘₁ (⊔-ub₁ q₁ q₂) (⊑ₛLat.x⊑ₛx⊔ₛy (↑ p₁) (↑ p₂))
  ⊔-ub₁ (⊑∘₂ p₁ q₁)      (⊑∘₂ p₂ q₂)              = ⊑∘₂ (⊑ₛLat.x⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑<>₁ q₁ p₁)     (⊑<>₁ q₂ p₂)             = ⊑<>₁ (⊔-ub₁ q₁ q₂) (⊑ₛLat.x⊑ₛx⊔ₛy (↑ p₁) (↑ p₂))
  ⊔-ub₁ (⊑&₁ q₁ p₁)      (⊑&₁ q₂ p₂)              = ⊑&₁ (⊔-ub₁ q₁ q₂) (⊑ₛLat.x⊑ₛx⊔ₛy (↑ p₁) (↑ p₂))
  ⊔-ub₁ (⊑&₂ p₁ q₁)      (⊑&₂ p₂ q₂)              = ⊑&₂ (⊑ₛLat.x⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑ι₁ q₁)         (⊑ι₁ q₂)                 = ⊑ι₁ (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑ι₂ q₁)         (⊑ι₂ q₂)                 = ⊑ι₂ (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂)       = ⊑case₁ (⊑ₛLat.x⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊔-ub₁ q₁ q₂) (⊑ₛLat.x⊑ₛx⊔ₛy (↑ r₁) (↑ r₂))
  ⊔-ub₁ (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂)       = ⊑case₂ (⊑ₛLat.x⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊑ₛLat.x⊑ₛx⊔ₛy (↑ r₁) (↑ r₂)) (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑π₁ q₁)         (⊑π₁ q₂)                 = ⊑π₁ (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑π₂ q₁)         (⊑π₂ q₂)                 = ⊑π₂ (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑Λ q₁)          (⊑Λ q₂)                  = ⊑Λ (⊔-ub₁ q₁ q₂)
  ⊔-ub₁ (⊑def₁ q₁ p₁)    (⊑def₁ q₂ p₂)            = ⊑def₁ (⊔-ub₁ q₁ q₂) (⊑ₛLat.x⊑ₛx⊔ₛy (↑ p₁) (↑ p₂))
  ⊔-ub₁ (⊑def₂ p₁ q₁)    (⊑def₂ p₂ q₂)            = ⊑def₂ (⊑ₛLat.x⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊔-ub₁ q₁ q₂)

  ⊔-ub₂ : ∀ {C₁ C₂ C} → C₁ ⊑ C → C₂ ⊑ C → C₂ ⊑ C₁ ⊔c C₂
  ⊔-ub₂ ⊑○ ⊑○                                     = ⊑○
  ⊔-ub₂ (⊑λ p₁ q₁)       (⊑λ p₂ q₂)               = ⊑λ (⊑ₛLat.y⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑λu q₁)         (⊑λu q₂)                 = ⊑λu (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑∘₁ q₁ p₁)      (⊑∘₁ q₂ p₂)              = ⊑∘₁ (⊔-ub₂ q₁ q₂) (⊑ₛLat.y⊑ₛx⊔ₛy (↑ p₁) (↑ p₂))
  ⊔-ub₂ (⊑∘₂ p₁ q₁)      (⊑∘₂ p₂ q₂)              = ⊑∘₂ (⊑ₛLat.y⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑<>₁ q₁ p₁)     (⊑<>₁ q₂ p₂)             = ⊑<>₁ (⊔-ub₂ q₁ q₂) (⊑ₛLat.y⊑ₛx⊔ₛy (↑ p₁) (↑ p₂))
  ⊔-ub₂ (⊑&₁ q₁ p₁)      (⊑&₁ q₂ p₂)              = ⊑&₁ (⊔-ub₂ q₁ q₂) (⊑ₛLat.y⊑ₛx⊔ₛy (↑ p₁) (↑ p₂))
  ⊔-ub₂ (⊑&₂ p₁ q₁)      (⊑&₂ p₂ q₂)              = ⊑&₂ (⊑ₛLat.y⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑ι₁ q₁)         (⊑ι₁ q₂)                 = ⊑ι₁ (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑ι₂ q₁)         (⊑ι₂ q₂)                 = ⊑ι₂ (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂)       = ⊑case₁ (⊑ₛLat.y⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊔-ub₂ q₁ q₂) (⊑ₛLat.y⊑ₛx⊔ₛy (↑ r₁) (↑ r₂))
  ⊔-ub₂ (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂)       = ⊑case₂ (⊑ₛLat.y⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊑ₛLat.y⊑ₛx⊔ₛy (↑ r₁) (↑ r₂)) (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑π₁ q₁)         (⊑π₁ q₂)                 = ⊑π₁ (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑π₂ q₁)         (⊑π₂ q₂)                 = ⊑π₂ (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑Λ q₁)          (⊑Λ q₂)                  = ⊑Λ (⊔-ub₂ q₁ q₂)
  ⊔-ub₂ (⊑def₁ q₁ p₁)    (⊑def₁ q₂ p₂)            = ⊑def₁ (⊔-ub₂ q₁ q₂) (⊑ₛLat.y⊑ₛx⊔ₛy (↑ p₁) (↑ p₂))
  ⊔-ub₂ (⊑def₂ p₁ q₁)    (⊑def₂ p₂ q₂)            = ⊑def₂ (⊑ₛLat.y⊑ₛx⊔ₛy (↑ p₁) (↑ p₂)) (⊔-ub₂ q₁ q₂)

  ⊔-lub : ∀ {C₁ C₂ C} → C₁ ⊑ C → C₂ ⊑ C → C₁ ⊔c C₂ ⊑ C
  ⊔-lub ⊑○ ⊑○                                     = ⊑○
  ⊔-lub (⊑λ p₁ q₁)       (⊑λ p₂ q₂)               = ⊑λ (⊑ₛLat.⊔ₛ-least {x = ↑ p₁} {↑ p₂} {⊤ₛ} p₁ p₂) (⊔-lub q₁ q₂)
  ⊔-lub (⊑λu q₁)         (⊑λu q₂)                 = ⊑λu (⊔-lub q₁ q₂)
  ⊔-lub (⊑∘₁ q₁ p₁)      (⊑∘₁ q₂ p₂)              = ⊑∘₁ (⊔-lub q₁ q₂) (⊑ₛLat.⊔ₛ-least {x = ↑ p₁} {↑ p₂} {⊤ₛ} p₁ p₂)
  ⊔-lub (⊑∘₂ p₁ q₁)      (⊑∘₂ p₂ q₂)              = ⊑∘₂ (⊑ₛLat.⊔ₛ-least {x = ↑ p₁} {↑ p₂} {⊤ₛ} p₁ p₂) (⊔-lub q₁ q₂)
  ⊔-lub (⊑<>₁ q₁ p₁)     (⊑<>₁ q₂ p₂)             = ⊑<>₁ (⊔-lub q₁ q₂) (⊑ₛLat.⊔ₛ-least {x = ↑ p₁} {↑ p₂} {⊤ₛ} p₁ p₂)
  ⊔-lub (⊑&₁ q₁ p₁)      (⊑&₁ q₂ p₂)              = ⊑&₁ (⊔-lub q₁ q₂) (⊑ₛLat.⊔ₛ-least {x = ↑ p₁} {↑ p₂} {⊤ₛ} p₁ p₂)
  ⊔-lub (⊑&₂ p₁ q₁)      (⊑&₂ p₂ q₂)              = ⊑&₂ (⊑ₛLat.⊔ₛ-least {x = ↑ p₁} {↑ p₂} {⊤ₛ} p₁ p₂) (⊔-lub q₁ q₂)
  ⊔-lub (⊑ι₁ q₁)         (⊑ι₁ q₂)                 = ⊑ι₁ (⊔-lub q₁ q₂)
  ⊔-lub (⊑ι₂ q₁)         (⊑ι₂ q₂)                 = ⊑ι₂ (⊔-lub q₁ q₂)
  ⊔-lub (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂)       = ⊑case₁ (⊑ₛLat.⊔ₛ-least {x = ↑ p₁} {↑ p₂} {⊤ₛ} p₁ p₂) (⊔-lub q₁ q₂) (⊑ₛLat.⊔ₛ-least {x = ↑ r₁} {↑ r₂} {⊤ₛ} r₁ r₂)
  ⊔-lub (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂)       = ⊑case₂ (⊑ₛLat.⊔ₛ-least {x = ↑ p₁} {↑ p₂} {⊤ₛ} p₁ p₂) (⊑ₛLat.⊔ₛ-least {x = ↑ r₁} {↑ r₂} {⊤ₛ} r₁ r₂) (⊔-lub q₁ q₂)
  ⊔-lub (⊑π₁ q₁)         (⊑π₁ q₂)                 = ⊑π₁ (⊔-lub q₁ q₂)
  ⊔-lub (⊑π₂ q₁)         (⊑π₂ q₂)                 = ⊑π₂ (⊔-lub q₁ q₂)
  ⊔-lub (⊑Λ q₁)          (⊑Λ q₂)                  = ⊑Λ (⊔-lub q₁ q₂)
  ⊔-lub (⊑def₁ q₁ p₁)    (⊑def₁ q₂ p₂)            = ⊑def₁ (⊔-lub q₁ q₂) (⊑ₛLat.⊔ₛ-least {x = ↑ p₁} {↑ p₂} {⊤ₛ} p₁ p₂)
  ⊔-lub (⊑def₂ p₁ q₁)    (⊑def₂ p₂ q₂)            = ⊑def₂ (⊑ₛLat.⊔ₛ-least {x = ↑ p₁} {↑ p₂} {⊤ₛ} p₁ p₂) (⊔-lub q₁ q₂)

instance
  ctx-meet : HasMeet Ctx
  ctx-meet = record { _⊓_ = _⊓c_ ; closure = λ p q → ⊑.trans {A = Ctx} (⊓-lb₁ p q) p }
  ctx-join : HasJoin Ctx
  ctx-join = record { _⊔_ = _⊔c_ ; closure = ⊔-lub }

private
  □-⊑ : ∀ C → □ C ⊑ C
  □-⊑ ○                    = ⊑○
  □-⊑ (λ: τ ⇒ C)           = ⊑λ ⊑□ (□-⊑ C)
  □-⊑ (λ⇒ C)               = ⊑λu (□-⊑ C)
  □-⊑ (C ∘₁ e)             = ⊑∘₁ (□-⊑ C) ⊑□
  □-⊑ (e ∘₂ C)             = ⊑∘₂ ⊑□ (□-⊑ C)
  □-⊑ (C < τ >₁)           = ⊑<>₁ (□-⊑ C) ⊑□
  □-⊑ (C &₁ e)             = ⊑&₁ (□-⊑ C) ⊑□
  □-⊑ (e &₂ C)             = ⊑&₂ ⊑□ (□-⊑ C)
  □-⊑ (ι₁ C)               = ⊑ι₁ (□-⊑ C)
  □-⊑ (ι₂ C)               = ⊑ι₂ (□-⊑ C)
  □-⊑ (case e of C ·₁ f)   = ⊑case₁ ⊑□ (□-⊑ C) ⊑□
  □-⊑ (case e of₂ f · C)   = ⊑case₂ ⊑□ ⊑□ (□-⊑ C)
  □-⊑ (π₁ C)               = ⊑π₁ (□-⊑ C)
  □-⊑ (π₂ C)               = ⊑π₂ (□-⊑ C)
  □-⊑ (Λ C)                = ⊑Λ (□-⊑ C)
  □-⊑ (def C ⊢₁ e)         = ⊑def₁ (□-⊑ C) ⊑□
  □-⊑ (def e ⊢₂ C)         = ⊑def₂ ⊑□ (□-⊑ C)

  ⊥ₛ' : ∀ {C : Ctx} → ⌊ C ⌋
  ⊥ₛ' {C} = □ C isSlice □-⊑ C

  ⊥ₛ-min : ∀ {C : Ctx} → Minimum (_⊑ₛ_ {A = Ctx} {a = C}) ⊥ₛ'
  ⊥ₛ-min (_ isSlice ⊑○)              = ⊑○
  ⊥ₛ-min (_ isSlice ⊑λ p q)          = ⊑λ ⊑□ (⊥ₛ-min (↑ q))
  ⊥ₛ-min (_ isSlice ⊑λu q)           = ⊑λu (⊥ₛ-min (↑ q))
  ⊥ₛ-min (_ isSlice ⊑∘₁ q p)         = ⊑∘₁ (⊥ₛ-min (↑ q)) ⊑□
  ⊥ₛ-min (_ isSlice ⊑∘₂ p q)         = ⊑∘₂ ⊑□ (⊥ₛ-min (↑ q))
  ⊥ₛ-min (_ isSlice ⊑<>₁ q p)        = ⊑<>₁ (⊥ₛ-min (↑ q)) ⊑□
  ⊥ₛ-min (_ isSlice ⊑&₁ q p)         = ⊑&₁ (⊥ₛ-min (↑ q)) ⊑□
  ⊥ₛ-min (_ isSlice ⊑&₂ p q)         = ⊑&₂ ⊑□ (⊥ₛ-min (↑ q))
  ⊥ₛ-min (_ isSlice ⊑ι₁ q)           = ⊑ι₁ (⊥ₛ-min (↑ q))
  ⊥ₛ-min (_ isSlice ⊑ι₂ q)           = ⊑ι₂ (⊥ₛ-min (↑ q))
  ⊥ₛ-min (_ isSlice ⊑case₁ p q r)    = ⊑case₁ ⊑□ (⊥ₛ-min (↑ q)) ⊑□
  ⊥ₛ-min (_ isSlice ⊑case₂ p r q)    = ⊑case₂ ⊑□ ⊑□ (⊥ₛ-min (↑ q))
  ⊥ₛ-min (_ isSlice ⊑π₁ q)           = ⊑π₁ (⊥ₛ-min (↑ q))
  ⊥ₛ-min (_ isSlice ⊑π₂ q)           = ⊑π₂ (⊥ₛ-min (↑ q))
  ⊥ₛ-min (_ isSlice ⊑Λ q)            = ⊑Λ (⊥ₛ-min (↑ q))
  ⊥ₛ-min (_ isSlice ⊑def₁ q p)       = ⊑def₁ (⊥ₛ-min (↑ q)) ⊑□
  ⊥ₛ-min (_ isSlice ⊑def₂ p q)       = ⊑def₂ ⊑□ (⊥ₛ-min (↑ q))

  ⊔ₛ-ub₁ : ∀ {C : Ctx} (γ₁ γ₂ : ⌊ C ⌋) → γ₁ ⊑ₛ (γ₁ ⊔ₛ γ₂)
  ⊔ₛ-ub₁ γ₁ γ₂ = ⊔-ub₁ (γ₁ .proof) (γ₂ .proof)

  ⊔ₛ-ub₂ : ∀ {C : Ctx} (γ₁ γ₂ : ⌊ C ⌋) → γ₂ ⊑ₛ (γ₁ ⊔ₛ γ₂)
  ⊔ₛ-ub₂ γ₁ γ₂ = ⊔-ub₂ (γ₁ .proof) (γ₂ .proof)

  -- Distributivity
  dist : ∀ {C C₁ C₂ C₃} → C₁ ⊑ C → C₂ ⊑ C → C₃ ⊑ C
       → C₁ ⊓c (C₂ ⊔c C₃) ≡ (C₁ ⊓c C₂) ⊔c (C₁ ⊓c C₃)
  dist ⊑○ ⊑○ ⊑○ = refl
  dist (⊑λ p₁ q₁) (⊑λ p₂ q₂) (⊑λ p₃ q₃)
    = cong₂ λ:_⇒_ (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ p₁) (↑ p₂) (↑ p₃)) (dist q₁ q₂ q₃)
  dist (⊑λu q₁) (⊑λu q₂) (⊑λu q₃)
    = cong λ⇒_ (dist q₁ q₂ q₃)
  dist (⊑∘₁ q₁ p₁) (⊑∘₁ q₂ p₂) (⊑∘₁ q₃ p₃)
    = cong₂ _∘₁_ (dist q₁ q₂ q₃) (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ p₁) (↑ p₂) (↑ p₃))
  dist (⊑∘₂ p₁ q₁) (⊑∘₂ p₂ q₂) (⊑∘₂ p₃ q₃)
    = cong₂ _∘₂_ (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ p₁) (↑ p₂) (↑ p₃)) (dist q₁ q₂ q₃)
  dist (⊑<>₁ q₁ p₁) (⊑<>₁ q₂ p₂) (⊑<>₁ q₃ p₃)
    = cong₂ _<_>₁ (dist q₁ q₂ q₃) (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ p₁) (↑ p₂) (↑ p₃))
  dist (⊑&₁ q₁ p₁) (⊑&₁ q₂ p₂) (⊑&₁ q₃ p₃)
    = cong₂ _&₁_ (dist q₁ q₂ q₃) (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ p₁) (↑ p₂) (↑ p₃))
  dist (⊑&₂ p₁ q₁) (⊑&₂ p₂ q₂) (⊑&₂ p₃ q₃)
    = cong₂ _&₂_ (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ p₁) (↑ p₂) (↑ p₃)) (dist q₁ q₂ q₃)
  dist (⊑ι₁ q₁) (⊑ι₁ q₂) (⊑ι₁ q₃)
    = cong ι₁ (dist q₁ q₂ q₃)
  dist (⊑ι₂ q₁) (⊑ι₂ q₂) (⊑ι₂ q₃)
    = cong ι₂ (dist q₁ q₂ q₃)
  dist (⊑case₁ p₁ q₁ r₁) (⊑case₁ p₂ q₂ r₂) (⊑case₁ p₃ q₃ r₃)
    = case₁-cong (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ p₁) (↑ p₂) (↑ p₃))
                 (dist q₁ q₂ q₃)
                 (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ r₁) (↑ r₂) (↑ r₃))
    where
    case₁-cong : ∀ {a a' : Exp} {b b' : Ctx} {c c' : Exp}
               → a ≡ a' → b ≡ b' → c ≡ c'
               → case a of b ·₁ c ≡ case a' of b' ·₁ c'
    case₁-cong refl refl refl = refl
  dist (⊑case₂ p₁ r₁ q₁) (⊑case₂ p₂ r₂ q₂) (⊑case₂ p₃ r₃ q₃)
    = case₂-cong (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ p₁) (↑ p₂) (↑ p₃))
                 (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ r₁) (↑ r₂) (↑ r₃))
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
    = cong₂ def_⊢₁_ (dist q₁ q₂ q₃) (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ p₁) (↑ p₂) (↑ p₃))
  dist (⊑def₂ p₁ q₁) (⊑def₂ p₂ q₂) (⊑def₂ p₃ q₃)
    = cong₂ def_⊢₂_ (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ p₁) (↑ p₂) (↑ p₃)) (dist q₁ q₂ q₃)

  ⊓ₛ-distribˡ-⊔ₛ' : ∀ {C : Ctx} (γ₁ γ₂ γ₃ : ⌊ C ⌋) → (γ₁ ⊓ₛ (γ₂ ⊔ₛ γ₃)) ≈ₛ ((γ₁ ⊓ₛ γ₂) ⊔ₛ (γ₁ ⊓ₛ γ₃))
  ⊓ₛ-distribˡ-⊔ₛ' γ₁ γ₂ γ₃ = dist (γ₁ .proof) (γ₂ .proof) (γ₃ .proof)

postulate
  ctx-¬ₛ : ∀ {C : Ctx} → ⌊ C ⌋ → ⌊ C ⌋
  ctx-⊔ₛ-complement : ∀ {C : Ctx} (s : ⌊ C ⌋) → (s ⊔ₛ ctx-¬ₛ s) ≈ₛ ⊤ₛ {a = C}
  ctx-⊓ₛ-complement : ∀ {C : Ctx} (s : ⌊ C ⌋) → (s ⊓ₛ ctx-¬ₛ s) ≈ₛ (⊥ₛ' {C})
  ctx-¬ₛ-cong : ∀ {C : Ctx} {s₁ s₂ : ⌊ C ⌋} → s₁ ≈ₛ s₂ → ctx-¬ₛ s₁ ≈ₛ ctx-¬ₛ s₂

instance
  ctx-sliceLattice : SliceLattice Ctx
  ctx-sliceLattice = record
    { ⊥ₛ = ⊥ₛ'
    ; ⊥ₛ-min = ⊥ₛ-min
    ; x⊓ₛy⊑ₛx = λ s₁ s₂ → ⊓-lb₁ (s₁ .proof) (s₂ .proof)
    ; x⊓ₛy⊑ₛy = λ s₁ s₂ → ⊓-lb₂ (s₁ .proof) (s₂ .proof)
    ; ⊓ₛ-greatest = λ {_} {s} {s₁} {s₂} p q → ⊓-glb (s₁ .proof) (s₂ .proof) p q
    ; x⊑ₛx⊔ₛy = ⊔ₛ-ub₁
    ; y⊑ₛx⊔ₛy = ⊔ₛ-ub₂
    ; ⊓ₛ-distribˡ-⊔ₛ = ⊓ₛ-distribˡ-⊔ₛ'
    ; ¬ₛ_ = ctx-¬ₛ
    ; ⊔ₛ-complement = ctx-⊔ₛ-complement
    ; ⊓ₛ-complement = ctx-⊓ₛ-complement
    ; ¬ₛ-cong = ctx-¬ₛ-cong
    }
