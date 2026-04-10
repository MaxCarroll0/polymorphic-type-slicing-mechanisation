module Core.Ctx.Precision where

open import Data.Product using (_,_; uncurry)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong; cong₂; inspect; [_]; _≢_)
open import Relation.Nullary using (Dec; yes; no; map′; ¬_)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Core.Instances
open import Core.Typ hiding (□)
open import Core.Exp hiding (□)
import Core.Exp as E using (⊑□; ⊑∘; ⊑&; ⊑def; ⊑λ; ⊑ι₁; ⊑ι₂; ⊑Λ; ⊑λu; ⊑<>; ⊑case; ⊑π₁; ⊑π₂)

open import Core.Ctx.Base
open import Core.Ctx.Equality

-- Syntactic precision for contexts
-- Note: only matching constructors are related (no global bottom)
data _⊑c_ : Ctx → Ctx → Set where
  ⊑○      :                                           ○          ⊑c ○
  ⊑λ      :  ∀ {τ τ' C C'}    →  τ ⊑ τ' → C ⊑c C'  →  λ: τ ⇒ C   ⊑c λ: τ' ⇒ C'
  ⊑λu     :  ∀ {C C'}         →  C ⊑c C'            →  λ⇒ C       ⊑c λ⇒ C'
  ⊑∘₁     :  ∀ {C C' e e'}    →  C ⊑c C' → e ⊑ e'  →  C ∘₁ e     ⊑c C' ∘₁ e'
  ⊑∘₂     :  ∀ {e e' C C'}    →  e ⊑ e' → C ⊑c C'  →  e ∘₂ C     ⊑c e' ∘₂ C'
  ⊑<>₁    :  ∀ {C C' τ τ'}    →  C ⊑c C' → τ ⊑ τ'  →  C < τ >₁   ⊑c C' < τ' >₁
  ⊑&₁     :  ∀ {C C' e e'}    →  C ⊑c C' → e ⊑ e'  →  C &₁ e     ⊑c C' &₁ e'
  ⊑&₂     :  ∀ {e e' C C'}    →  e ⊑ e' → C ⊑c C'  →  e &₂ C     ⊑c e' &₂ C'
  ⊑ι₁     :  ∀ {C C'}         →  C ⊑c C'            →  ι₁ C       ⊑c ι₁ C'
  ⊑ι₂     :  ∀ {C C'}         →  C ⊑c C'            →  ι₂ C       ⊑c ι₂ C'
  ⊑case₁  :  ∀ {e e' C C' f f'}
             → e ⊑ e' → C ⊑c C' → f ⊑ f'     → case e of C ·₁ f ⊑c case e' of C' ·₁ f'
  ⊑case₂  :  ∀ {e e' f f' C C'}
             → e ⊑ e' → f ⊑ f' → C ⊑c C'     → case e of₂ f · C ⊑c case e' of₂ f' · C'
  ⊑π₁     :  ∀ {C C'}         →  C ⊑c C'            →  π₁ C       ⊑c π₁ C'
  ⊑π₂     :  ∀ {C C'}         →  C ⊑c C'            →  π₂ C       ⊑c π₂ C'
  ⊑Λ      :  ∀ {C C'}         →  C ⊑c C'            →  Λ C        ⊑c Λ C'
  ⊑def₁   :  ∀ {C C' e e'}    →  C ⊑c C' → e ⊑ e'  →  def C ⊢₁ e ⊑c def C' ⊢₁ e'
  ⊑def₂   :  ∀ {e e' C C'}    →  e ⊑ e' → C ⊑c C'  →  def e ⊢₂ C ⊑c def e' ⊢₂ C'

infix 4 _⊑c_

private
  ⊑-refl : Reflexive _⊑c_
  ⊑-refl {○}                    = ⊑○
  ⊑-refl {λ: _ ⇒ _}             = ⊑λ (⊑.refl {A = Typ}) ⊑-refl
  ⊑-refl {λ⇒ _}                 = ⊑λu ⊑-refl
  ⊑-refl {_ ∘₁ _}               = ⊑∘₁ ⊑-refl (⊑.refl {A = Exp})
  ⊑-refl {_ ∘₂ _}               = ⊑∘₂ (⊑.refl {A = Exp}) ⊑-refl
  ⊑-refl {_ < _ >₁}             = ⊑<>₁ ⊑-refl (⊑.refl {A = Typ})
  ⊑-refl {_ &₁ _}               = ⊑&₁ ⊑-refl (⊑.refl {A = Exp})
  ⊑-refl {_ &₂ _}               = ⊑&₂ (⊑.refl {A = Exp}) ⊑-refl
  ⊑-refl {ι₁ _}                 = ⊑ι₁ ⊑-refl
  ⊑-refl {ι₂ _}                 = ⊑ι₂ ⊑-refl
  ⊑-refl {case _ of _ ·₁ _}     = ⊑case₁ (⊑.refl {A = Exp}) ⊑-refl (⊑.refl {A = Exp})
  ⊑-refl {case _ of₂ _ · _}     = ⊑case₂ (⊑.refl {A = Exp}) (⊑.refl {A = Exp}) ⊑-refl
  ⊑-refl {π₁ _}                 = ⊑π₁ ⊑-refl
  ⊑-refl {π₂ _}                 = ⊑π₂ ⊑-refl
  ⊑-refl {Λ _}                  = ⊑Λ ⊑-refl
  ⊑-refl {def _ ⊢₁ _}           = ⊑def₁ ⊑-refl (⊑.refl {A = Exp})
  ⊑-refl {def _ ⊢₂ _}           = ⊑def₂ (⊑.refl {A = Exp}) ⊑-refl

  ⊑-trans : Transitive _⊑c_
  ⊑-trans ⊑○ ⊑○                       = ⊑○
  ⊑-trans (⊑λ p q) (⊑λ r s)           = ⊑λ (⊑.trans {A = Typ} p r) (⊑-trans q s)
  ⊑-trans (⊑λu p) (⊑λu q)             = ⊑λu (⊑-trans p q)
  ⊑-trans (⊑∘₁ p q) (⊑∘₁ r s)         = ⊑∘₁ (⊑-trans p r) (⊑.trans {A = Exp} q s)
  ⊑-trans (⊑∘₂ p q) (⊑∘₂ r s)         = ⊑∘₂ (⊑.trans {A = Exp} p r) (⊑-trans q s)
  ⊑-trans (⊑<>₁ p q) (⊑<>₁ r s)       = ⊑<>₁ (⊑-trans p r) (⊑.trans {A = Typ} q s)
  ⊑-trans (⊑&₁ p q) (⊑&₁ r s)         = ⊑&₁ (⊑-trans p r) (⊑.trans {A = Exp} q s)
  ⊑-trans (⊑&₂ p q) (⊑&₂ r s)         = ⊑&₂ (⊑.trans {A = Exp} p r) (⊑-trans q s)
  ⊑-trans (⊑ι₁ p) (⊑ι₁ q)             = ⊑ι₁ (⊑-trans p q)
  ⊑-trans (⊑ι₂ p) (⊑ι₂ q)             = ⊑ι₂ (⊑-trans p q)
  ⊑-trans (⊑case₁ p q r) (⊑case₁ s t u) = ⊑case₁ (⊑.trans {A = Exp} p s) (⊑-trans q t) (⊑.trans {A = Exp} r u)
  ⊑-trans (⊑case₂ p q r) (⊑case₂ s t u) = ⊑case₂ (⊑.trans {A = Exp} p s) (⊑.trans {A = Exp} q t) (⊑-trans r u)
  ⊑-trans (⊑π₁ p) (⊑π₁ q)             = ⊑π₁ (⊑-trans p q)
  ⊑-trans (⊑π₂ p) (⊑π₂ q)             = ⊑π₂ (⊑-trans p q)
  ⊑-trans (⊑Λ p) (⊑Λ q)               = ⊑Λ (⊑-trans p q)
  ⊑-trans (⊑def₁ p q) (⊑def₁ r s)     = ⊑def₁ (⊑-trans p r) (⊑.trans {A = Exp} q s)
  ⊑-trans (⊑def₂ p q) (⊑def₂ r s)     = ⊑def₂ (⊑.trans {A = Exp} p r) (⊑-trans q s)

  ⊑-antisym : Antisymmetric _≡_ _⊑c_
  ⊑-antisym ⊑○ ⊑○                       = refl
  ⊑-antisym (⊑λ p q) (⊑λ r s)           = cong₂ λ:_⇒_ (⊑.antisym {A = Typ} p r) (⊑-antisym q s)
  ⊑-antisym (⊑λu p) (⊑λu q)             = cong λ⇒_ (⊑-antisym p q)
  ⊑-antisym (⊑∘₁ p q) (⊑∘₁ r s)         = cong₂ _∘₁_ (⊑-antisym p r) (⊑.antisym {A = Exp} q s)
  ⊑-antisym (⊑∘₂ p q) (⊑∘₂ r s)         = cong₂ _∘₂_ (⊑.antisym {A = Exp} p r) (⊑-antisym q s)
  ⊑-antisym (⊑<>₁ p q) (⊑<>₁ r s)       = cong₂ _<_>₁ (⊑-antisym p r) (⊑.antisym {A = Typ} q s)
  ⊑-antisym (⊑&₁ p q) (⊑&₁ r s)         = cong₂ _&₁_ (⊑-antisym p r) (⊑.antisym {A = Exp} q s)
  ⊑-antisym (⊑&₂ p q) (⊑&₂ r s)         = cong₂ _&₂_ (⊑.antisym {A = Exp} p r) (⊑-antisym q s)
  ⊑-antisym (⊑ι₁ p) (⊑ι₁ q)             = cong ι₁ (⊑-antisym p q)
  ⊑-antisym (⊑ι₂ p) (⊑ι₂ q)             = cong ι₂ (⊑-antisym p q)
  ⊑-antisym (⊑case₁ p q r) (⊑case₁ s t u) with ⊑.antisym {A = Exp} p s | ⊑-antisym q t | ⊑.antisym {A = Exp} r u
  ... | refl | refl | refl = refl
  ⊑-antisym (⊑case₂ p q r) (⊑case₂ s t u) with ⊑.antisym {A = Exp} p s | ⊑.antisym {A = Exp} q t | ⊑-antisym r u
  ... | refl | refl | refl = refl
  ⊑-antisym (⊑π₁ p) (⊑π₁ q)             = cong π₁ (⊑-antisym p q)
  ⊑-antisym (⊑π₂ p) (⊑π₂ q)             = cong π₂ (⊑-antisym p q)
  ⊑-antisym (⊑Λ p) (⊑Λ q)               = cong Λ (⊑-antisym p q)
  ⊑-antisym (⊑def₁ p q) (⊑def₁ r s)     = cong₂ def_⊢₁_ (⊑-antisym p r) (⊑.antisym {A = Exp} q s)
  ⊑-antisym (⊑def₂ p q) (⊑def₂ r s)     = cong₂ def_⊢₂_ (⊑.antisym {A = Exp} p r) (⊑-antisym q s)

  ⊑-isPartialOrder : IsPartialOrder _≡_ _⊑c_
  ⊑-isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive     = λ where refl → ⊑-refl
      ; trans         = ⊑-trans
      }
    ; antisym = ⊑-antisym
    }

  shallow-imprecision : ∀ {C C'} → diag C C' ≡ diff → ¬(C ⊑c C')
  shallow-imprecision () ⊑○
  shallow-imprecision () (⊑λ _ _)
  shallow-imprecision () (⊑λu _)
  shallow-imprecision () (⊑∘₁ _ _)
  shallow-imprecision () (⊑∘₂ _ _)
  shallow-imprecision () (⊑<>₁ _ _)
  shallow-imprecision () (⊑&₁ _ _)
  shallow-imprecision () (⊑&₂ _ _)
  shallow-imprecision () (⊑ι₁ _)
  shallow-imprecision () (⊑ι₂ _)
  shallow-imprecision () (⊑case₁ _ _ _)
  shallow-imprecision () (⊑case₂ _ _ _)
  shallow-imprecision () (⊑π₁ _)
  shallow-imprecision () (⊑π₂ _)
  shallow-imprecision () (⊑Λ _)
  shallow-imprecision () (⊑def₁ _ _)
  shallow-imprecision () (⊑def₂ _ _)

-- Decidable precision
_⊑c?_ : ∀ C C' → Dec (C ⊑c C')
C ⊑c? C'                       with diag C C' | Eq.inspect (diag C) C'
...                              | kind○     | _ = yes ⊑○
(λ: τ ⇒ C₁)  ⊑c? (λ: τ' ⇒ C₁')  | kindλ     | _ = map′ (uncurry ⊑λ)
                                                        (λ where (⊑λ p q) → p , q)
                                                        (τ ⊑? τ' ×-dec C₁ ⊑c? C₁')
(λ⇒ C₁)      ⊑c? (λ⇒ C₁')       | kindλu    | _ = map′ ⊑λu (λ where (⊑λu p) → p) (C₁ ⊑c? C₁')
(C₁ ∘₁ e)    ⊑c? (C₁' ∘₁ e')    | kind∘₁    | _ = map′ (uncurry ⊑∘₁)
                                                        (λ where (⊑∘₁ p q) → p , q)
                                                        (C₁ ⊑c? C₁' ×-dec e ⊑? e')
(e ∘₂ C₁)    ⊑c? (e' ∘₂ C₁')    | kind∘₂    | _ = map′ (uncurry ⊑∘₂)
                                                        (λ where (⊑∘₂ p q) → p , q)
                                                        (e ⊑? e' ×-dec C₁ ⊑c? C₁')
(C₁ < τ >₁)  ⊑c? (C₁' < τ' >₁)  | kind<>₁   | _ = map′ (uncurry ⊑<>₁)
                                                        (λ where (⊑<>₁ p q) → p , q)
                                                        (C₁ ⊑c? C₁' ×-dec τ ⊑? τ')
(C₁ &₁ e)    ⊑c? (C₁' &₁ e')    | kind&₁    | _ = map′ (uncurry ⊑&₁)
                                                        (λ where (⊑&₁ p q) → p , q)
                                                        (C₁ ⊑c? C₁' ×-dec e ⊑? e')
(e &₂ C₁)    ⊑c? (e' &₂ C₁')    | kind&₂    | _ = map′ (uncurry ⊑&₂)
                                                        (λ where (⊑&₂ p q) → p , q)
                                                        (e ⊑? e' ×-dec C₁ ⊑c? C₁')
(ι₁ C₁)      ⊑c? (ι₁ C₁')       | kindι₁    | _ = map′ ⊑ι₁ (λ where (⊑ι₁ p) → p) (C₁ ⊑c? C₁')
(ι₂ C₁)      ⊑c? (ι₂ C₁')       | kindι₂    | _ = map′ ⊑ι₂ (λ where (⊑ι₂ p) → p) (C₁ ⊑c? C₁')
(case e of C₁ ·₁ f) ⊑c? (case e' of C₁' ·₁ f') | kindcase₁ | _ =
                                                      map′ (λ where (p , q , r) → ⊑case₁ p q r)
                                                           (λ where (⊑case₁ p q r) → p , q , r)
                                                           (e ⊑? e' ×-dec C₁ ⊑c? C₁' ×-dec f ⊑? f')
(case e of₂ f · C₁) ⊑c? (case e' of₂ f' · C₁') | kindcase₂ | _ =
                                                      map′ (λ where (p , q , r) → ⊑case₂ p q r)
                                                           (λ where (⊑case₂ p q r) → p , q , r)
                                                           (e ⊑? e' ×-dec f ⊑? f' ×-dec C₁ ⊑c? C₁')
(π₁ C₁)      ⊑c? (π₁ C₁')       | kindπ₁    | _ = map′ ⊑π₁ (λ where (⊑π₁ p) → p) (C₁ ⊑c? C₁')
(π₂ C₁)      ⊑c? (π₂ C₁')       | kindπ₂    | _ = map′ ⊑π₂ (λ where (⊑π₂ p) → p) (C₁ ⊑c? C₁')
(Λ C₁)       ⊑c? (Λ C₁')        | kindΛ     | _ = map′ ⊑Λ (λ where (⊑Λ p) → p) (C₁ ⊑c? C₁')
(def C₁ ⊢₁ e) ⊑c? (def C₁' ⊢₁ e') | kinddef₁ | _ = map′ (uncurry ⊑def₁)
                                                        (λ where (⊑def₁ p q) → p , q)
                                                        (C₁ ⊑c? C₁' ×-dec e ⊑? e')
(def e ⊢₂ C₁) ⊑c? (def e' ⊢₂ C₁') | kinddef₂ | _ = map′ (uncurry ⊑def₂)
                                                        (λ where (⊑def₂ p q) → p , q)
                                                        (e ⊑? e' ×-dec C₁ ⊑c? C₁')
_            ⊑c? _                | diff      | [ eq ] = no (shallow-imprecision eq)

private
  ⊑-isDecPartialOrder : IsDecPartialOrder _≡_ _⊑c_
  ⊑-isDecPartialOrder = record
                      { isPartialOrder = ⊑-isPartialOrder
                      ; _≟_            = _≟_
                      ; _≤?_           = _⊑c?_
                      }

-- Plug preserves precision
plug-preserves-⊑ : ∀ {C C' e e'} → C ⊑c C' → e ⊑ e' → plug C e ⊑ plug C' e'
plug-preserves-⊑ ⊑○ p               = p
plug-preserves-⊑ (⊑λ q r) p         = E.⊑λ    q (plug-preserves-⊑ r p)
plug-preserves-⊑ (⊑λu q) p          = E.⊑λu   (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑∘₁ q r) p        = E.⊑∘    (plug-preserves-⊑ q p) r
plug-preserves-⊑ (⊑∘₂ q r) p        = E.⊑∘    q (plug-preserves-⊑ r p)
plug-preserves-⊑ (⊑<>₁ q r) p       = E.⊑<>   (plug-preserves-⊑ q p) r
plug-preserves-⊑ (⊑&₁ q r) p        = E.⊑&    (plug-preserves-⊑ q p) r
plug-preserves-⊑ (⊑&₂ q r) p        = E.⊑&    q (plug-preserves-⊑ r p)
plug-preserves-⊑ (⊑ι₁ q) p          = E.⊑ι₁   (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑ι₂ q) p          = E.⊑ι₂   (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑case₁ q r s) p   = E.⊑case q (plug-preserves-⊑ r p) s
plug-preserves-⊑ (⊑case₂ q r s) p   = E.⊑case q r (plug-preserves-⊑ s p)
plug-preserves-⊑ (⊑π₁ q) p          = E.⊑π₁   (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑π₂ q) p          = E.⊑π₂   (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑Λ q) p           = E.⊑Λ    (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑def₁ q r) p      = E.⊑def  (plug-preserves-⊑ q p) r
plug-preserves-⊑ (⊑def₂ q r) p      = E.⊑def  q (plug-preserves-⊑ r p)

instance
  ctx-precision : HasPrecision Ctx
  ctx-precision = record { _⊑_ = _⊑c_ ; isDecPartialOrder = ⊑-isDecPartialOrder }
