module Core.Ctx.Precision where

open import Data.Product using (_,_; uncurry)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong; cong₂; inspect; [_]; _≢_)
open import Relation.Nullary using (Dec; yes; no; map′; ¬_)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Core.Typ using (Typ)
  renaming (_⊑_ to _⊑t_; _⊑?_ to _⊑t?_;
            module ⊑ to ⊑t)
open import Core.Exp using (Exp; ⊑□; ⊑∘; ⊑&; ⊑def; ⊑λ; ⊑ι₁; ⊑ι₂; ⊑Λ; ⊑λu; ⊑<>; ⊑case; ⊑π₁; ⊑π₂)
  renaming (_⊑_ to _⊑e_; _⊑?_ to _⊑e?_;
            module ⊑ to ⊑e)

open import Core.Ctx.Base
open import Core.Ctx.Equality using () renaming (_≟_ to _≟Ctx_)

-- Syntactic precision for contexts
-- Note: only matching constructors are related (no global bottom)
data _⊑_ : Ctx → Ctx → Set where
  ⊑○      :                                           ○          ⊑ ○
  ⊑λ      :  ∀ {τ τ' C C'}    →  τ ⊑t τ' → C ⊑ C'  →  λ: τ ⇒ C   ⊑ λ: τ' ⇒ C'
  ⊑λu     :  ∀ {C C'}         →  C ⊑ C'            →  λ⇒ C       ⊑ λ⇒ C'
  ⊑∘₁     :  ∀ {C C' e e'}    →  C ⊑ C' → e ⊑e e'  →  C ∘₁ e     ⊑ C' ∘₁ e'
  ⊑∘₂     :  ∀ {e e' C C'}    →  e ⊑e e' → C ⊑ C'  →  e ∘₂ C     ⊑ e' ∘₂ C'
  ⊑<>₁    :  ∀ {C C' τ τ'}    →  C ⊑ C' → τ ⊑t τ'  →  C < τ >₁   ⊑ C' < τ' >₁
  ⊑&₁     :  ∀ {C C' e e'}    →  C ⊑ C' → e ⊑e e'  →  C &₁ e     ⊑ C' &₁ e'
  ⊑&₂     :  ∀ {e e' C C'}    →  e ⊑e e' → C ⊑ C'  →  e &₂ C     ⊑ e' &₂ C'
  ⊑ι₁     :  ∀ {C C'}         →  C ⊑ C'            →  ι₁ C       ⊑ ι₁ C'
  ⊑ι₂     :  ∀ {C C'}         →  C ⊑ C'            →  ι₂ C       ⊑ ι₂ C'
  ⊑case₁  :  ∀ {e e' C C' f f'}
             → e ⊑e e' → C ⊑ C' → f ⊑e f'     → case e of C ·₁ f ⊑ case e' of C' ·₁ f'
  ⊑case₂  :  ∀ {e e' f f' C C'}
             → e ⊑e e' → f ⊑e f' → C ⊑ C'     → case e of₂ f · C ⊑ case e' of₂ f' · C'
  ⊑π₁     :  ∀ {C C'}         →  C ⊑ C'            →  π₁ C       ⊑ π₁ C'
  ⊑π₂     :  ∀ {C C'}         →  C ⊑ C'            →  π₂ C       ⊑ π₂ C'
  ⊑Λ      :  ∀ {C C'}         →  C ⊑ C'            →  Λ C        ⊑ Λ C'
  ⊑def₁   :  ∀ {C C' e e'}    →  C ⊑ C' → e ⊑e e'  →  def C ⊢₁ e ⊑ def C' ⊢₁ e'
  ⊑def₂   :  ∀ {e e' C C'}    →  e ⊑e e' → C ⊑ C'  →  def e ⊢₂ C ⊑ def e' ⊢₂ C'

infix 4 _⊑_

private
  ⊑-refl : Reflexive _⊑_
  ⊑-refl {○}                    = ⊑○
  ⊑-refl {λ: _ ⇒ _}             = ⊑λ ⊑t.refl ⊑-refl
  ⊑-refl {λ⇒ _}                 = ⊑λu ⊑-refl
  ⊑-refl {_ ∘₁ _}               = ⊑∘₁ ⊑-refl ⊑e.refl
  ⊑-refl {_ ∘₂ _}               = ⊑∘₂ ⊑e.refl ⊑-refl
  ⊑-refl {_ < _ >₁}             = ⊑<>₁ ⊑-refl ⊑t.refl
  ⊑-refl {_ &₁ _}               = ⊑&₁ ⊑-refl ⊑e.refl
  ⊑-refl {_ &₂ _}               = ⊑&₂ ⊑e.refl ⊑-refl
  ⊑-refl {ι₁ _}                 = ⊑ι₁ ⊑-refl
  ⊑-refl {ι₂ _}                 = ⊑ι₂ ⊑-refl
  ⊑-refl {case _ of _ ·₁ _}     = ⊑case₁ ⊑e.refl ⊑-refl ⊑e.refl
  ⊑-refl {case _ of₂ _ · _}     = ⊑case₂ ⊑e.refl ⊑e.refl ⊑-refl
  ⊑-refl {π₁ _}                 = ⊑π₁ ⊑-refl
  ⊑-refl {π₂ _}                 = ⊑π₂ ⊑-refl
  ⊑-refl {Λ _}                  = ⊑Λ ⊑-refl
  ⊑-refl {def _ ⊢₁ _}           = ⊑def₁ ⊑-refl ⊑e.refl
  ⊑-refl {def _ ⊢₂ _}           = ⊑def₂ ⊑e.refl ⊑-refl

  ⊑-trans : Transitive _⊑_
  ⊑-trans ⊑○ ⊑○                       = ⊑○
  ⊑-trans (⊑λ p q) (⊑λ r s)           = ⊑λ (⊑t.trans p r) (⊑-trans q s)
  ⊑-trans (⊑λu p) (⊑λu q)             = ⊑λu (⊑-trans p q)
  ⊑-trans (⊑∘₁ p q) (⊑∘₁ r s)         = ⊑∘₁ (⊑-trans p r) (⊑e.trans q s)
  ⊑-trans (⊑∘₂ p q) (⊑∘₂ r s)         = ⊑∘₂ (⊑e.trans p r) (⊑-trans q s)
  ⊑-trans (⊑<>₁ p q) (⊑<>₁ r s)       = ⊑<>₁ (⊑-trans p r) (⊑t.trans q s)
  ⊑-trans (⊑&₁ p q) (⊑&₁ r s)         = ⊑&₁ (⊑-trans p r) (⊑e.trans q s)
  ⊑-trans (⊑&₂ p q) (⊑&₂ r s)         = ⊑&₂ (⊑e.trans p r) (⊑-trans q s)
  ⊑-trans (⊑ι₁ p) (⊑ι₁ q)             = ⊑ι₁ (⊑-trans p q)
  ⊑-trans (⊑ι₂ p) (⊑ι₂ q)             = ⊑ι₂ (⊑-trans p q)
  ⊑-trans (⊑case₁ p q r) (⊑case₁ s t u) = ⊑case₁ (⊑e.trans p s) (⊑-trans q t) (⊑e.trans r u)
  ⊑-trans (⊑case₂ p q r) (⊑case₂ s t u) = ⊑case₂ (⊑e.trans p s) (⊑e.trans q t) (⊑-trans r u)
  ⊑-trans (⊑π₁ p) (⊑π₁ q)             = ⊑π₁ (⊑-trans p q)
  ⊑-trans (⊑π₂ p) (⊑π₂ q)             = ⊑π₂ (⊑-trans p q)
  ⊑-trans (⊑Λ p) (⊑Λ q)               = ⊑Λ (⊑-trans p q)
  ⊑-trans (⊑def₁ p q) (⊑def₁ r s)     = ⊑def₁ (⊑-trans p r) (⊑e.trans q s)
  ⊑-trans (⊑def₂ p q) (⊑def₂ r s)     = ⊑def₂ (⊑e.trans p r) (⊑-trans q s)

  ⊑-antisym : Antisymmetric _≡_ _⊑_
  ⊑-antisym ⊑○ ⊑○                         = refl
  ⊑-antisym (⊑λ p q) (⊑λ r s)             = cong₂ λ:_⇒_ (⊑t.antisym p r) (⊑-antisym q s)
  ⊑-antisym (⊑λu p) (⊑λu q)               = cong λ⇒_ (⊑-antisym p q)
  ⊑-antisym (⊑∘₁ p q) (⊑∘₁ r s)           = cong₂ _∘₁_ (⊑-antisym p r) (⊑e.antisym q s)
  ⊑-antisym (⊑∘₂ p q) (⊑∘₂ r s)           = cong₂ _∘₂_ (⊑e.antisym p r) (⊑-antisym q s)
  ⊑-antisym (⊑<>₁ p q) (⊑<>₁ r s)         = cong₂ _<_>₁ (⊑-antisym p r) (⊑t.antisym q s)
  ⊑-antisym (⊑&₁ p q) (⊑&₁ r s)           = cong₂ _&₁_ (⊑-antisym p r) (⊑e.antisym q s)
  ⊑-antisym (⊑&₂ p q) (⊑&₂ r s)           = cong₂ _&₂_ (⊑e.antisym p r) (⊑-antisym q s)
  ⊑-antisym (⊑ι₁ p) (⊑ι₁ q)               = cong ι₁ (⊑-antisym p q)
  ⊑-antisym (⊑ι₂ p) (⊑ι₂ q)               = cong ι₂ (⊑-antisym p q)
  ⊑-antisym (⊑case₁ p q r) (⊑case₁ s t u) with ⊑e.antisym p s | ⊑-antisym q t | ⊑e.antisym r u
  ... | refl | refl | refl = refl
  ⊑-antisym (⊑case₂ p q r) (⊑case₂ s t u) with ⊑e.antisym p s | ⊑e.antisym q t | ⊑-antisym r u
  ... | refl | refl | refl = refl
  ⊑-antisym (⊑π₁ p) (⊑π₁ q)               = cong π₁ (⊑-antisym p q)
  ⊑-antisym (⊑π₂ p) (⊑π₂ q)               = cong π₂ (⊑-antisym p q)
  ⊑-antisym (⊑Λ p) (⊑Λ q)                 = cong Λ (⊑-antisym p q)
  ⊑-antisym (⊑def₁ p q) (⊑def₁ r s)       = cong₂ def_⊢₁_ (⊑-antisym p r) (⊑e.antisym q s)
  ⊑-antisym (⊑def₂ p q) (⊑def₂ r s)       = cong₂ def_⊢₂_ (⊑e.antisym p r) (⊑-antisym q s)

  ⊑-isPartialOrder : IsPartialOrder _≡_ _⊑_
  ⊑-isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ where refl → ⊑-refl
      ; trans = ⊑-trans
      }
    ; antisym = ⊑-antisym
    }

  shallow-imprecision : ∀ {c c'} → diag c c' ≡ diff → ¬(c ⊑ c')
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
_⊑?_ : ∀ C C' → Dec (C ⊑ C')
C ⊑? C'                         with diag C C'  | inspect (diag C) C'
○              ⊑? ○                | kind○      | _  = yes  ⊑○
(λ: τ ⇒ C₁)   ⊑? (λ: τ' ⇒ C₁')     | kindλ      | _  = map′ (uncurry ⊑λ)
                                                            (λ where (⊑λ p q) → p , q)
                                                            (τ ⊑t? τ' ×-dec C₁ ⊑? C₁')
(λ⇒ C₁)       ⊑? (λ⇒ C₁')          | kindλu     | _  = map′ ⊑λu (λ where (⊑λu p) → p) (C₁ ⊑? C₁')
(C₁ ∘₁ e)     ⊑? (C₁' ∘₁ e')       | kind∘₁     | _  = map′ (uncurry ⊑∘₁)
                                                            (λ where (⊑∘₁ p q) → p , q)
                                                            (C₁ ⊑? C₁' ×-dec e ⊑e? e')
(e ∘₂ C₁)     ⊑? (e' ∘₂ C₁')       | kind∘₂     | _  = map′ (uncurry ⊑∘₂)
                                                            (λ where (⊑∘₂ p q) → p , q)
                                                            (e ⊑e? e' ×-dec C₁ ⊑? C₁')
(C₁ < τ >₁)   ⊑? (C₁' < τ' >₁)     | kind<>₁    | _  = map′ (uncurry ⊑<>₁)
                                                            (λ where (⊑<>₁ p q) → p , q)
                                                            (C₁ ⊑? C₁' ×-dec τ ⊑t? τ')
(C₁ &₁ e)     ⊑? (C₁' &₁ e')       | kind&₁     | _  = map′ (uncurry ⊑&₁)
                                                            (λ where (⊑&₁ p q) → p , q)
                                                            (C₁ ⊑? C₁' ×-dec e ⊑e? e')
(e &₂ C₁)     ⊑? (e' &₂ C₁')       | kind&₂     | _  = map′ (uncurry ⊑&₂)
                                                            (λ where (⊑&₂ p q) → p , q)
                                                            (e ⊑e? e' ×-dec C₁ ⊑? C₁')
(ι₁ C₁)       ⊑? (ι₁ C₁')          | kindι₁     | _  = map′ ⊑ι₁ (λ where (⊑ι₁ p) → p) (C₁ ⊑? C₁')
(ι₂ C₁)       ⊑? (ι₂ C₁')          | kindι₂     | _  = map′ ⊑ι₂ (λ where (⊑ι₂ p) → p) (C₁ ⊑? C₁')
(case e of C₁ ·₁ f) ⊑? (case e' of C₁' ·₁ f') | kindcase₁ | _
                                                     = map′ (λ where (p , q , r) → ⊑case₁ p q r)
                                                            (λ where (⊑case₁ p q r) → p , q , r)
                                                            (e ⊑e? e' ×-dec C₁ ⊑? C₁' ×-dec f ⊑e? f')
(case e of₂ f · C₁) ⊑? (case e' of₂ f' · C₁') | kindcase₂ | _
                                                     = map′ (λ where (p , q , r) → ⊑case₂ p q r)
                                                            (λ where (⊑case₂ p q r) → p , q , r)
                                                            (e ⊑e? e' ×-dec f ⊑e? f' ×-dec C₁ ⊑? C₁')
(π₁ C₁)       ⊑? (π₁ C₁')          | kindπ₁     | _  = map′ ⊑π₁ (λ where (⊑π₁ p) → p) (C₁ ⊑? C₁')
(π₂ C₁)       ⊑? (π₂ C₁')          | kindπ₂     | _  = map′ ⊑π₂ (λ where (⊑π₂ p) → p) (C₁ ⊑? C₁')
(Λ C₁)        ⊑? (Λ C₁')           | kindΛ      | _  = map′ ⊑Λ (λ where (⊑Λ p) → p) (C₁ ⊑? C₁')
(def C₁ ⊢₁ e) ⊑? (def C₁' ⊢₁ e')   | kinddef₁   | _  = map′ (uncurry ⊑def₁)
                                                            (λ where (⊑def₁ p q) → p , q)
                                                            (C₁ ⊑? C₁' ×-dec e ⊑e? e')
(def e ⊢₂ C₁) ⊑? (def e' ⊢₂ C₁')   | kinddef₂   | _  = map′ (uncurry ⊑def₂)
                                                            (λ where (⊑def₂ p q) → p , q)
                                                            (e ⊑e? e' ×-dec C₁ ⊑? C₁')
_              ⊑? _                | diff       | [ eq ] = no (shallow-imprecision eq)

⊑-isDecPartialOrder : IsDecPartialOrder _≡_ _⊑_
⊑-isDecPartialOrder = record
                      { isPartialOrder = ⊑-isPartialOrder
                      ; _≟_            = _≟Ctx_
                      ; _≤?_           = _⊑?_
                      }

module ⊑ = IsDecPartialOrder ⊑-isDecPartialOrder using (antisym; isPartialOrder; isPreorder; refl; reflexive; trans)

-- Plug preserves precision
plug-preserves-⊑ : ∀ {C C' e e'} → C ⊑ C' → e ⊑e e' → plug C e ⊑e plug C' e'
plug-preserves-⊑ ⊑○ p               = p
plug-preserves-⊑ (⊑λ q r) p         = ⊑λ    q (plug-preserves-⊑ r p)
plug-preserves-⊑ (⊑λu q) p          = ⊑λu   (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑∘₁ q r) p        = ⊑∘    (plug-preserves-⊑ q p) r
plug-preserves-⊑ (⊑∘₂ q r) p        = ⊑∘    q (plug-preserves-⊑ r p)
plug-preserves-⊑ (⊑<>₁ q r) p       = ⊑<>   (plug-preserves-⊑ q p) r
plug-preserves-⊑ (⊑&₁ q r) p        = ⊑&    (plug-preserves-⊑ q p) r
plug-preserves-⊑ (⊑&₂ q r) p        = ⊑&    q (plug-preserves-⊑ r p)
plug-preserves-⊑ (⊑ι₁ q) p          = ⊑ι₁   (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑ι₂ q) p          = ⊑ι₂   (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑case₁ q r s) p   = ⊑case q (plug-preserves-⊑ r p) s
plug-preserves-⊑ (⊑case₂ q r s) p   = ⊑case q r (plug-preserves-⊑ s p)
plug-preserves-⊑ (⊑π₁ q) p          = ⊑π₁   (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑π₂ q) p          = ⊑π₂   (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑Λ q) p           = ⊑Λ    (plug-preserves-⊑ q p)
plug-preserves-⊑ (⊑def₁ q r) p      = ⊑def  (plug-preserves-⊑ q p) r
plug-preserves-⊑ (⊑def₂ q r) p      = ⊑def  q (plug-preserves-⊑ r p)

-- Instantiate generic Slice module for contexts
open import Core.Slice ⊑-isDecPartialOrder public

import Core.Instances as I
instance ctx-precision : I.HasPrecision Ctx
         ctx-precision = record { _⊑_ = _⊑_ ; isDecPartialOrder = ⊑-isDecPartialOrder }
