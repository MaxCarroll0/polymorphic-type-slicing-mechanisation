module Core.Ctx.Equality where

open import Data.Product using (_,_; uncurry)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; inspect; [_])
open import Relation.Nullary using (Dec; yes; no; map′)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Core.Instances
open import Core.Typ
open import Core.Exp
open import Core.Ctx.Base

private
  _≟c_ : (C C' : Ctx) → Dec (C ≡ C')
  C         ≟c C'               with diag C C' | inspect (diag C) C'
  ...                             | kind○     | _ = yes  refl
  (λ: τ ⇒ C₁)  ≟c (λ: τ' ⇒ C₁')    | kindλ     | _ = map′ (uncurry (cong₂ λ:_⇒_))
                                                        (λ where refl → refl , refl)
                                                        (τ ≟ τ' ×-dec C₁ ≟c C₁')
  (λ⇒ C₁)      ≟c (λ⇒ C₁')         | kindλu    | _ = map′ (cong λ⇒_)
                                                        (λ where refl → refl) (C₁ ≟c C₁')
  (C₁ ∘₁ e)    ≟c (C₁' ∘₁ e')      | kind∘₁    | _ = map′ (uncurry (cong₂ _∘₁_))
                                                        (λ where refl → refl , refl)
                                                        (C₁ ≟c C₁' ×-dec e ≟ e')
  (e ∘₂ C₁)    ≟c (e' ∘₂ C₁')      | kind∘₂    | _ = map′ (uncurry (cong₂ _∘₂_))
                                                        (λ where refl → refl , refl)
                                                        (e ≟ e' ×-dec C₁ ≟c C₁')
  (C₁ < τ >₁)  ≟c (C₁' < τ' >₁)    | kind<>₁   | _ = map′ (uncurry (cong₂ _<_>₁))
                                                        (λ where refl → refl , refl)
                                                        (C₁ ≟c C₁' ×-dec τ ≟ τ')
  (C₁ &₁ e)    ≟c (C₁' &₁ e')      | kind&₁    | _ = map′ (uncurry (cong₂ _&₁_))
                                                        (λ where refl → refl , refl)
                                                        (C₁ ≟c C₁' ×-dec e ≟ e')
  (e &₂ C₁)    ≟c (e' &₂ C₁')      | kind&₂    | _ = map′ (uncurry (cong₂ _&₂_))
                                                        (λ where refl → refl , refl)
                                                        (e ≟ e' ×-dec C₁ ≟c C₁')
  (ι₁ C₁)      ≟c (ι₁ C₁')         | kindι₁    | _ = map′ (cong ι₁)
                                                        (λ where refl → refl) (C₁ ≟c C₁')
  (ι₂ C₁)      ≟c (ι₂ C₁')         | kindι₂    | _ = map′ (cong ι₂)
                                                        (λ where refl → refl) (C₁ ≟c C₁')
  (case e of C₁ ·₁ f)  ≟c (case e' of C₁' ·₁ f')  | kindcase₁ | _
                                                  = map′ (λ where (refl , refl , refl) → refl)
                                                         (λ where refl → refl , refl , refl)
                                                         (e ≟ e' ×-dec C₁ ≟c C₁' ×-dec f ≟ f')
  (case e of₂ f · C₁)  ≟c (case e' of₂ f' · C₁')  | kindcase₂ | _
                                                  = map′ (λ where (refl , refl , refl) → refl)
                                                         (λ where refl → refl , refl , refl)
                                                         (e ≟ e' ×-dec f ≟ f' ×-dec C₁ ≟c C₁')
  (π₁ C₁)      ≟c (π₁ C₁')         | kindπ₁    | _ = map′ (cong π₁)
                                                        (λ where refl → refl) (C₁ ≟c C₁')
  (π₂ C₁)      ≟c (π₂ C₁')         | kindπ₂    | _ = map′ (cong π₂)
                                                        (λ where refl → refl) (C₁ ≟c C₁')
  (Λ C₁)       ≟c (Λ C₁')          | kindΛ     | _ = map′ (cong Λ)
                                                        (λ where refl → refl) (C₁ ≟c C₁')
  (def C₁ ⊢₁ e) ≟c (def C₁' ⊢₁ e') | kinddef₁  | _ = map′ (uncurry (cong₂ def_⊢₁_))
                                                        (λ where refl → refl , refl)
                                                        (C₁ ≟c C₁' ×-dec e ≟ e')
  (def e ⊢₂ C₁) ≟c (def e' ⊢₂ C₁') | kinddef₂  | _ = map′ (uncurry (cong₂ def_⊢₂_))
                                                        (λ where refl → refl , refl)
                                                        (e ≟ e' ×-dec C₁ ≟c C₁')
  ...                             | diff      | [ as ] = no λ where refl → shallow-disequality as

instance ctx-decEq : HasDecEq Ctx
         ctx-decEq = record { _≟_ = _≟c_ }
