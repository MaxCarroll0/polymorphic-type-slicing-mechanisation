{-# OPTIONS --allow-unsolved-metas --allow-incomplete-matches #-}
open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Data.List using (_∷_)
open import Core
open import Core.Typ.Lift
open import Core.Typ.Properties using (⊔-⇒-⊑; ⊔-+-⊑; ⊔-×-⊑; ⊔-∀-⊑; ⊔-ann-⇒-⊑; ⊔-mono-⊑; sub-⊑)
open import Core.Assms.Lift using (hdₛ; tlₛ; cons-decompₛ; shiftΓₛ; unshiftΓₛ; unshift-shiftΓₛ; shift-unshiftΓ)
open import Core.Assms.Precision using (unshiftΓ-⊑; unshiftΓ-shiftΓ; shiftΓ-⊑)
open import Core.Typ.Precision using (~-⊑-down)
open import Core.Typ.Lattice using (module ~)
open import Semantics.Statics
open import Slicing.Analysis.Analysis
open import Slicing.Analysis.AnaSliceCalc
open import Slicing.Synthesis.Synthesis using (MinSynSlice_◂_; minimality; _↓s)
import Slicing.Synthesis.Synthesis as SS
open import Semantics.Graduality using (mode-⊑; ⇒mode-⊑; ⇐mode-⊑;
                                          static-gradual-syn; static-gradual-syn-cls; syn-unicity; syn-cls-unicity)

-- Minimality of extract / extract-pos for MinAna / MinAnaPos (Dissertation §8.6).
module Slicing.Analysis.Minimality where

private
  ⇒-inj-snd : ∀ {a b c d : Typ} → a ⇒ b ≡ c ⇒ d → b ≡ d
  ⇒-inj-snd refl = refl

  ×-inj-fst : ∀ {a b c d : Typ} → a × b ≡ c × d → a ≡ c
  ×-inj-fst refl = refl

  ×-inj-snd : ∀ {a b c d : Typ} → a × b ≡ c × d → b ≡ d
  ×-inj-snd refl = refl

  +-inj-fst : ∀ {a b c d : Typ} → a + b ≡ c + d → a ≡ c
  +-inj-fst refl = refl

  +-inj-snd : ∀ {a b c d : Typ} → a + b ≡ c + d → b ≡ d
  +-inj-snd refl = refl

  ∀-inj : ∀ {a b : Typ} → ∀· a ≡ ∀· b → a ≡ b
  ∀-inj refl = refl

syn-cls-precision : ∀ {n Γ₁ Γ₂ C₁ C₂ τ_p₁ τ_p₂ n_f₁ n_f₂ Γ_f₁ Γ_f₂ m₁ m₂}
                  → Γ₁ ⊑ Γ₂ → C₁ ⊑c C₂ → mode-⊑ m₁ m₂
                  → n , Γ₁ ⊢ C₁ at synPos τ_p₁ ▷ n_f₁ , Γ_f₁ [ m₁ ]
                  → n , Γ₂ ⊢ C₂ at synPos τ_p₂ ▷ n_f₂ , Γ_f₂ [ m₂ ]
                  → τ_p₁ ⊑ τ_p₂
syn-cls-precision Γ⊑ ⊑○ (⇒mode-⊑ τ⊑) s○ s○ = τ⊑
syn-cls-precision Γ⊑ (⊑λ τ_h⊑ C⊑) m⊑ (sλ: _ cls₁) (sλ: _ cls₂)
  = ⊑⇒ τ_h⊑ (syn-cls-precision (⊑∷ τ_h⊑ Γ⊑) C⊑ m⊑ cls₁ cls₂)
syn-cls-precision Γ⊑ (⊑∘₁ C⊑ _) m⊑ (s∘₁ cls₁ eq₁ _) (s∘₁ cls₂ eq₂ _)
  with ⊔-⇒-⊑ (syn-cls-precision Γ⊑ C⊑ m⊑ cls₁ cls₂) eq₂
... | _ , _ , eq₁' , _ , q
  rewrite ⇒-inj-snd (trans (sym eq₁') eq₁) = q
syn-cls-precision Γ⊑ (⊑∘₂ e⊑ _) m⊑ (s∘₂ D₁ eq₁ _) (s∘₂ D₂ eq₂ _)
  with static-gradual-syn Γ⊑ e⊑ D₂
... | _ , D₁' , τ⊑
  with refl ← syn-unicity D₁ D₁'
  with ⊔-⇒-⊑ τ⊑ eq₂
... | _ , _ , eq₁' , _ , q
  rewrite ⇒-inj-snd (trans (sym eq₁') eq₁) = q
syn-cls-precision Γ⊑ (⊑<>₁ C⊑ σ⊑) m⊑ (s<>₁ cls₁ eq₁ _) (s<>₁ cls₂ eq₂ _)
  with ⊔-∀-⊑ (syn-cls-precision Γ⊑ C⊑ m⊑ cls₁ cls₂) eq₂
... | _ , eq₁' , q
  rewrite ∀-inj (trans (sym eq₁') eq₁) = sub-⊑ zero σ⊑ q
syn-cls-precision Γ⊑ (⊑&₁ C⊑ e⊑) m⊑ (s&₁ cls₁ d₁) (s&₁ cls₂ d₂)
  with static-gradual-syn Γ⊑ e⊑ d₂
... | _ , d₁' , τ⊑
  with refl ← syn-unicity d₁ d₁'
  = ⊑× (syn-cls-precision Γ⊑ C⊑ m⊑ cls₁ cls₂) τ⊑
syn-cls-precision Γ⊑ (⊑&₂ e⊑ C⊑) m⊑ (s&₂ d₁ cls₁) (s&₂ d₂ cls₂)
  with static-gradual-syn Γ⊑ e⊑ d₂
... | _ , d₁' , τ⊑
  with refl ← syn-unicity d₁ d₁'
  = ⊑× τ⊑ (syn-cls-precision Γ⊑ C⊑ m⊑ cls₁ cls₂)
syn-cls-precision Γ⊑ (⊑ι₁ C⊑) m⊑ (sι₁ cls₁) (sι₁ cls₂)
  = ⊑+ (syn-cls-precision Γ⊑ C⊑ m⊑ cls₁ cls₂) ⊑□
syn-cls-precision Γ⊑ (⊑ι₂ C⊑) m⊑ (sι₂ cls₁) (sι₂ cls₂)
  = ⊑+ ⊑□ (syn-cls-precision Γ⊑ C⊑ m⊑ cls₁ cls₂)
syn-cls-precision Γ⊑ (⊑case₁ e⊑ C⊑ e'⊑) m⊑
                  (scase₁ D₁ eq₁ cls₁ d₂₁ con₁) (scase₁ D₂ eq₂ cls₂ d₂₂ con₂)
  with static-gradual-syn Γ⊑ e⊑ D₂
... | _ , D₁' , τ⊑
  with refl ← syn-unicity D₁ D₁'
  with ⊔-+-⊑ τ⊑ eq₂
... | _ , _ , eq₁' , p₁ , p₂
  with refl ← +-inj-fst (trans (sym eq₁') eq₁)
     | refl ← +-inj-snd (trans (sym eq₁') eq₁)
  with static-gradual-syn (⊑∷ p₂ Γ⊑) e'⊑ d₂₂
... | _ , d₂₁' , τ₂⊑
  with refl ← syn-unicity d₂₁ d₂₁'
  = ⊔-mono-⊑ con₂ (syn-cls-precision (⊑∷ p₁ Γ⊑) C⊑ m⊑ cls₁ cls₂) τ₂⊑
syn-cls-precision Γ⊑ (⊑case₂ e⊑ e'⊑ C⊑) m⊑
                  (scase₂ D₁ eq₁ d₁₁ cls₁ con₁) (scase₂ D₂ eq₂ d₁₂ cls₂ con₂)
  with static-gradual-syn Γ⊑ e⊑ D₂
... | _ , D₁' , τ⊑
  with refl ← syn-unicity D₁ D₁'
  with ⊔-+-⊑ τ⊑ eq₂
... | _ , _ , eq₁' , p₁ , p₂
  with refl ← +-inj-fst (trans (sym eq₁') eq₁)
     | refl ← +-inj-snd (trans (sym eq₁') eq₁)
  with static-gradual-syn (⊑∷ p₁ Γ⊑) e'⊑ d₁₂
... | _ , d₁₁' , τ₁⊑
  with refl ← syn-unicity d₁₁ d₁₁'
  = ⊔-mono-⊑ con₂ τ₁⊑ (syn-cls-precision (⊑∷ p₂ Γ⊑) C⊑ m⊑ cls₁ cls₂)
syn-cls-precision Γ⊑ (⊑π₁ C⊑) m⊑ (sπ₁ cls₁ eq₁) (sπ₁ cls₂ eq₂)
  with ⊔-×-⊑ (syn-cls-precision Γ⊑ C⊑ m⊑ cls₁ cls₂) eq₂
... | _ , _ , eq₁' , pa , _
  rewrite ×-inj-fst (trans (sym eq₁') eq₁) = pa
syn-cls-precision Γ⊑ (⊑π₂ C⊑) m⊑ (sπ₂ cls₁ eq₁) (sπ₂ cls₂ eq₂)
  with ⊔-×-⊑ (syn-cls-precision Γ⊑ C⊑ m⊑ cls₁ cls₂) eq₂
... | _ , _ , eq₁' , _ , pb
  rewrite ×-inj-snd (trans (sym eq₁') eq₁) = pb
syn-cls-precision Γ⊑ (⊑Λ C⊑) m⊑ (sΛ cls₁) (sΛ cls₂)
  = ⊑∀ (syn-cls-precision (shiftΓ-⊑ Γ⊑) C⊑ m⊑ cls₁ cls₂)
syn-cls-precision Γ⊑ (⊑def₁ C⊑ e⊑) m⊑ (sdef₁ cls₁ d₁) (sdef₁ cls₂ d₂)
  with static-gradual-syn (⊑∷ (syn-cls-precision Γ⊑ C⊑ m⊑ cls₁ cls₂) Γ⊑) e⊑ d₂
... | _ , d₁' , τ⊑
  with refl ← syn-unicity d₁ d₁' = τ⊑
syn-cls-precision Γ⊑ (⊑def₂ e⊑ C⊑) m⊑ (sdef₂ D₁ cls₁) (sdef₂ D₂ cls₂)
  with static-gradual-syn Γ⊑ e⊑ D₂
... | _ , D₁' , τ'⊑
  with refl ← syn-unicity D₁ D₁'
  = syn-cls-precision (⊑∷ τ'⊑ Γ⊑) C⊑ m⊑ cls₁ cls₂


mutual
  extract-minimal : ∀ {n Γ₀ C n_f Γ τ τ_p}
                      {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
                    → (m : MinAna Cls υ)
                    → IsMinimal (extract m)

  extract-pos-minimal : ∀ {n Γ₀ C n_f Γ τ τ_p}
                          {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
                        → (m : MinAnaPos Cls υ)
                        → IsMinimalPos (extract-pos m)

  extract-minimal min□ s' (κ⊑ , γ⊑) =
    ⊑ₛLat.⊥ₛ-min (s' .κ) , ⊑ₛLat.⊥ₛ-min (s' .γ)

  extract-minimal (minSλ: {Cls' = Cls'} υ₁ m) s' (κ⊑ , γ⊑)
    with s' .κ                         | κ⊑                        | s' .valid
  ... | _ isSlice (⊑λ τ-prec body-prec) | ⊑λ binder-prec body⊑inner | _ , _ , sλ: wf'' inner-cls' =
        let γ⊑-inner : (_ ∷ s' .γ .↓) ⊑a extract m .γ .↓
            γ⊑-inner = subst ((_ ∷ s' .γ .↓) ⊑a_)
                             (sym (cons-decompₛ (extract m .γ)))
                             (⊑∷ binder-prec γ⊑)
            inner-s' : AnaSlice Cls' _
            inner-s' = record
              { κ      = ↑ body-prec
              ; γ      = ↑ (⊑∷ τ-prec (s' .γ .proof))
              ; type   = ↑ (syn-cls-precision
                              (⊑∷ τ-prec (s' .γ .proof)) body-prec
                              (⇐mode-⊑ (s' .focus .proof)) inner-cls' Cls')
              ; focus  = s' .focus
              ; focus⊒ = s' .focus⊒
              ; valid  = _ , _ , inner-cls'
              }
            ih-κ , ih-γ-raw = extract-minimal m inner-s' (body⊑inner , γ⊑-inner)
            ih-γ-decomp : (hdₛ (extract m .γ) .↓ ∷ tlₛ (extract m .γ) .↓) ⊑a (_ ∷ s' .γ .↓)
            ih-γ-decomp = subst (_⊑a (_ ∷ s' .γ .↓))
                                (cons-decompₛ (extract m .γ))
                                ih-γ-raw
        in invert-and-build ih-κ ih-γ-decomp
        where
          invert-and-build : ∀ {a b c d}
            → extract m .κ .↓ ⊑c b
            → (hdₛ (extract m .γ) .↓ ∷ a) ⊑a (c ∷ d)
            → ((λ: hdₛ (extract m .γ) .↓ ⇒ extract m .κ .↓) ⊑c (λ: c ⇒ b))
            ∧ (a ⊑a d)
          invert-and-build ih-κ (⊑∷ ih-hd ih-tl) = ⊑λ ih-hd ih-κ , ih-tl
  extract-minimal (minS∘₁ {Cls' = Cls'} {eq = eq} m) s' (κ⊑ , γ⊑)
    with s' .κ                  | κ⊑                  | s' .valid
  ... | _ isSlice (⊑∘₁ s-proof _) | ⊑∘₁ κ-body⊑inner _ | _ , _ , s∘₁ inner-cls' _ _ =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof (⇐mode-⊑ (s' .focus .proof)) inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .γ ; type = _ isSlice τ⊑
                ; focus = s' .focus ; focus⊒ = s' .focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑∘₁ (proj₁ ih) ⊑□ , proj₂ ih
  extract-minimal (minS∘₂ m ss focus focus⊒ cls-lifted) = {!!}
  extract-minimal (minS<>₁ {Cls' = Cls'} {eq = eq} {wf = wf} m) s' (κ⊑ , γ⊑)
    with s' .κ                  | κ⊑                  | s' .valid
  ... | _ isSlice (⊑<>₁ s-proof _) | ⊑<>₁ κ-body⊑inner _ | _ , _ , s<>₁ inner-cls' eq'-real wf' =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof (⇐mode-⊑ (s' .focus .proof)) inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .γ ; type = _ isSlice τ⊑
                ; focus = s' .focus ; focus⊒ = s' .focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑<>₁ (proj₁ ih) ⊑□ , proj₂ ih

  extract-minimal (minS&₁ {Cls' = Cls'} m) s' (κ⊑ , γ⊑)
    with s' .κ                 | κ⊑                 | s' .valid
  ... | _ isSlice (⊑&₁ s-proof _) | ⊑&₁ κ-body⊑inner _ | _ , _ , s&₁ inner-cls' d₂' =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof (⇐mode-⊑ (s' .focus .proof)) inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .γ ; type = _ isSlice τ⊑
                ; focus = s' .focus ; focus⊒ = s' .focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑&₁ (proj₁ ih) ⊑□ , proj₂ ih

  extract-minimal (minS&₂ {Cls' = Cls'} m) s' (κ⊑ , γ⊑)
    with s' .κ                 | κ⊑                 | s' .valid
  ... | _ isSlice (⊑&₂ _ s-proof) | ⊑&₂ _ κ-body⊑inner | _ , _ , s&₂ d₁' inner-cls' =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof (⇐mode-⊑ (s' .focus .proof)) inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .γ ; type = _ isSlice τ⊑
                ; focus = s' .focus ; focus⊒ = s' .focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑&₂ ⊑□ (proj₁ ih) , proj₂ ih
  extract-minimal m@(minScase₁ _ _ _ _ _ _) = {!!}
  extract-minimal m@(minScase₂ _ _ _ _ _ _) = {!!}
  extract-minimal (minSπ₁ {Cls' = Cls'} {eq = eq} m) s' (κ⊑ , γ⊑)
    with s' .κ                | κ⊑                | s' .valid
  ... | _ isSlice (⊑π₁ s-proof) | ⊑π₁ κ-body⊑inner | _ , _ , sπ₁ inner-cls' eq' =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof (⇐mode-⊑ (s' .focus .proof)) inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ      = _ isSlice s-proof
                ; γ      = s' .γ
                ; type   = _ isSlice τ⊑
                ; focus  = s' .focus
                ; focus⊒ = s' .focus⊒
                ; valid  = _ , _ , inner-cls'
                }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑π₁ (proj₁ ih) , proj₂ ih
  extract-minimal (minSπ₂ {Cls' = Cls'} {eq = eq} m) s' (κ⊑ , γ⊑)
    with s' .κ                | κ⊑                | s' .valid
  ... | _ isSlice (⊑π₂ s-proof) | ⊑π₂ κ-body⊑inner | _ , _ , sπ₂ inner-cls' eq' =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof (⇐mode-⊑ (s' .focus .proof)) inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .γ ; type = _ isSlice τ⊑
                ; focus = s' .focus ; focus⊒ = s' .focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑π₂ (proj₁ ih) , proj₂ ih
  extract-minimal (minSΛ {Cls' = Cls'} m) s' (κ⊑ , γ⊑)
    with s' .κ            | κ⊑          | s' .valid
  ... | _ isSlice (⊑Λ C-prec) | ⊑Λ body⊑inner | _ , _ , sΛ inner-cls' =
        let γ⊑-inner : shiftΓₛ (s' .γ) .↓ ⊑a extract m .γ .↓
            γ⊑-inner = subst (shiftΓₛ (s' .γ) .↓ ⊑a_)
                             (shift-unshiftΓ (extract m .γ .↓) (extract m .γ .proof))
                             (shiftΓ-⊑ γ⊑)
            inner-s' : AnaSlice Cls' _
            inner-s' = record
              { κ      = ↑ C-prec
              ; γ      = shiftΓₛ (s' .γ)
              ; type   = ↑ (syn-cls-precision
                              (shiftΓₛ (s' .γ) .proof) C-prec
                              (⇐mode-⊑ (s' .focus .proof)) inner-cls' Cls')
              ; focus  = s' .focus
              ; focus⊒ = s' .focus⊒
              ; valid  = _ , _ , inner-cls'
              }
            ih-κ , ih-γ = extract-minimal m inner-s' (body⊑inner , γ⊑-inner)
            ih-γ-unshift : unshiftΓₛ (extract m .γ) .↓ ⊑a s' .γ .↓
            ih-γ-unshift = subst (unshiftΓₛ (extract m .γ) .↓ ⊑a_)
                                 (unshiftΓ-shiftΓ (s' .γ .↓))
                                 (unshiftΓ-⊑ ih-γ)
        in ⊑Λ ih-κ , ih-γ-unshift
  extract-minimal (minSdef₁ {Cls' = Cls'} m) s' (κ⊑ , γ⊑)
    with s' .κ                    | κ⊑                    | s' .valid
  ... | _ isSlice (⊑def₁ s-proof _) | ⊑def₁ κ-body⊑inner _ | _ , _ , sdef₁ inner-cls' _ =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof (⇐mode-⊑ (s' .focus .proof)) inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .γ ; type = _ isSlice τ⊑
                ; focus = s' .focus ; focus⊒ = s' .focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑def₁ (proj₁ ih) ⊑□ , proj₂ ih

  extract-minimal m@(minSdef₂ _ _ _ _ _ _) = {!!}

  extract-pos-minimal min□Pos s' (κ⊑ , γ⊑ , υ⊑) =
      ⊑ₛLat.⊥ₛ-min (ana-κ s')
    , ⊑ₛLat.⊥ₛ-min (ana-γ s')
    , ⊑ₛLat.⊥ₛ-min (ana-υ_outer s')

  extract-pos-minimal (minA○ υ) s' (⊑○ , γ⊑ , υ⊑)
    with ana-valid s'
  ... | _ , _ , a○ =
          ⊑ₛLat.⊥ₛ-min (ana-κ s')
        , ⊑ₛLat.⊥ₛ-min (ana-γ s')
        , {!!}
  ... | _ , _ , aSub () _
  extract-pos-minimal (minASub {Cls' = Cls'} m) = {!!}
  extract-pos-minimal (minAλ: {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {Cls' = Cls'}
                              m outer-υ-slot c-lifted eq-lifted outer-min)
                       s' (κ⊑ , γ⊑ , υ⊑)
    with s' .ana-κ                  | κ⊑                  | s' .ana-valid
  ... | _ isSlice (⊑λ τ-prec p)     | ⊑λ binder-prec κ-body⊑ | _ , _ , aλ: c' eq' wf' s'-inner-cls'
      with ⊔-ann-⇒-⊑ υ⊑ binder-prec eq-lifted
  ... | _ , _ , derived-eq , τ_b⊑υ-cod
      with refl ← trans (sym derived-eq) eq' =
        let inner = extract-pos m
            hd = hdₛ (ana-γ inner)
            τ_b'⊑τ₂ = ⊑.trans {Typ} τ_b⊑υ-cod (ana-υ_outer inner .proof)
            inner-s' : AnaPosSlice Cls' _
            inner-s' = record
              { κ       = ↑ p
              ; γ       = ↑ (⊑∷ τ-prec (s' .ana-γ .proof))
              ; υ_outer = ↑ τ_b'⊑τ₂
              ; focus   = s' .ana-focus
              ; focus⊒  = s' .ana-focus⊒
              ; valid   = _ , _ , s'-inner-cls'
              }
            γ⊑-inner : _ ⊑a ana-γ inner .↓
            γ⊑-inner = subst (_ ⊑a_) (sym (cons-decompₛ (ana-γ inner)))
                              (⊑∷ binder-prec γ⊑)
            ih-κ , ih-γ-raw , ih-υ = extract-pos-minimal m inner-s' (κ-body⊑ , γ⊑-inner , τ_b⊑υ-cod)
            ih-γ-decomp : (hd .↓ ∷ tlₛ (ana-γ inner) .↓) ⊑a _
            ih-γ-decomp = subst (_⊑a _) (cons-decompₛ (ana-γ inner)) ih-γ-raw
            outer-υ⊑ : outer-υ-slot .↓ ⊑t s' .ana-υ_outer .↓
            outer-υ⊑ = outer-min binder-prec eq' ih-υ
        in ⊑λ (head-of ih-γ-decomp) ih-κ , tail-of ih-γ-decomp , outer-υ⊑
        where
          head-of : ∀ {a b c d} → (a ∷ b) ⊑a (c ∷ d) → a ⊑t c
          head-of (⊑∷ p _) = p
          tail-of : ∀ {a b c d} → (a ∷ b) ⊑a (c ∷ d) → b ⊑a d
          tail-of (⊑∷ _ q) = q
  extract-pos-minimal (minAλ⇒ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} {Cls' = Cls'} m) s' (κ⊑ , γ⊑ , υ⊑)
    with s' .ana-κ                | κ⊑           | s' .ana-valid
  ... | _ isSlice (⊑λu p)          | ⊑λu κ-body⊑ | _ , _ , aλ⇒ s'-match-eq s'-inner-cls'
      with ⊔-⇒-⊑ (s' .ana-υ_outer .proof) eq
  ... | _ , _ , derived-eq , τ_a⊑ , τ_b⊑
      with refl ← trans (sym derived-eq) s'-match-eq =
        let inner = extract-pos m
            outer-υ-slice = ana-υ_outer (extract-pos (minAλ⇒ {eq = eq} m))
            outer-match-eq = match⇒ₛ outer-υ-slice eq
            inner-s' : AnaPosSlice Cls' _
            inner-s' = record
              { κ       = ↑ p
              ; γ       = ↑ (⊑∷ τ_a⊑ (s' .ana-γ .proof))
              ; υ_outer = ↑ τ_b⊑
              ; focus   = s' .ana-focus
              ; focus⊒  = s' .ana-focus⊒
              ; valid   = _ , _ , s'-inner-cls'
              }
            bind-hyp : _ ⊑t (hdₛ (ana-γ inner)) .↓
            bind-hyp =
              let dom-step = ⇒-proj-dom-mono outer-υ-slice eq υ⊑ s'-match-eq
                  bridge   = unmatch⇒-≡-fst {τ = τ} eq (hdₛ (ana-γ inner))
                                              (ana-υ_outer inner) outer-match-eq
              in subst (_ ⊑t_) (sym bridge) dom-step
            ih-υ-hyp : ↑ τ_b⊑ ⊑ₛ ana-υ_outer inner
            ih-υ-hyp =
              let cod-step = ⇒-proj-cod-mono outer-υ-slice eq υ⊑ s'-match-eq
                  bridge   = unmatch⇒-≡-snd {τ = τ} eq (hdₛ (ana-γ inner))
                                              (ana-υ_outer inner) outer-match-eq
              in subst (_ ⊑t_) (sym bridge) cod-step
            γ⊑-inner : _ ⊑a ana-γ inner .↓
            γ⊑-inner = subst (_ ⊑a_) (sym (cons-decompₛ (ana-γ inner)))
                              (⊑∷ bind-hyp γ⊑)
            ih-κ , ih-γ-raw , ih-υ = extract-pos-minimal m inner-s' (κ-body⊑ , γ⊑-inner , ih-υ-hyp)
            ih-γ-decomp : (hdₛ (ana-γ inner) .↓ ∷ tlₛ (ana-γ inner) .↓) ⊑a _
            ih-γ-decomp = subst (_⊑a _) (cons-decompₛ (ana-γ inner)) ih-γ-raw
            outer-υ⊑ : ana-υ_outer (extract-pos (minAλ⇒ {eq = eq} m)) .↓ ⊑t s' .ana-υ_outer .↓
            outer-υ⊑ = unmatch⇒-min-⊑ τ eq (hdₛ (ana-γ inner)) (ana-υ_outer inner)
                         (s' .ana-υ_outer .proof) s'-match-eq (head-of ih-γ-decomp) ih-υ
        in ⊑λu ih-κ , tail-of ih-γ-decomp , outer-υ⊑
        where
          head-of : ∀ {a b c d} → (a ∷ b) ⊑a (c ∷ d) → a ⊑t c
          head-of (⊑∷ p _) = p
          tail-of : ∀ {a b c d} → (a ∷ b) ⊑a (c ∷ d) → b ⊑a d
          tail-of (⊑∷ _ q) = q
  extract-pos-minimal (minA&₁ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} {Cls' = Cls'} m) s' (κ⊑ , γ⊑ , υ⊑)
    with s' .ana-κ                  | κ⊑              | s' .ana-valid
  ... | _ isSlice (⊑&₁ p _)          | ⊑&₁ κ-body⊑ ⊑□ | _ , _ , a&₁ s'-match-eq s'-inner-cls' _
      with ⊔-×-⊑ (s' .ana-υ_outer .proof) eq
  ... | _ , _ , derived-eq , τ_a⊑ , τ_b⊑
      with refl ← trans (sym derived-eq) s'-match-eq =
        let inner = extract-pos m
            outer-υ-slice = ana-υ_outer (extract-pos (minA&₁ {eq = eq} m))
            outer-match-eq = match×ₛ outer-υ-slice eq
            inner-s' : AnaPosSlice Cls' _
            inner-s' = record
              { κ       = ↑ p
              ; γ       = s' .ana-γ
              ; υ_outer = ↑ τ_a⊑
              ; focus   = s' .ana-focus
              ; focus⊒  = s' .ana-focus⊒
              ; valid   = _ , _ , s'-inner-cls'
              }
            ih-υ-hyp : ↑ τ_a⊑ ⊑ₛ ana-υ_outer inner
            ih-υ-hyp =
              let fst-step = ×-proj-fst-mono outer-υ-slice eq υ⊑ s'-match-eq
                  bridge   = unmatch×-≡-fst {τ = τ} eq (ana-υ_outer inner) ⊥ₛ outer-match-eq
              in subst (_ ⊑t_) (sym bridge) fst-step
            ih-κ , ih-γ , ih-υ = extract-pos-minimal m inner-s' (κ-body⊑ , γ⊑ , ih-υ-hyp)
            outer-υ⊑ : ana-υ_outer (extract-pos (minA&₁ {eq = eq} m)) .↓ ⊑t s' .ana-υ_outer .↓
            outer-υ⊑ = unmatch×-min-⊑ τ eq (ana-υ_outer inner) (⊥ₛ {a = τ₂})
                         (s' .ana-υ_outer .proof) s'-match-eq ih-υ ⊑□
        in ⊑&₁ ih-κ ⊑□ , ih-γ , outer-υ⊑
  extract-pos-minimal (minA&₂ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} {Cls' = Cls'} m) s' (κ⊑ , γ⊑ , υ⊑)
    with s' .ana-κ                  | κ⊑              | s' .ana-valid
  ... | _ isSlice (⊑&₂ _ q)          | ⊑&₂ ⊑□ κ-body⊑ | _ , _ , a&₂ s'-match-eq _ s'-inner-cls'
      with ⊔-×-⊑ (s' .ana-υ_outer .proof) eq
  ... | _ , _ , derived-eq , τ_a⊑ , τ_b⊑
      with refl ← trans (sym derived-eq) s'-match-eq =
        let inner = extract-pos m
            outer-υ-slice = ana-υ_outer (extract-pos (minA&₂ {eq = eq} m))
            outer-match-eq = match×ₛ outer-υ-slice eq
            inner-s' : AnaPosSlice Cls' _
            inner-s' = record
              { κ       = ↑ q
              ; γ       = s' .ana-γ
              ; υ_outer = ↑ τ_b⊑
              ; focus   = s' .ana-focus
              ; focus⊒  = s' .ana-focus⊒
              ; valid   = _ , _ , s'-inner-cls'
              }
            ih-υ-hyp : ↑ τ_b⊑ ⊑ₛ ana-υ_outer inner
            ih-υ-hyp =
              let snd-step = ×-proj-snd-mono outer-υ-slice eq υ⊑ s'-match-eq
                  bridge   = unmatch×-≡-snd {τ = τ} eq ⊥ₛ (ana-υ_outer inner) outer-match-eq
              in subst (_ ⊑t_) (sym bridge) snd-step
            ih-κ , ih-γ , ih-υ = extract-pos-minimal m inner-s' (κ-body⊑ , γ⊑ , ih-υ-hyp)
            outer-υ⊑ : ana-υ_outer (extract-pos (minA&₂ {eq = eq} m)) .↓ ⊑t s' .ana-υ_outer .↓
            outer-υ⊑ = unmatch×-min-⊑ τ eq (⊥ₛ {a = τ₁}) (ana-υ_outer inner)
                         (s' .ana-υ_outer .proof) s'-match-eq ⊑□ ih-υ
        in ⊑&₂ ⊑□ ih-κ , ih-γ , outer-υ⊑
  extract-pos-minimal (minAι₁ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} {Cls' = Cls'} m) s' (κ⊑ , γ⊑ , υ⊑)
    with s' .ana-κ                   | κ⊑           | s' .ana-valid
  ... | _ isSlice (⊑ι₁ p)            | ⊑ι₁ κ-body⊑ | _ , _ , aι₁ s'-match-eq s'-inner-cls'
      with ⊔-+-⊑ (s' .ana-υ_outer .proof) eq
  ... | _ , _ , derived-eq , τ_a⊑ , τ_b⊑
      with refl ← trans (sym derived-eq) s'-match-eq =
        let inner-s' : AnaPosSlice Cls' _
            inner-s' = record
              { κ       = ↑ p
              ; γ       = s' .ana-γ
              ; υ_outer = ↑ τ_a⊑
              ; focus   = s' .ana-focus
              ; focus⊒  = s' .ana-focus⊒
              ; valid   = _ , _ , s'-inner-cls'
              }
            ih-υ-hyp : ↑ τ_a⊑ ⊑ₛ ana-υ_outer (extract-pos m)
            ih-υ-hyp =
              let outer-υ-slice = ana-υ_outer (extract-pos (minAι₁ {eq = eq} m))
                  outer-match-eq = match+ₛ outer-υ-slice eq
                  fst-step : _ ⊑t (fst+ₛ' outer-υ-slice eq) .↓
                  fst-step = +-proj-fst-mono outer-υ-slice eq υ⊑ s'-match-eq
                  bridge : (ana-υ_outer (extract-pos m)) .↓ ≡ (fst+ₛ' outer-υ-slice eq) .↓
                  bridge = unmatch+-min-≡-fst {τ = τ} eq (ana-υ_outer (extract-pos m)) ⊥ₛ outer-match-eq
              in subst (_ ⊑t_) (sym bridge) fst-step
            ih-κ , ih-γ , ih-υ = extract-pos-minimal m inner-s' (κ-body⊑ , γ⊑ , ih-υ-hyp)
            outer-υ⊑ : ana-υ_outer (extract-pos (minAι₁ {eq = eq} m)) .↓ ⊑t s' .ana-υ_outer .↓
            outer-υ⊑ = unmatch+-min-⊑ τ eq (ana-υ_outer (extract-pos m)) (⊥ₛ {a = τ₂})
                         (s' .ana-υ_outer .proof) s'-match-eq ih-υ ⊑□
        in ⊑ι₁ ih-κ , ih-γ , outer-υ⊑
  extract-pos-minimal (minAι₂ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} {Cls' = Cls'} m) s' (κ⊑ , γ⊑ , υ⊑)
    with s' .ana-κ                   | κ⊑           | s' .ana-valid
  ... | _ isSlice (⊑ι₂ q)            | ⊑ι₂ κ-body⊑ | _ , _ , aι₂ s'-match-eq s'-inner-cls'
      with ⊔-+-⊑ (s' .ana-υ_outer .proof) eq
  ... | _ , _ , derived-eq , τ_a⊑ , τ_b⊑
      with refl ← trans (sym derived-eq) s'-match-eq =
        let inner-s' : AnaPosSlice Cls' _
            inner-s' = record
              { κ       = ↑ q
              ; γ       = s' .ana-γ
              ; υ_outer = ↑ τ_b⊑
              ; focus   = s' .ana-focus
              ; focus⊒  = s' .ana-focus⊒
              ; valid   = _ , _ , s'-inner-cls'
              }
            ih-υ-hyp : ↑ τ_b⊑ ⊑ₛ ana-υ_outer (extract-pos m)
            ih-υ-hyp =
              let outer-υ-slice = ana-υ_outer (extract-pos (minAι₂ {eq = eq} m))
                  outer-match-eq = match+ₛ outer-υ-slice eq
                  snd-step : _ ⊑t (snd+ₛ' outer-υ-slice eq) .↓
                  snd-step = +-proj-snd-mono outer-υ-slice eq υ⊑ s'-match-eq
                  bridge : (ana-υ_outer (extract-pos m)) .↓ ≡ (snd+ₛ' outer-υ-slice eq) .↓
                  bridge = unmatch+-min-≡-snd {τ = τ} eq ⊥ₛ (ana-υ_outer (extract-pos m)) outer-match-eq
              in subst (_ ⊑t_) (sym bridge) snd-step
            ih-κ , ih-γ , ih-υ = extract-pos-minimal m inner-s' (κ-body⊑ , γ⊑ , ih-υ-hyp)
            outer-υ⊑ : ana-υ_outer (extract-pos (minAι₂ {eq = eq} m)) .↓ ⊑t s' .ana-υ_outer .↓
            outer-υ⊑ = unmatch+-min-⊑ τ eq (⊥ₛ {a = τ₁}) (ana-υ_outer (extract-pos m))
                         (s' .ana-υ_outer .proof) s'-match-eq ⊑□ ih-υ
        in ⊑ι₂ ih-κ , ih-γ , outer-υ⊑
  extract-pos-minimal m@(minAcase₁ _ _ _ _ _) = {!!}
  extract-pos-minimal m@(minAcase₂ _ _ _ _ _) = {!!}
  extract-pos-minimal m@(minAdef₂ _ _ _ _ _) = {!!}
  extract-pos-minimal (minAdef₁ {Cls' = Cls'} m) s' (κ⊑ , γ⊑ , υ⊑)
    with s' .ana-κ                | κ⊑                  | s' .ana-valid
  ... | _ isSlice (⊑def₁ s-proof _) | ⊑def₁ κ-body⊑inner _ | _ , _ , adef₁ inner-cls' _ =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof (⇐mode-⊑ (s' .ana-focus .proof)) inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .ana-γ ; type = _ isSlice τ⊑
                ; focus = s' .ana-focus ; focus⊒ = s' .ana-focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑def₁ (proj₁ ih) ⊑□ , proj₂ ih , ⊑ₛLat.⊥ₛ-min (ana-υ_outer s')
  ... | _ isSlice (⊑def₁ s-proof _) | ⊑def₁ κ-body⊑inner _ | _ , _ , aSub (sdef₁ inner-cls' _) _ =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof (⇐mode-⊑ (s' .ana-focus .proof)) inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .ana-γ ; type = _ isSlice τ⊑
                ; focus = s' .ana-focus ; focus⊒ = s' .ana-focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑def₁ (proj₁ ih) ⊑□ , proj₂ ih , ⊑ₛLat.⊥ₛ-min (ana-υ_outer s')
