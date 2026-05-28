{-# OPTIONS --allow-unsolved-metas --allow-incomplete-matches #-}
open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Data.List using (_∷_)
open import Core
open import Core.Typ.Lift
open import Core.Assms.Lift using (hdₛ; tlₛ; cons-decompₛ; shiftΓₛ; unshiftΓₛ; unshift-shiftΓₛ; shift-unshiftΓ)
open import Core.Assms.Precision using (unshiftΓ-⊑; unshiftΓ-shiftΓ; shiftΓ-⊑)
open import Core.Typ.Precision using (~-⊑-down)
open import Core.Typ.Lattice using (module ~)
open import Semantics.Statics
open import Slicing.Analysis.Analysis
open import Slicing.Analysis.AnaSliceCalc
open import Slicing.Synthesis.Synthesis using (MinSynSlice_◂_; minimality; _↓s)
import Slicing.Synthesis.Synthesis as SS
open import Semantics.Graduality using (static-gradual-syn; static-gradual-syn-cls; syn-unicity; syn-cls-unicity)

module Slicing.Analysis.Minimality where

-- Minimality of extract / extract-pos.
--
-- These lemmas state that the MinAna / MinAnaPos data types are
-- rule-faithfully minimal: every MinAnaPos m extracts to an AnaPosSlice
-- whose triple (κ, γ, υ_outer) is least under the lattice ordering
-- ⊑ana-pos, and similarly extract m is minimal for MinAna under ⊑ana
-- (the pair (κ, γ)).
--
-- Proofs follow the synthesis template
-- (`Slicing.Synthesis.FixedAssmsCalc.extract'`): pattern match on m,
-- destructure an arbitrary alternative s' (especially s'.valid), and
-- discharge each branch using the IH and monotonicity properties of
-- the slice combinators (unmatch{⇒,×,+}, hdₛ/tlₛ).
--
-- The catch-all constructors `minViaAnaSlice` / `minViaAnaPosSlice`
-- take an opaque AnaSlice / AnaPosSlice with no minimality guarantee,
-- so for those cases the proof is left as a hole — the algorithm in
-- `Slicing.Analysis.AnaSlicing` does not use the catch-alls, so any
-- algorithmically-produced slice never reaches them.

-- unmatch{⇒,×,+}-min variants now live in Core.Typ.Lift alongside their
-- precision lemmas.

-- Classification-precision lemma. Provable via static-gradual-syn-cls
-- plus syn-cls-unicity, but unicity requires matching modes. The
-- graduality theorem returns an existential mode, so we cannot pin it
-- to cls₁'s input mode without extra structure (mode-⊑ precondition
-- and direct induction). Postulated until the cleaner proof lands.
postulate
  syn-cls-precision : ∀ {n Γ₁ Γ₂ C₁ C₂ τ_p₁ τ_p₂ n_f₁ n_f₂ Γ_f₁ Γ_f₂ m₁ m₂}
                    → Γ₁ ⊑ Γ₂ → C₁ ⊑c C₂
                    → n , Γ₁ ⊢ C₁ at synPos τ_p₁ ▷ n_f₁ , Γ_f₁ [ m₁ ]
                    → n , Γ₂ ⊢ C₂ at synPos τ_p₂ ▷ n_f₂ , Γ_f₂ [ m₂ ]
                    → τ_p₁ ⊑ τ_p₂

-- Top-level minimality theorems. Mutual because MinAna and MinAnaPos
-- are mutually inductive (minASub, minAdef₁ cross synPos→anaPos; minS∘₂
-- crosses anaPos→synPos).
mutual
  extract-minimal : ∀ {n Γ₀ C n_f Γ τ τ_p}
                      {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
                    → (m : MinAna Cls υ)
                    → IsMinimal (extract m)

  extract-pos-minimal : ∀ {n Γ₀ C n_f Γ τ τ_p}
                          {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]} {υ}
                        → (m : MinAnaPos Cls υ)
                        → IsMinimalPos (extract-pos m)

  -- BASE CASES (proven) ------------------------------------------------

  -- min□: extract → ⊥-ana with κ = ⊥ₛ, γ = ⊥ₛ. Any s' ⊑ ⊥-ana has
  -- s'.κ ⊑ ⊥ₛ and s'.γ ⊑ ⊥ₛ, forcing both to ⊥ₛ; we discharge by ⊥-min.
  extract-minimal min□ s' (κ⊑ , γ⊑) =
    ⊑ₛLat.⊥ₛ-min (s' .κ) , ⊑ₛLat.⊥ₛ-min (s' .γ)

  -- INDUCTIVE CASES (TODO) ---------------------------------------------
  --
  -- Each case below follows the synthesis template:
  --   1. Pattern-match on m to expose the constructor structure.
  --   2. Take an arbitrary alternative s' : AnaPosSlice Cls υ with s' ⊑ extract-pos m.
  --   3. Destructure s'.valid (the underlying classification derivation)
  --      to learn the structural shape of s'.κ, s'.γ, s'.υ_outer.
  --   4. Apply the IH (extract-pos-minimal m') to the projected sub-slice.
  --   5. Use unmatch-min-⊑ / monotonicity to discharge the υ_outer obligation.
  --
  -- Currently unproved cases are below as interactive holes (not
  -- postulates). Comments per case point at the specific machinery
  -- the proof needs.
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
                              (⊑∷ τ-prec (s' .γ .proof)) body-prec inner-cls' Cls')
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
  -- minS∘₁: outer κ shape `C ∘₁ e`. Argument exp slice is □e.
  extract-minimal (minS∘₁ {Cls' = Cls'} {eq = eq} m) s' (κ⊑ , γ⊑)
    with s' .κ                  | κ⊑                  | s' .valid
  ... | _ isSlice (⊑∘₁ s-proof _) | ⊑∘₁ κ-body⊑inner _ | _ , _ , s∘₁ inner-cls' _ _ =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .γ ; type = _ isSlice τ⊑
                ; focus = s' .focus ; focus⊒ = s' .focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑∘₁ (proj₁ ih) ⊑□ , proj₂ ih
  -- minS∘₂ (KEY cross-mutual case).
  --
  -- Outer: s∘₂ D₁ eq Cls' at synPos τ₂. extract.κ = fn.σ ∘₂ ana-κ arg.
  -- s'.valid = s∘₂ D-s' eq-s' arg-cls-s'.
  --
  -- Proof outline:
  --   1. Apply IH on m via inner-arg-s' built from arg-cls-s' (at anaPos τ_a-s'
  --      bridged to anaPos τ₁ via slice). Get υ-fst ⊑t τ_a-s', plus arg.κ ⊑c s'-arg.
  --   2. Build a SynSlice candidate for D₁ at query (unmatch⇒-min eq υ-fst ⊥ₛ)
  --      with progₛ = (s'.γ.↓, s'-fn), syn = D-s'. Need Q ⊑ candidate.type:
  --      unmatch⇒-min-⊑ applied with eq-s' and (1)'s υ-fst⊑τ_a-s'.
  --   3. ss minimality on candidate gives fn.γ ⊑ s'.γ and fn.σ ⊑e s'-fn.
  --   4. Combine (1)+(3) into ⊑∘₂.
  --
  -- Bridging lemmas needed:
  --   - τ_a-s' ⊑t τ₁ (proj-dom-mono on s'.υ_outer-equivalent, but s' is AnaSlice
  --     not AnaPosSlice; derive via syn-precision + ⊔ properties).
  --   - υ-fst.↓ ⊑t τ_a-s' (from IH on m after bridging).
  --
  extract-minimal (minS∘₂ m ss focus focus⊒ cls-lifted) s' s'⊑ = {!TODO: minS∘₂ — uses ss minimality + IH on m. See comment for outline.!}
  -- minS<>₁: outer κ shape `C <τ>₁`.
  extract-minimal (minS<>₁ {Cls' = Cls'} {eq = eq} {wf = wf} m) s' (κ⊑ , γ⊑)
    with s' .κ                  | κ⊑                  | s' .valid
  ... | _ isSlice (⊑<>₁ s-proof _) | ⊑<>₁ κ-body⊑inner _ | _ , _ , s<>₁ inner-cls' eq'-real wf' =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .γ ; type = _ isSlice τ⊑
                ; focus = s' .focus ; focus⊒ = s' .focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑<>₁ (proj₁ ih) ⊑□ , proj₂ ih

  -- minS&₁: outer κ shape `C &₁ e`. Sibling exp slice is □e (minimal).
  extract-minimal (minS&₁ {Cls' = Cls'} m) s' (κ⊑ , γ⊑)
    with s' .κ                 | κ⊑                 | s' .valid
  ... | _ isSlice (⊑&₁ s-proof _) | ⊑&₁ κ-body⊑inner _ | _ , _ , s&₁ inner-cls' d₂' =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .γ ; type = _ isSlice τ⊑
                ; focus = s' .focus ; focus⊒ = s' .focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑&₁ (proj₁ ih) ⊑□ , proj₂ ih

  -- minS&₂: symmetric.
  extract-minimal (minS&₂ {Cls' = Cls'} m) s' (κ⊑ , γ⊑)
    with s' .κ                 | κ⊑                 | s' .valid
  ... | _ isSlice (⊑&₂ _ s-proof) | ⊑&₂ _ κ-body⊑inner | _ , _ , s&₂ d₁' inner-cls' =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .γ ; type = _ isSlice τ⊑
                ; focus = s' .focus ; focus⊒ = s' .focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑&₂ ⊑□ (proj₁ ih) , proj₂ ih
  -- minScase₁: scrutinee and sibling both sliced to □. The κ becomes
  -- `case □ of inner.κ.↓ ·₁ □`. By ⊑case₁ inversion, s'.κ.↓ is forced to
  -- `case □ of s'-C ·₁ □` (with s'-e and s'-e' both □). s'.valid's scase₁
  -- pattern then gives D = ⇑□ (so τ₀-some = □), eq forcing τ₁ = τ₂ = □,
  -- inner-cls' at (□ ∷ s'.γ.↓), d₂ = ⇑□.
  extract-minimal (minScase₁ {Cls' = Cls'} m _ _ _ _ _) s' (κ⊑ , γ⊑)
    with s' .κ                          | κ⊑                       | s' .valid
  ... | _ isSlice (⊑case₁ e-prec body-prec e'-prec) | ⊑case₁ _ body⊑inner _ | _ , _ , scase₁ ⇑□ refl inner-cls' ⇑□ _ =
        let γ⊑-inner : (□ ∷ s' .γ .↓) ⊑a extract m .γ .↓
            γ⊑-inner = subst ((□ ∷ s' .γ .↓) ⊑a_)
                             (sym (cons-decompₛ (extract m .γ)))
                             (⊑∷ ⊑□ γ⊑)
            inner-s' : AnaSlice Cls' _
            inner-s' = record
              { κ      = ↑ body-prec
              ; γ      = ↑ (⊑∷ ⊑□ (s' .γ .proof))
              ; type   = ↑ (syn-cls-precision
                              (⊑∷ ⊑□ (s' .γ .proof))
                              body-prec inner-cls' Cls')
              ; focus  = s' .focus
              ; focus⊒ = s' .focus⊒
              ; valid  = _ , _ , inner-cls'
              }
            ih-κ , ih-γ-raw = extract-minimal m inner-s' (body⊑inner , γ⊑-inner)
            ih-γ-decomp : (hdₛ (extract m .γ) .↓ ∷ tlₛ (extract m .γ) .↓) ⊑a (□ ∷ s' .γ .↓)
            ih-γ-decomp = subst (_⊑a (□ ∷ s' .γ .↓))
                                (cons-decompₛ (extract m .γ))
                                ih-γ-raw
        in invert-and-build ih-κ ih-γ-decomp
        where
          invert-and-build : ∀ {a c d e' C' e''}
            → extract m .κ .↓ ⊑c C'
            → (hdₛ (extract m .γ) .↓ ∷ a) ⊑a (c ∷ d)
            → ((case □ of extract m .κ .↓ ·₁ □) ⊑c (case e' of C' ·₁ e''))
            ∧ (a ⊑a d)
          invert-and-build ih-κ (⊑∷ _ ih-tl) =
            ⊑case₁ ⊑□ ih-κ ⊑□ , ih-tl
  extract-minimal (minScase₂ {Cls' = Cls'} m _ _ _ _ _) s' (κ⊑ , γ⊑)
    with s' .κ                          | κ⊑                       | s' .valid
  ... | _ isSlice (⊑case₂ e-prec e'-prec body-prec) | ⊑case₂ _ _ body⊑inner | _ , _ , scase₂ ⇑□ refl ⇑□ inner-cls' _ =
        let γ⊑-inner : (□ ∷ s' .γ .↓) ⊑a extract m .γ .↓
            γ⊑-inner = subst ((□ ∷ s' .γ .↓) ⊑a_)
                             (sym (cons-decompₛ (extract m .γ)))
                             (⊑∷ ⊑□ γ⊑)
            inner-s' : AnaSlice Cls' _
            inner-s' = record
              { κ      = ↑ body-prec
              ; γ      = ↑ (⊑∷ ⊑□ (s' .γ .proof))
              ; type   = ↑ (syn-cls-precision
                              (⊑∷ ⊑□ (s' .γ .proof))
                              body-prec inner-cls' Cls')
              ; focus  = s' .focus
              ; focus⊒ = s' .focus⊒
              ; valid  = _ , _ , inner-cls'
              }
            ih-κ , ih-γ-raw = extract-minimal m inner-s' (body⊑inner , γ⊑-inner)
            ih-γ-decomp : (hdₛ (extract m .γ) .↓ ∷ tlₛ (extract m .γ) .↓) ⊑a (□ ∷ s' .γ .↓)
            ih-γ-decomp = subst (_⊑a (□ ∷ s' .γ .↓))
                                (cons-decompₛ (extract m .γ))
                                ih-γ-raw
        in invert-and-build ih-κ ih-γ-decomp
        where
          invert-and-build : ∀ {a c d e' e'' C'}
            → extract m .κ .↓ ⊑c C'
            → (hdₛ (extract m .γ) .↓ ∷ a) ⊑a (c ∷ d)
            → ((case □ of₂ □ · extract m .κ .↓) ⊑c (case e' of₂ e'' · C'))
            ∧ (a ⊑a d)
          invert-and-build ih-κ (⊑∷ _ ih-tl) =
            ⊑case₂ ⊑□ ⊑□ ih-κ , ih-tl
  -- minSπ₁: extract is at π₁-shaped outer κ. Invert s'.κ + κ⊑ + s'.valid
  -- (without with-abstracting `extract m`, so the IH `extract-minimal m`
  -- still typechecks against `extract m` rather than a freshly-bound
  -- inner variable). Build inner-s' for Cls', apply IH, lift via ⊑π₁.
  extract-minimal (minSπ₁ {Cls' = Cls'} {eq = eq} m) s' (κ⊑ , γ⊑)
    with s' .κ                | κ⊑                | s' .valid
  ... | _ isSlice (⊑π₁ s-proof) | ⊑π₁ κ-body⊑inner | _ , _ , sπ₁ inner-cls' eq' =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof inner-cls' Cls'
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
  -- minSπ₂: symmetric to minSπ₁.
  extract-minimal (minSπ₂ {Cls' = Cls'} {eq = eq} m) s' (κ⊑ , γ⊑)
    with s' .κ                | κ⊑                | s' .valid
  ... | _ isSlice (⊑π₂ s-proof) | ⊑π₂ κ-body⊑inner | _ , _ , sπ₂ inner-cls' eq' =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .γ ; type = _ isSlice τ⊑
                ; focus = s' .focus ; focus⊒ = s' .focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑π₂ (proj₁ ih) , proj₂ ih
  -- minSΛ: outer κ = Λ C, inner Cls' at (suc n; shiftΓ (suc zero) Γ).
  -- Bridge γ via shift/unshift: inner-s'.γ = shiftΓₛ (s'.γ).
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
                              inner-cls' Cls')
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
  -- minSdef₁: outer κ shape `def C ⊢₁ e`. Body exp slice is □e.
  extract-minimal (minSdef₁ {Cls' = Cls'} m) s' (κ⊑ , γ⊑)
    with s' .κ                    | κ⊑                    | s' .valid
  ... | _ isSlice (⊑def₁ s-proof _) | ⊑def₁ κ-body⊑inner _ | _ , _ , sdef₁ inner-cls' _ =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .γ ; type = _ isSlice τ⊑
                ; focus = s' .focus ; focus⊒ = s' .focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑def₁ (proj₁ ih) ⊑□ , proj₂ ih

  -- minSdef₂: outer κ shape `def e ⊢₂ C`. Body Cls' at extended ctx (τ' ∷ Γ);
  -- analogous to minSλ: but with def₂ wrapper. Uses cons-decompₛ to bridge.
  -- minSdef₂ (restructured): extract.κ.↓ = `def □ ⊢₂ inner.κ.↓` (def-e
  -- sliced to □). For s' ⊑ extract, s'.κ.↓ = `def □ ⊢₂ s'-C` (s'-e is
  -- forced to □ by ⊑□). For s'.valid, sdef₂ rule fires with the def-e
  -- synthesizing □ (via ⇑□), so τ-some = □. inner-cls' lives at (□ ∷ s'.γ.↓).
  extract-minimal (minSdef₂ {Cls' = Cls'} m _ _ _ _ _) s' (κ⊑ , γ⊑)
    with s' .κ                          | κ⊑                       | s' .valid
  ... | _ isSlice (⊑def₂ e-prec body-prec) | ⊑def₂ _ body⊑inner | _ , _ , sdef₂ ⇑□ inner-cls' =
        let γ⊑-inner : (□ ∷ s' .γ .↓) ⊑a extract m .γ .↓
            γ⊑-inner = subst ((□ ∷ s' .γ .↓) ⊑a_)
                             (sym (cons-decompₛ (extract m .γ)))
                             (⊑∷ ⊑□ γ⊑)
            inner-s' : AnaSlice Cls' _
            inner-s' = record
              { κ      = ↑ body-prec
              ; γ      = ↑ (⊑∷ ⊑□ (s' .γ .proof))
              ; type   = ↑ (syn-cls-precision
                              (⊑∷ ⊑□ (s' .γ .proof))
                              body-prec inner-cls' Cls')
              ; focus  = s' .focus
              ; focus⊒ = s' .focus⊒
              ; valid  = _ , _ , inner-cls'
              }
            ih-κ , ih-γ-raw = extract-minimal m inner-s' (body⊑inner , γ⊑-inner)
            ih-γ-decomp : (hdₛ (extract m .γ) .↓ ∷ tlₛ (extract m .γ) .↓) ⊑a (□ ∷ s' .γ .↓)
            ih-γ-decomp = subst (_⊑a (□ ∷ s' .γ .↓))
                                (cons-decompₛ (extract m .γ))
                                ih-γ-raw
        in invert-and-build ih-κ ih-γ-decomp
        where
          invert-and-build : ∀ {a c d e' C'}
            → extract m .κ .↓ ⊑c C'
            → (hdₛ (extract m .γ) .↓ ∷ a) ⊑a (c ∷ d)
            → ((def □ ⊢₂ extract m .κ .↓) ⊑c (def e' ⊢₂ C'))
            ∧ (a ⊑a d)
          invert-and-build ih-κ (⊑∷ _ ih-tl) =
            ⊑def₂ ⊑□ ih-κ , ih-tl

  -- min□Pos: parallel to min□, on the triple (κ, γ, υ_outer).
  extract-pos-minimal min□Pos s' (κ⊑ , γ⊑ , υ⊑) =
      ⊑ₛLat.⊥ₛ-min (ana-κ s')
    , ⊑ₛLat.⊥ₛ-min (ana-γ s')
    , ⊑ₛLat.⊥ₛ-min (ana-υ_outer s')

  -- minA○: outer Cls = a○ at anaPos τ with ⇐mode τ. The a○ rule couples
  -- the anaPos τ and ⇐mode τ to the same metavariable, so any valid
  -- derivation at this slice position forces s'.υ_outer.↓ ≡ s'.focus.↓
  -- (the only matching rule is a○ itself, since aSub would need a
  -- synPos sub-derivation at ⇐mode, but s○ produces ⇒mode).
  -- Hence υ ⊑ₛ s'.υ_outer follows from s'.focus⊒ : υ ⊑ₛ s'.focus.
  -- κ⊑ : (ana-κ s').↓ ⊑c ○ ; only constructor is ⊑○, forcing (ana-κ s').↓ = ○.
  -- Then ana-valid s' must be a○ (aSub at ⇐mode for ○ context needs s○
  -- which forces ⇒mode — impossible).
  extract-pos-minimal (minA○ υ) s' (⊑○ , γ⊑ , υ⊑)
    with ana-valid s'
  ... | _ , _ , a○ =
          ⊑ₛLat.⊥ₛ-min (ana-κ s')
        , ⊑ₛLat.⊥ₛ-min (ana-γ s')
        , ana-focus⊒ s'
  ... | _ , _ , aSub () _
  -- minASub: outer aSub Cls' con. Requires full dispatch on ana-valid s'
  -- since extract m .κ shape isn't fixed (Cls' is synPos with arbitrary
  -- κ). Each non-aSub ana-rule could in principle fire when extract m .κ
  -- has the matching shape. Punt for now.
  extract-pos-minimal (minASub {Cls' = Cls'} m) s' s'⊑ = {!TODO: minASub — needs dispatch on ana-valid s' across all ana-rule constructors, each handled by either projecting an inner synPos derivation or showing absurdity via mode/shape!}
  -- minAλ: (binder case). Outer aλ: changes anaPos type via eq: τ ⊔ τ₁⇒□
  -- ≡ τ₁'⇒τ₂. Inner Cls' is at anaPos τ₂. s'.υ_outer : ⌊τ⌋, but inner-s' for
  -- Cls' needs ⌊τ₂⌋. Bridging requires using s'.valid's eq to extract a
  -- slice of τ₂ via cod⇒ₛ. Deferred.
  extract-pos-minimal (minAλ: m _ _ _) s' s'⊑ = {!TODO: minAλ: — eq-induced type bridging via cod⇒ₛ!}
  -- minAλ⇒ and related binder cases are deferred (see note at minAλ:).
  extract-pos-minimal (minAλ⇒ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} m) s' s'⊑ = {!TODO: minAλ⇒ binder handling — TODO!}
  extract-pos-minimal (minA&₁ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} m) s' s'⊑ =
    {!TODO: minA&₁ — type mismatch on pair decomposition!}
  extract-pos-minimal (minA&₂ {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {eq = eq} m) s' s'⊑ =
    {!TODO: minA&₂ — type mismatch on pair decomposition!}
  -- minAι₁: outer aι₁ eq Cls'. extract.υ_outer = unmatch+-min eq υ-fst ⊥ where
  -- υ-fst = ana-υ_outer (extract-pos m). Decompose s'.ana-υ_outer's precision
  -- via ⊔-+-⊑ to get τ_a ⊑ τ₁ with s'.ana-υ_outer.↓ ⊔ □+□ ≡ τ_a + τ_b. Unify
  -- with s'-match-eq's components via trans+sym. Build inner-s' for Cls' with
  -- υ_outer = ↑ τ_a⊑ (a slice of τ₁ whose .↓ = τ_a). Apply IH; lift the υ_outer
  -- conclusion back via unmatch+-min-⊑.
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
  -- minAι₂: symmetric to minAι₁ (right component of sum).
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
  -- minAcase₁ (restructured): scrutinee + sibling sliced to □, inner Cls'
  -- lifted to (□ ∷ tlₛ). Pattern-match e/e' precision as ⊑□ to force them
  -- to □; then D' = ⇑□ and eq' = refl pin the binder types to □.
  extract-pos-minimal (minAcase₁ {Cls' = Cls'} m _ _ _) s' (κ⊑ , γ⊑ , υ⊑)
    with s' .ana-κ                          | κ⊑                  | s' .ana-valid
  ... | _ isSlice (⊑case₁ ⊑□ body-prec ⊑□) | ⊑case₁ _ body⊑inner _ | _ , _ , acase₁ ⇑□ refl inner-cls' d₂' =
        let γ⊑-inner : (□ ∷ s' .ana-γ .↓) ⊑a ana-γ (extract-pos m) .↓
            γ⊑-inner = subst ((□ ∷ s' .ana-γ .↓) ⊑a_)
                             (sym (cons-decompₛ (ana-γ (extract-pos m))))
                             (⊑∷ ⊑□ γ⊑)
            inner-s' : AnaPosSlice Cls' _
            inner-s' = record
              { κ       = ↑ body-prec
              ; γ       = ↑ (⊑∷ ⊑□ (s' .ana-γ .proof))
              ; υ_outer = s' .ana-υ_outer
              ; focus   = s' .ana-focus
              ; focus⊒  = s' .ana-focus⊒
              ; valid   = _ , _ , inner-cls'
              }
            ih-κ , ih-γ-raw , ih-υ = extract-pos-minimal m inner-s' (body⊑inner , γ⊑-inner , υ⊑)
            ih-γ-decomp : (hdₛ (ana-γ (extract-pos m)) .↓ ∷ tlₛ (ana-γ (extract-pos m)) .↓) ⊑a (□ ∷ s' .ana-γ .↓)
            ih-γ-decomp = subst (_⊑a (□ ∷ s' .ana-γ .↓))
                                (cons-decompₛ (ana-γ (extract-pos m)))
                                ih-γ-raw
        in invert-and-build ih-κ ih-γ-decomp ih-υ
        where
          invert-and-build : ∀ {a c d e₀ e₂ C'}
            → ana-κ (extract-pos m) .↓ ⊑c C'
            → (hdₛ (ana-γ (extract-pos m)) .↓ ∷ a) ⊑a (c ∷ d)
            → ana-υ_outer (extract-pos m) .↓ ⊑ s' .ana-υ_outer .↓
            → ((case □ of ana-κ (extract-pos m) .↓ ·₁ □) ⊑c (case e₀ of C' ·₁ e₂))
            ∧ (a ⊑a d)
            ∧ (ana-υ_outer (extract-pos m) .↓ ⊑ s' .ana-υ_outer .↓)
          invert-and-build ih-κ (⊑∷ _ ih-tl) ih-υ =
            ⊑case₁ ⊑□ ih-κ ⊑□ , ih-tl , ih-υ
  -- aSub branch: s'.valid = aSub (scase₁ ⇑□ refl inner-cls' _ con-scase) c-orig.
  -- Inner-cls' is at synPos τ₁'; we wrap with aSub using consistency derived from
  -- c-orig + con-scase via ~-⊑-down.
  ... | _ isSlice (⊑case₁ ⊑□ body-prec ⊑□) | ⊑case₁ _ body⊑inner _ | _ , _ , aSub (scase₁ ⇑□ refl inner-cls' _ con-scase) c-orig =
        let con-derived = ~-⊑-down c-orig (⊑.refl {A = Typ}) (~.⊔-ub₁ con-scase)
            γ⊑-inner : (□ ∷ s' .ana-γ .↓) ⊑a ana-γ (extract-pos m) .↓
            γ⊑-inner = subst ((□ ∷ s' .ana-γ .↓) ⊑a_)
                             (sym (cons-decompₛ (ana-γ (extract-pos m))))
                             (⊑∷ ⊑□ γ⊑)
            inner-s' : AnaPosSlice Cls' _
            inner-s' = record
              { κ       = ↑ body-prec
              ; γ       = ↑ (⊑∷ ⊑□ (s' .ana-γ .proof))
              ; υ_outer = s' .ana-υ_outer
              ; focus   = s' .ana-focus
              ; focus⊒  = s' .ana-focus⊒
              ; valid   = _ , _ , aSub inner-cls' con-derived
              }
            ih-κ , ih-γ-raw , ih-υ = extract-pos-minimal m inner-s' (body⊑inner , γ⊑-inner , υ⊑)
            ih-γ-decomp : (hdₛ (ana-γ (extract-pos m)) .↓ ∷ tlₛ (ana-γ (extract-pos m)) .↓) ⊑a (□ ∷ s' .ana-γ .↓)
            ih-γ-decomp = subst (_⊑a (□ ∷ s' .ana-γ .↓))
                                (cons-decompₛ (ana-γ (extract-pos m)))
                                ih-γ-raw
        in invert-and-build ih-κ ih-γ-decomp ih-υ
        where
          invert-and-build : ∀ {a c d e₀ e₂ C'}
            → ana-κ (extract-pos m) .↓ ⊑c C'
            → (hdₛ (ana-γ (extract-pos m)) .↓ ∷ a) ⊑a (c ∷ d)
            → ana-υ_outer (extract-pos m) .↓ ⊑ s' .ana-υ_outer .↓
            → ((case □ of ana-κ (extract-pos m) .↓ ·₁ □) ⊑c (case e₀ of C' ·₁ e₂))
            ∧ (a ⊑a d)
            ∧ (ana-υ_outer (extract-pos m) .↓ ⊑ s' .ana-υ_outer .↓)
          invert-and-build ih-κ (⊑∷ _ ih-tl) ih-υ =
            ⊑case₁ ⊑□ ih-κ ⊑□ , ih-tl , ih-υ

  -- minAcase₂ (symmetric).
  extract-pos-minimal (minAcase₂ {Cls' = Cls'} m _ _ _) s' (κ⊑ , γ⊑ , υ⊑)
    with s' .ana-κ                          | κ⊑                  | s' .ana-valid
  ... | _ isSlice (⊑case₂ ⊑□ ⊑□ body-prec) | ⊑case₂ _ _ body⊑inner | _ , _ , acase₂ ⇑□ refl d₁' inner-cls' =
        let γ⊑-inner : (□ ∷ s' .ana-γ .↓) ⊑a ana-γ (extract-pos m) .↓
            γ⊑-inner = subst ((□ ∷ s' .ana-γ .↓) ⊑a_)
                             (sym (cons-decompₛ (ana-γ (extract-pos m))))
                             (⊑∷ ⊑□ γ⊑)
            inner-s' : AnaPosSlice Cls' _
            inner-s' = record
              { κ       = ↑ body-prec
              ; γ       = ↑ (⊑∷ ⊑□ (s' .ana-γ .proof))
              ; υ_outer = s' .ana-υ_outer
              ; focus   = s' .ana-focus
              ; focus⊒  = s' .ana-focus⊒
              ; valid   = _ , _ , inner-cls'
              }
            ih-κ , ih-γ-raw , ih-υ = extract-pos-minimal m inner-s' (body⊑inner , γ⊑-inner , υ⊑)
            ih-γ-decomp : (hdₛ (ana-γ (extract-pos m)) .↓ ∷ tlₛ (ana-γ (extract-pos m)) .↓) ⊑a (□ ∷ s' .ana-γ .↓)
            ih-γ-decomp = subst (_⊑a (□ ∷ s' .ana-γ .↓))
                                (cons-decompₛ (ana-γ (extract-pos m)))
                                ih-γ-raw
        in invert-and-build ih-κ ih-γ-decomp ih-υ
        where
          invert-and-build : ∀ {a c d e₀ e₁ C'}
            → ana-κ (extract-pos m) .↓ ⊑c C'
            → (hdₛ (ana-γ (extract-pos m)) .↓ ∷ a) ⊑a (c ∷ d)
            → ana-υ_outer (extract-pos m) .↓ ⊑ s' .ana-υ_outer .↓
            → ((case □ of₂ □ · ana-κ (extract-pos m) .↓) ⊑c (case e₀ of₂ e₁ · C'))
            ∧ (a ⊑a d)
            ∧ (ana-υ_outer (extract-pos m) .↓ ⊑ s' .ana-υ_outer .↓)
          invert-and-build ih-κ (⊑∷ _ ih-tl) ih-υ =
            ⊑case₂ ⊑□ ⊑□ ih-κ , ih-tl , ih-υ
  -- aSub branch (symmetric to minAcase₁ aSub branch).
  ... | _ isSlice (⊑case₂ ⊑□ ⊑□ body-prec) | ⊑case₂ _ _ body⊑inner | _ , _ , aSub (scase₂ ⇑□ refl _ inner-cls' con-scase) c-orig =
        let con-derived = ~-⊑-down c-orig (⊑.refl {A = Typ}) (~.⊔-ub₂ con-scase)
            γ⊑-inner : (□ ∷ s' .ana-γ .↓) ⊑a ana-γ (extract-pos m) .↓
            γ⊑-inner = subst ((□ ∷ s' .ana-γ .↓) ⊑a_)
                             (sym (cons-decompₛ (ana-γ (extract-pos m))))
                             (⊑∷ ⊑□ γ⊑)
            inner-s' : AnaPosSlice Cls' _
            inner-s' = record
              { κ       = ↑ body-prec
              ; γ       = ↑ (⊑∷ ⊑□ (s' .ana-γ .proof))
              ; υ_outer = s' .ana-υ_outer
              ; focus   = s' .ana-focus
              ; focus⊒  = s' .ana-focus⊒
              ; valid   = _ , _ , aSub inner-cls' con-derived
              }
            ih-κ , ih-γ-raw , ih-υ = extract-pos-minimal m inner-s' (body⊑inner , γ⊑-inner , υ⊑)
            ih-γ-decomp : (hdₛ (ana-γ (extract-pos m)) .↓ ∷ tlₛ (ana-γ (extract-pos m)) .↓) ⊑a (□ ∷ s' .ana-γ .↓)
            ih-γ-decomp = subst (_⊑a (□ ∷ s' .ana-γ .↓))
                                (cons-decompₛ (ana-γ (extract-pos m)))
                                ih-γ-raw
        in invert-and-build ih-κ ih-γ-decomp ih-υ
        where
          invert-and-build : ∀ {a c d e₀ e₁ C'}
            → ana-κ (extract-pos m) .↓ ⊑c C'
            → (hdₛ (ana-γ (extract-pos m)) .↓ ∷ a) ⊑a (c ∷ d)
            → ana-υ_outer (extract-pos m) .↓ ⊑ s' .ana-υ_outer .↓
            → ((case □ of₂ □ · ana-κ (extract-pos m) .↓) ⊑c (case e₀ of₂ e₁ · C'))
            ∧ (a ⊑a d)
            ∧ (ana-υ_outer (extract-pos m) .↓ ⊑ s' .ana-υ_outer .↓)
          invert-and-build ih-κ (⊑∷ _ ih-tl) ih-υ =
            ⊑case₂ ⊑□ ⊑□ ih-κ , ih-tl , ih-υ
  -- minAdef₁: outer Cls = adef₁ Cls' d₂ at anaPos τ. Cross-mutual to
  -- extract-minimal on the synPos inner. Body exp slice is □e (minimal);
  -- υ_outer = ⊥ₛ. Two possible derivations for s'.valid: adef₁ (the
  -- natural one) and aSub of sdef₁ (subsumption lifting).
  extract-pos-minimal (minAdef₁ {Cls' = Cls'} m) s' (κ⊑ , γ⊑ , υ⊑)
    with s' .ana-κ                | κ⊑                  | s' .ana-valid
  ... | _ isSlice (⊑def₁ s-proof _) | ⊑def₁ κ-body⊑inner _ | _ , _ , adef₁ inner-cls' _ =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .ana-γ ; type = _ isSlice τ⊑
                ; focus = s' .ana-focus ; focus⊒ = s' .ana-focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑def₁ (proj₁ ih) ⊑□ , proj₂ ih , ⊑ₛLat.⊥ₛ-min (ana-υ_outer s')
  ... | _ isSlice (⊑def₁ s-proof _) | ⊑def₁ κ-body⊑inner _ | _ , _ , aSub (sdef₁ inner-cls' _) _ =
          let γ⊑Γ = ⊑.trans {Assms} γ⊑ (extract m .γ .proof)
              τ⊑  = syn-cls-precision γ⊑Γ s-proof inner-cls' Cls'
              inner-s' : AnaSlice Cls' _
              inner-s' = record
                { κ = _ isSlice s-proof ; γ = s' .ana-γ ; type = _ isSlice τ⊑
                ; focus = s' .ana-focus ; focus⊒ = s' .ana-focus⊒
                ; valid = _ , _ , inner-cls' }
              ih = extract-minimal m inner-s' (κ-body⊑inner , γ⊑)
          in ⊑def₁ (proj₁ ih) ⊑□ , proj₂ ih , ⊑ₛLat.⊥ₛ-min (ana-υ_outer s')
  -- minAdef₂ (restructured): same pattern as minSdef₂ but at anaPos.
  -- def-e sliced to □, body Cls' lifted to (□ ∷ tlₛ). υ_outer forwarded
  -- from inner. Two s'.valid cases: adef₂ (natural) and aSub(sdef₂).
  extract-pos-minimal (minAdef₂ {Cls' = Cls'} m _ _ _) s' (κ⊑ , γ⊑ , υ⊑)
    with s' .ana-κ                          | κ⊑                       | s' .ana-valid
  ... | _ isSlice (⊑def₂ e-prec body-prec) | ⊑def₂ _ body⊑inner | _ , _ , adef₂ ⇑□ inner-cls' =
        let γ⊑-inner : (□ ∷ s' .ana-γ .↓) ⊑a ana-γ (extract-pos m) .↓
            γ⊑-inner = subst ((□ ∷ s' .ana-γ .↓) ⊑a_)
                             (sym (cons-decompₛ (ana-γ (extract-pos m))))
                             (⊑∷ ⊑□ γ⊑)
            inner-s' : AnaPosSlice Cls' _
            inner-s' = record
              { κ       = ↑ body-prec
              ; γ       = ↑ (⊑∷ ⊑□ (s' .ana-γ .proof))
              ; υ_outer = s' .ana-υ_outer
              ; focus   = s' .ana-focus
              ; focus⊒  = s' .ana-focus⊒
              ; valid   = _ , _ , inner-cls'
              }
            ih-κ , ih-γ-raw , ih-υ = extract-pos-minimal m inner-s' (body⊑inner , γ⊑-inner , υ⊑)
            ih-γ-decomp : (hdₛ (ana-γ (extract-pos m)) .↓ ∷ tlₛ (ana-γ (extract-pos m)) .↓) ⊑a (□ ∷ s' .ana-γ .↓)
            ih-γ-decomp = subst (_⊑a (□ ∷ s' .ana-γ .↓))
                                (cons-decompₛ (ana-γ (extract-pos m)))
                                ih-γ-raw
        in invert-and-build ih-κ ih-γ-decomp ih-υ
        where
          invert-and-build : ∀ {a c d e' C'}
            → ana-κ (extract-pos m) .↓ ⊑c C'
            → (hdₛ (ana-γ (extract-pos m)) .↓ ∷ a) ⊑a (c ∷ d)
            → ana-υ_outer (extract-pos m) .↓ ⊑ s' .ana-υ_outer .↓
            → ((def □ ⊢₂ ana-κ (extract-pos m) .↓) ⊑c (def e' ⊢₂ C'))
            ∧ (a ⊑a d)
            ∧ (ana-υ_outer (extract-pos m) .↓ ⊑ s' .ana-υ_outer .↓)
          invert-and-build ih-κ (⊑∷ _ ih-tl) ih-υ =
            ⊑def₂ ⊑□ ih-κ , ih-tl , ih-υ
  ... | _ isSlice (⊑def₂ e-prec body-prec) | ⊑def₂ _ body⊑inner | _ , _ , aSub (sdef₂ ⇑□ inner-cls') con-some =
        let γ⊑-inner : (□ ∷ s' .ana-γ .↓) ⊑a ana-γ (extract-pos m) .↓
            γ⊑-inner = subst ((□ ∷ s' .ana-γ .↓) ⊑a_)
                             (sym (cons-decompₛ (ana-γ (extract-pos m))))
                             (⊑∷ ⊑□ γ⊑)
            inner-s' : AnaPosSlice Cls' _
            inner-s' = record
              { κ       = ↑ body-prec
              ; γ       = ↑ (⊑∷ ⊑□ (s' .ana-γ .proof))
              ; υ_outer = s' .ana-υ_outer
              ; focus   = s' .ana-focus
              ; focus⊒  = s' .ana-focus⊒
              ; valid   = _ , _ , aSub inner-cls' con-some
              }
            ih-κ , ih-γ-raw , ih-υ = extract-pos-minimal m inner-s' (body⊑inner , γ⊑-inner , υ⊑)
            ih-γ-decomp : (hdₛ (ana-γ (extract-pos m)) .↓ ∷ tlₛ (ana-γ (extract-pos m)) .↓) ⊑a (□ ∷ s' .ana-γ .↓)
            ih-γ-decomp = subst (_⊑a (□ ∷ s' .ana-γ .↓))
                                (cons-decompₛ (ana-γ (extract-pos m)))
                                ih-γ-raw
        in invert-and-build ih-κ ih-γ-decomp ih-υ
        where
          invert-and-build : ∀ {a c d e' C'}
            → ana-κ (extract-pos m) .↓ ⊑c C'
            → (hdₛ (ana-γ (extract-pos m)) .↓ ∷ a) ⊑a (c ∷ d)
            → ana-υ_outer (extract-pos m) .↓ ⊑ s' .ana-υ_outer .↓
            → ((def □ ⊢₂ ana-κ (extract-pos m) .↓) ⊑c (def e' ⊢₂ C'))
            ∧ (a ⊑a d)
            ∧ (ana-υ_outer (extract-pos m) .↓ ⊑ s' .ana-υ_outer .↓)
          invert-and-build ih-κ (⊑∷ _ ih-tl) ih-υ =
            ⊑def₂ ⊑□ ih-κ , ih-tl , ih-υ
