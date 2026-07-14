open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Core
open import Core.Typ.Consistency using (~?₂)
open import Semantics.Statics
open import Semantics.Graduality using
  (mode-⊑; ⇒mode-⊑; static-gradual-syn; syn-precision)
open import Slicing.Synthesis.Synthesis using (SynSlice_◂_; IsMinimal)
import Slicing.Synthesis.Synthesis as SS
open import Slicing.Synthesis.FixedAssmsSynthesis using
  (FixedAssmsSynSlice; static-gradual-syn-exp)
import Slicing.Synthesis.FixedAssmsCalc as FC
open import Slicing.Synthesis.FixedAssmsCalc using (_◂_⤳_⇑_⊣_)
open import Slicing.Analysis.AnaSlicing using
  (ana-cls-to-syn; syn-cls-precision)
open import Slicing.Full.Full
open import Slicing.Full.FullSliceCalc

-- Soundness and minimality of the full-slice calculation judgment.
module Slicing.Full.FullSlicing where

mutual
  extract : ∀ {n Γ₀ C n_f Γ e τ τₚ}
              {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
              {D : n_f , Γ ⊢ e ⇑ τ}
              {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
          → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
          → SynTypeSlice Cls D u

  extract (minS○ {D = D} {u = u} {σ = σ} {γ = γ} c)
    with FC.extract-ctx c
  ... | φ , d , u⊑φ = record
    { κ           = ○ₖ
    ; γ           = γ
    ; outer       = φ
    ; focus-slice = record
        { progₛ = γ ,ₛ σ ; type = φ ; syn = d ; valid = u⊑φ }
    ; powered     = _ , γ , φ ,
        ⊑.refl {A = Assms} , s○ , d
    }

  extract-pos : ∀ {n Γ₀ C n_f Γ e τ τₚ}
                  {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                  {D : n_f , Γ ⊢ e ⇑ τ}
                  {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋}
                  {uₒ : ⌊ τₚ ⌋} {γ : ⌊ Γ₀ ⌋}
              → Cls , D ◂ u ⤳ κ ∣ σ ⇓ uₒ ⊣ γ
              → SynPosTypeSlice Cls D u

  extract-pos (minASub c) with extract c
  ... | s with s .powered
  ... | n' , Γ' , φ' , focus⊑ , cls , d = record
    { pos-κ           = s .κ
    ; pos-γ           = s .γ
    ; pos-outer       = ⊥ₛ
    ; pos-focus-slice = s .focus-slice
    ; pos-powered     = n' , Γ' , φ' , focus⊑ , aSub cls ~?₂ , d
    }

-- FixedAssmsCalc minimises the focused term under the maximal original
-- assumptions.  Consequently every valid focused SynSlice below its output
-- has exactly the same expression component, regardless of which live
-- assumptions that rival SynSlice selected.
focus-exp-eq : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ}
                 {u : ⌊ τ ⌋} {σ : ⌊ e ⌋} {ψ : ⌊ τ ⌋} {γ : ⌊ Γ ⌋}
             → (c : D ◂ u ⤳ σ ⇑ ψ ⊣ γ)
             → (s : SynSlice D ◂ u)
             → SS._↓σₛ s ⊑ₛ σ
             → σ .↓ ≡ SS._↓σ s
focus-exp-eq {D = D} c s s⊑σ
  with static-gradual-syn-exp D (SS._↓σₛ s)
... | ψ' , d'
  with FC.extract-minimal c
         (record
           { expₛ = SS._↓σₛ s
           ; type = ψ'
           ; syn = d'
           ; valid = ⊑.trans {A = Typ} (SS.valid s)
               (syn-precision (SS._↓γ⊑ s) (⊑.refl {A = Exp}) d' (SS.syn s))
           })
         (subst (SS._↓σ s ⊑e_)
                (sym (cong (λ x → x .↓) (FC.extract-σ c))) s⊑σ)
... | eq = trans (sym (cong (λ x → x .↓) (FC.extract-σ c))) eq

extract-least : ∀ {n Γ₀ C n_f Γ e τ τₚ}
                  {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                  {D : n_f , Γ ⊢ e ⇑ τ}
                  {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
              → (c : Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ)
              → (r : SynTypeSlice Cls D u)
              → r ⊑ extract c
              → extract c ⊑ r
extract-least (minS○ {σ = σ} {γ = γ} c) r ((κr⊑ , γr⊑) , σr⊑)
  with r .powered
... | _ , Γᶠ , φᶠ , focus⊑ , s○ , dᶠ =
  let
    u⊑φᶠ = ⊑.trans {A = Typ} (SS.valid (r .focus-slice))
      (syn-precision focus⊑ (⊑.refl {A = Exp}) dᶠ
        (SS.syn (r .focus-slice)))
    eqσ = focus-exp-eq c (r .focus-slice) σr⊑
    dσ = subst (λ x → _ , Γᶠ .↓ ⊢ x ⇑ φᶠ .↓) (sym eqσ) dᶠ
    γ⊑γr = FC.extract-ctx-min c dσ u⊑φᶠ (Γᶠ .proof)
  in (⊑○ , γ⊑γr) , ⊑.reflexive {A = Exp} eqσ

extract-minimal : ∀ {n Γ₀ C n_f Γ e τ τₚ}
                    {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                    {D : n_f , Γ ⊢ e ⇑ τ}
                    {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
                → (c : Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ)
                → IsMinimal (extract c)
extract-minimal c r ((κr⊑ , γr⊑) , σr⊑)
  with extract-least c r ((κr⊑ , γr⊑) , σr⊑)
... | (κ⊑r , γ⊑r) , σ⊑r =
  (⊑.antisym {A = Ctx} κ⊑r κr⊑ ,
   ⊑.antisym {A = Assms} γ⊑r γr⊑) ,
  ⊑.antisym {A = Exp} σ⊑r σr⊑

extract-pos-least : ∀ {n Γ₀ C n_f Γ e τ τₚ}
                      {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                      {D : n_f , Γ ⊢ e ⇑ τ}
                      {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋}
                      {uₒ : ⌊ τₚ ⌋} {γ : ⌊ Γ₀ ⌋}
                  → (c : Cls , D ◂ u ⤳ κ ∣ σ ⇓ uₒ ⊣ γ)
                  → (r : SynPosTypeSlice Cls D u)
                  → r ⊑ extract-pos c
                  → extract-pos c ⊑ r
extract-pos-least (minASub {Cls = Cls} {D = D} c) r
    (((κr⊑ , γr⊑) , σr⊑) , ur⊑)
  with r .pos-powered
... | n' , Γᶠ , φᶠ , focus⊑ , clsᵃ , dᶠ
  with ana-cls-to-syn (r .pos-γ .proof) (r .pos-κ .proof)
         (⇒mode-⊑ (φᶠ .proof)) Cls clsᵃ
... | ψ , clsˢ
  with syn-cls-precision (r .pos-γ .proof) (r .pos-κ .proof)
         (⇒mode-⊑ (φᶠ .proof)) clsˢ Cls
... | ψ⊑
  with extract-least c
         (record
           { κ = r .pos-κ
           ; γ = r .pos-γ
           ; outer = ↑ ψ⊑
           ; focus-slice = r .pos-focus-slice
           ; powered = n' , Γᶠ , φᶠ , focus⊑ , clsˢ , dᶠ
           })
         ((κr⊑ , γr⊑) , σr⊑)
... | (κ⊑r , γ⊑r) , σ⊑r =
  ((κ⊑r , γ⊑r) , σ⊑r) , ⊑ₛLat.⊥ₛ-min {A = Typ} (r .pos-outer)

extract-pos-minimal : ∀ {n Γ₀ C n_f Γ e τ τₚ}
                        {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                        {D : n_f , Γ ⊢ e ⇑ τ}
                        {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋}
                        {uₒ : ⌊ τₚ ⌋} {γ : ⌊ Γ₀ ⌋}
                    → (c : Cls , D ◂ u ⤳ κ ∣ σ ⇓ uₒ ⊣ γ)
                    → IsMinimal (extract-pos c)
extract-pos-minimal c r (((κr⊑ , γr⊑) , σr⊑) , ur⊑)
  with extract-pos-least c r (((κr⊑ , γr⊑) , σr⊑) , ur⊑)
... | ((κ⊑r , γ⊑r) , σ⊑r) , u⊑r =
  ((⊑.antisym {A = Ctx} κ⊑r κr⊑ ,
    ⊑.antisym {A = Assms} γ⊑r γr⊑) ,
   ⊑.antisym {A = Exp} σ⊑r σr⊑) ,
  ⊑.antisym {A = Typ} u⊑r ur⊑

extract-min : ∀ {n Γ₀ C n_f Γ e τ τₚ}
                {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
            → MinSynTypeSlice Cls D u
extract-min c = extract c , extract-minimal c

extract-pos-min : ∀ {n Γ₀ C n_f Γ e τ τₚ}
                    {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                    {D : n_f , Γ ⊢ e ⇑ τ}
                    {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋}
                    {uₒ : ⌊ τₚ ⌋} {γ : ⌊ Γ₀ ⌋}
                → Cls , D ◂ u ⤳ κ ∣ σ ⇓ uₒ ⊣ γ
                → MinSynPosTypeSlice Cls D u
extract-pos-min c = extract-pos c , extract-pos-minimal c
