open import Data.Nat using (ℕ; zero)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Core
open import Core.Typ.Lift using
  (match⇒ₛ; dom⇒ₛ; cod⇒ₛ; match×ₛ; fst×ₛ'; snd×ₛ;
   match+ₛ; fst+ₛ'; snd+ₛ'; match∀ₛ; body∀ₛ;
   unmatch⇒-min-cov; unmatch×-min-cov; unmatch+-min-cov;
   unmatch⇒-min-least; unmatch×-min-least; unmatch+-min-least;
   unmatch⇒-min-□; unmatch×-min-□; unmatch+-min-□;
   ann-⇒-plain)
open import Core.Typ.Properties using
  (sub-⊑; ⊔-⇒-⊑; ⊔-×-⊑; ⊔-+-⊑; ⊔-mono-⊑; ⊔-ann-⇒-⊑)
open import Core.Typ.Precision using (~-⊑-down)
open import Core.Typ.WellFormedness using (wf□; wf-⊑)
open import Core.Typ.Consistency using (~?₁; ~?₂)
open import Core.Assms.Precision using (shiftΓ-⊑; unshiftΓ-⊑)
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

private
  ⇒-inj-fst : ∀ {a b c d : Typ} → a ⇒ b ≡ c ⇒ d → a ≡ c
  ⇒-inj-fst refl = refl

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

  ⊑□-inv : ∀ {x : Typ} → x ⊑t □ → x ≡ □
  ⊑□-inv ⊑□ = refl

mutual
  focus : ∀ {n Γ₀ C n_f Γ e τ τₚ}
            {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
            {D : n_f , Γ ⊢ e ⇑ τ}
            {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
        → Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ
        → SynSlice D ◂ u

  focus (minS○ {σ = σ} {γ = γ} c) with FC.extract-ctx c
  ... | φ , d , u⊑φ = record
    { progₛ = γ ,ₛ σ ; type = φ ; syn = d ; valid = u⊑φ }
  focus (minSι₁ c) = focus c
  focus (minSι₂ c) = focus c
  focus (minS&₁ c) = focus c
  focus (minS&₂ c) = focus c
  focus (minSπ₁ c) = focus c
  focus (minSπ₂ c) = focus c
  focus (minS∘₁ c) = focus c
  focus (minS<>₁ c) = focus c
  focus (minS∘₂ c f) = focus-pos c
  focus (minSλ: c) = focus c
  focus (minSΛ c) = focus c
  focus (minSdef₁ c) = focus c
  focus (minSdef₂ c f) = focus c
  focus (minScase₀ c) = focus c
  focus (minScase₁ c f) = focus c
  focus (minScase₂ c f) = focus c

  focus-pos : ∀ {n Γ₀ C n_f Γ e τ τₚ}
                {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                {D : n_f , Γ ⊢ e ⇑ τ}
                {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋}
                {uₒ : ⌊ τₚ ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls , D ◂ u ⤳ κ ∣ σ ⇓ uₒ ⊣ γ
            → SynSlice D ◂ u

  focus-pos (minASub c) = focus c
  focus-pos (minAι₁ c) = focus-pos c
  focus-pos (minAι₂ c) = focus-pos c
  focus-pos (minA&₁ c) = focus-pos c
  focus-pos (minA&₂ c) = focus-pos c
  focus-pos (minAλ⇒ c) = focus-pos c
  focus-pos (minAλ: c) = focus-pos c
  focus-pos (minAdef₁ c) = focus c
  focus-pos (minAdef₂ c f) = focus-pos c
  focus-pos (minAcase₀ c) = focus c
  focus-pos (minAcase₁ c f) = focus-pos c
  focus-pos (minAcase₂ c f) = focus-pos c

mutual
  focus-σ : ∀ {n Γ₀ C n_f Γ e τ τₚ}
              {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
              {D : n_f , Γ ⊢ e ⇑ τ}
              {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
          → (c : Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ)
          → SS._↓σ (focus c) ≡ σ .↓
  focus-σ (minS○ c) with FC.extract-ctx c
  ... | _ , _ , _ = refl
  focus-σ (minSι₁ c) = focus-σ c
  focus-σ (minSι₂ c) = focus-σ c
  focus-σ (minS&₁ c) = focus-σ c
  focus-σ (minS&₂ c) = focus-σ c
  focus-σ (minSπ₁ c) = focus-σ c
  focus-σ (minSπ₂ c) = focus-σ c
  focus-σ (minS∘₁ c) = focus-σ c
  focus-σ (minS<>₁ c) = focus-σ c
  focus-σ (minS∘₂ c f) = focus-pos-σ c
  focus-σ (minSλ: c) = focus-σ c
  focus-σ (minSΛ c) = focus-σ c
  focus-σ (minSdef₁ c) = focus-σ c
  focus-σ (minSdef₂ c f) = focus-σ c
  focus-σ (minScase₀ c) = focus-σ c
  focus-σ (minScase₁ c f) = focus-σ c
  focus-σ (minScase₂ c f) = focus-σ c

  focus-pos-σ : ∀ {n Γ₀ C n_f Γ e τ τₚ}
                  {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                  {D : n_f , Γ ⊢ e ⇑ τ}
                  {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋}
                  {uₒ : ⌊ τₚ ⌋} {γ : ⌊ Γ₀ ⌋}
              → (c : Cls , D ◂ u ⤳ κ ∣ σ ⇓ uₒ ⊣ γ)
              → SS._↓σ (focus-pos c) ≡ σ .↓
  focus-pos-σ (minASub c) = focus-σ c
  focus-pos-σ (minAι₁ c) = focus-pos-σ c
  focus-pos-σ (minAι₂ c) = focus-pos-σ c
  focus-pos-σ (minA&₁ c) = focus-pos-σ c
  focus-pos-σ (minA&₂ c) = focus-pos-σ c
  focus-pos-σ (minAλ⇒ c) = focus-pos-σ c
  focus-pos-σ (minAλ: c) = focus-pos-σ c
  focus-pos-σ (minAdef₁ c) = focus-σ c
  focus-pos-σ (minAdef₂ c f) = focus-pos-σ c
  focus-pos-σ (minAcase₀ c) = focus-σ c
  focus-pos-σ (minAcase₁ c f) = focus-pos-σ c
  focus-pos-σ (minAcase₂ c f) = focus-pos-σ c

-- A calculation can be replayed under any assumptions above its calculated
-- external assumptions.  At an analysis position it can likewise be replayed
-- at any outer demand above the one it calculated.  These bounded lifts keep
-- the focused SynSlice fixed while rebuilding the context-powered typing.
mutual
  lift-syn : ∀ {n Γ₀ C n_f Γ e τ τₚ}
               {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
               {D : n_f , Γ ⊢ e ⇑ τ}
               {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
           → (c : Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ)
           → (Γ'' : ⌊ Γ₀ ⌋) → γ ⊑ₛ Γ''
           → Σ[ ψₚ ∈ ⌊ τₚ ⌋ ] Σ[ n'' ∈ ℕ ]
             Σ[ Γᶠ ∈ ⌊ Γ ⌋ ] Σ[ φᶠ ∈ ⌊ τ ⌋ ]
               (SS._↓γₛ (focus c) ⊑ₛ Γᶠ) ∧
               (n , Γ'' .↓ ⊢ κ .↓ at synPos (ψₚ .↓) ▷ n'' , Γᶠ .↓
                  [ ⇒mode (φᶠ .↓) ]) ∧
               (n'' , Γᶠ .↓ ⊢ SS._↓σ (focus c) ⇑ φᶠ .↓)

  lift-pos : ∀ {n Γ₀ C n_f Γ e τ τₚ}
               {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
               {D : n_f , Γ ⊢ e ⇑ τ}
               {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋}
               {uₒ : ⌊ τₚ ⌋} {γ : ⌊ Γ₀ ⌋}
           → (c : Cls , D ◂ u ⤳ κ ∣ σ ⇓ uₒ ⊣ γ)
           → (Γ'' : ⌊ Γ₀ ⌋) → γ ⊑ₛ Γ''
           → (uₚ : ⌊ τₚ ⌋) → uₒ ⊑ₛ uₚ
           → Σ[ n'' ∈ ℕ ] Σ[ Γᶠ ∈ ⌊ Γ ⌋ ] Σ[ φᶠ ∈ ⌊ τ ⌋ ]
               (SS._↓γₛ (focus-pos c) ⊑ₛ Γᶠ) ∧
               (n , Γ'' .↓ ⊢ κ .↓ at anaPos (uₚ .↓) ▷ n'' , Γᶠ .↓
                  [ ⇒mode (φᶠ .↓) ]) ∧
               (n'' , Γᶠ .↓ ⊢ SS._↓σ (focus-pos c) ⇑ φᶠ .↓)

  lift-syn (minS○ {D = D} {σ = σ} c) Γ'' γ⊑
    with FC.extract-ctx c | static-gradual-syn (Γ'' .proof) (σ .proof) D
  ... | φγ , dγ , u⊑φγ | φ' , d' , φ'⊑ =
    ↑ φ'⊑ , _ , Γ'' , ↑ φ'⊑ , γ⊑ , s○ , d'

  lift-syn (minSι₁ c) Γ'' γ⊑ with lift-syn c Γ'' γ⊑
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    ψₚ +ₛ ⊥ₛ , n' , Γᶠ , φᶠ , focus⊑ , sι₁ cls , d

  lift-syn (minSι₂ c) Γ'' γ⊑ with lift-syn c Γ'' γ⊑
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    ⊥ₛ +ₛ ψₚ , n' , Γᶠ , φᶠ , focus⊑ , sι₂ cls , d

  lift-syn (minS&₁ c) Γ'' γ⊑ with lift-syn c Γ'' γ⊑
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    ψₚ ×ₛ ⊥ₛ , n' , Γᶠ , φᶠ , focus⊑ , s&₁ cls ⇑□ , d

  lift-syn (minS&₂ c) Γ'' γ⊑ with lift-syn c Γ'' γ⊑
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    ⊥ₛ ×ₛ ψₚ , n' , Γᶠ , φᶠ , focus⊑ , s&₂ ⇑□ cls , d

  lift-syn (minSπ₁ {eq = eq} c) Γ'' γ⊑ with lift-syn c Γ'' γ⊑
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    fst×ₛ' ψₚ eq , n' , Γᶠ , φᶠ , focus⊑ ,
    sπ₁ cls (match×ₛ ψₚ eq) , d

  lift-syn (minSπ₂ {eq = eq} c) Γ'' γ⊑ with lift-syn c Γ'' γ⊑
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    snd×ₛ ψₚ eq , n' , Γᶠ , φᶠ , focus⊑ ,
    sπ₂ cls (match×ₛ ψₚ eq) , d

  lift-syn (minS∘₁ {eq = eq} c) Γ'' γ⊑ with lift-syn c Γ'' γ⊑
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    cod⇒ₛ ψₚ eq , n' , Γᶠ , φᶠ , focus⊑ ,
    s∘₁ cls (match⇒ₛ ψₚ eq) (⇓Sub ⇑□ ~?₁) , d

  lift-syn (minS<>₁ {eq = eq} c) Γ'' γ⊑ with lift-syn c Γ'' γ⊑
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    ↑ (sub-⊑ zero ⊑□ (body∀ₛ ψₚ eq .proof)) ,
    n' , Γᶠ , φᶠ , focus⊑ , s<>₁ cls (match∀ₛ ψₚ eq) wf□ , d

  lift-syn (minSλ: {wf = wf} {φ₁ = φ₁} c) Γ'' γ⊑
    with lift-syn c (φ₁ ∷ₛ Γ'') (⊑∷ (⊑.refl {A = Typ}) γ⊑)
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    φ₁ ⇒ₛ ψₚ , n' , Γᶠ , φᶠ , focus⊑ ,
    sλ: (wf-⊑ wf (φ₁ .proof)) cls , d

  lift-syn
      (minS∘₂ {τ₀ = τ₀} {D₁ = D₁} {eq = eq} {uₒ = uₒ}
               {γ' = γ'} {σ₁ = σ₁} {γ₁ = γ₁} c f)
      Γ'' γ⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ₁ .proof) D₁
  ... | ψγ , dγ , q⊑ψγ | ψ' , d' , ψ'⊑τ₀
    with unmatch⇒-min-cov τ₀ eq uₒ ⊥ₛ
           (⊑.trans {A = Typ} q⊑ψγ
             (syn-precision
               (⊑.trans {A = Assms}
                 (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₁ γ') γ⊑)
               (⊑.refl {A = Exp}) d' dγ))
           (match⇒ₛ (_ isSlice ψ'⊑τ₀) eq)
  ... | uₒ⊑dom , _
    with lift-pos c Γ''
           (⊑.trans {A = Assms}
             (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₁ γ') γ⊑)
           (dom⇒ₛ (_ isSlice ψ'⊑τ₀) eq) uₒ⊑dom
  ... | n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    cod⇒ₛ (_ isSlice ψ'⊑τ₀) eq , n' , Γᶠ , φᶠ , focus⊑ ,
    s∘₂ d' (match⇒ₛ (_ isSlice ψ'⊑τ₀) eq) cls , d

  lift-syn (minSΛ {γ' = γ'} c) Γ'' γ⊑
    with lift-syn c (shiftΓₛ Γ'')
           (⊑.trans {A = Assms}
             (⊑.reflexive {A = Assms}
               (sym (shift-unshiftΓ (γ' .↓) (γ' .proof))))
             (shiftΓ-⊑ γ⊑))
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    ∀·ₛ ψₚ , n' , Γᶠ , φᶠ , focus⊑ , sΛ cls , d

  lift-syn (minSdef₁ c) Γ'' γ⊑ with lift-syn c Γ'' γ⊑
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    ⊥ₛ , n' , Γᶠ , φᶠ , focus⊑ , sdef₁ cls ⇑□ , d

  lift-syn
      (minSdef₂ {τ' = τ'} {D₁ = D₁} {φ = φ} {γ₂ = γ₂}
                 {σ₁ = σ₁} {γ₁ = γ₁} c f)
      Γ'' γ⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ₁ .proof) D₁
  ... | ψγ , dγ , φ⊑ψγ | ψ' , d' , ψ'⊑τ'
    with lift-syn c ((_ isSlice ψ'⊑τ') ∷ₛ Γ'')
           (⊑∷
             (⊑.trans {A = Typ} φ⊑ψγ
               (syn-precision
                 (⊑.trans {A = Assms}
                   (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₁ γ₂) γ⊑)
                 (⊑.refl {A = Exp}) d' dγ))
             (⊑.trans {A = Assms}
               (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₁ γ₂) γ⊑))
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    ψₚ , n' , Γᶠ , φᶠ , focus⊑ , sdef₂ d' cls , d

  lift-syn (minScase₀ {eq = eq} c) Γ'' γ⊑ with lift-syn c Γ'' γ⊑
  ... | ψ₀ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    ⊥ₛ , n' , Γᶠ , φᶠ , focus⊑ ,
    scase₀ cls (match+ₛ ψ₀ eq) ⇑□ ⇑□ ~?₁ , d

  lift-syn
      (minScase₁ {τ₀ = τ₀} {D₀ = D₀} {eq = eq} {con = con}
                  {φ₁ = φ₁} {γ₁ = γ₁} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      Γ'' γ⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ₀ .proof) D₀
  ... | ψγ , dγ , q⊑ψγ | ψ₀' , d₀' , ψ₀'⊑τ₀
    with unmatch+-min-cov τ₀ eq φ₁ ⊥ₛ
           (⊑.trans {A = Typ} q⊑ψγ
             (syn-precision
               (⊑.trans {A = Assms}
                 (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₀ γ₁) γ⊑)
               (⊑.refl {A = Exp}) d₀' dγ))
           (match+ₛ (_ isSlice ψ₀'⊑τ₀) eq)
  ... | φ₁⊑fst , _
    with lift-syn c ((fst+ₛ' (_ isSlice ψ₀'⊑τ₀) eq) ∷ₛ Γ'')
           (⊑∷ φ₁⊑fst
             (⊑.trans {A = Assms}
               (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₀ γ₁) γ⊑))
  ... | ψ₁' , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    ↑ (⊔-mono-⊑ con (ψ₁' .proof) ⊑□) ,
    n' , Γᶠ , φᶠ , focus⊑ ,
    scase₁ d₀' (match+ₛ (_ isSlice ψ₀'⊑τ₀) eq) cls ⇑□ ~?₁ , d

  lift-syn
      (minScase₂ {τ₀ = τ₀} {D₀ = D₀} {eq = eq} {con = con}
                  {φ₂ = φ₂} {γ₂ = γ₂} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      Γ'' γ⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ₀ .proof) D₀
  ... | ψγ , dγ , q⊑ψγ | ψ₀' , d₀' , ψ₀'⊑τ₀
    with unmatch+-min-cov τ₀ eq ⊥ₛ φ₂
           (⊑.trans {A = Typ} q⊑ψγ
             (syn-precision
               (⊑.trans {A = Assms}
                 (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₀ γ₂) γ⊑)
               (⊑.refl {A = Exp}) d₀' dγ))
           (match+ₛ (_ isSlice ψ₀'⊑τ₀) eq)
  ... | _ , φ₂⊑snd
    with lift-syn c ((snd+ₛ' (_ isSlice ψ₀'⊑τ₀) eq) ∷ₛ Γ'')
           (⊑∷ φ₂⊑snd
             (⊑.trans {A = Assms}
               (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₀ γ₂) γ⊑))
  ... | ψ₂' , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    ↑ (⊔-mono-⊑ con ⊑□ (ψ₂' .proof)) ,
    n' , Γᶠ , φᶠ , focus⊑ ,
    scase₂ d₀' (match+ₛ (_ isSlice ψ₀'⊑τ₀) eq) ⇑□ cls ~?₂ , d

  lift-pos (minASub {con = con} c) Γ'' γ⊑ uₚ _
    with lift-syn c Γ'' γ⊑
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    n' , Γᶠ , φᶠ , focus⊑ ,
    aSub cls (~-⊑-down con (uₚ .proof) (ψₚ .proof)) , d

  lift-pos (minAι₁ {τₒ = τₒ} {eq = eq} {uᵢ = uᵢ} c)
      Γ'' γ⊑ uₚ uₒ⊑
    with unmatch+-min-cov τₒ eq uᵢ ⊥ₛ uₒ⊑ (match+ₛ uₚ eq)
  ... | uᵢ⊑fst , _
    with lift-pos c Γ'' γ⊑ (fst+ₛ' uₚ eq) uᵢ⊑fst
  ... | n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    n' , Γᶠ , φᶠ , focus⊑ , aι₁ (match+ₛ uₚ eq) cls , d

  lift-pos (minAι₂ {τₒ = τₒ} {eq = eq} {uᵢ = uᵢ} c)
      Γ'' γ⊑ uₚ uₒ⊑
    with unmatch+-min-cov τₒ eq ⊥ₛ uᵢ uₒ⊑ (match+ₛ uₚ eq)
  ... | _ , uᵢ⊑snd
    with lift-pos c Γ'' γ⊑ (snd+ₛ' uₚ eq) uᵢ⊑snd
  ... | n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    n' , Γᶠ , φᶠ , focus⊑ , aι₂ (match+ₛ uₚ eq) cls , d

  lift-pos (minA&₁ {τₒ = τₒ} {eq = eq} {uᵢ = uᵢ} c)
      Γ'' γ⊑ uₚ uₒ⊑
    with unmatch×-min-cov τₒ eq uᵢ ⊥ₛ uₒ⊑ (match×ₛ uₚ eq)
  ... | uᵢ⊑fst , _
    with lift-pos c Γ'' γ⊑ (fst×ₛ' uₚ eq) uᵢ⊑fst
  ... | n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    n' , Γᶠ , φᶠ , focus⊑ ,
    a&₁ (match×ₛ uₚ eq) cls (⇓Sub ⇑□ ~?₁) , d

  lift-pos (minA&₂ {τₒ = τₒ} {eq = eq} {uᵢ = uᵢ} c)
      Γ'' γ⊑ uₚ uₒ⊑
    with unmatch×-min-cov τₒ eq ⊥ₛ uᵢ uₒ⊑ (match×ₛ uₚ eq)
  ... | _ , uᵢ⊑snd
    with lift-pos c Γ'' γ⊑ (snd×ₛ uₚ eq) uᵢ⊑snd
  ... | n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    n' , Γᶠ , φᶠ , focus⊑ ,
    a&₂ (match×ₛ uₚ eq) (⇓Sub ⇑□ ~?₁) cls , d

  lift-pos (minAλ⇒ {τₒ = τₒ} {eq = eq} {φ₁ = φ₁} {uᵢ = uᵢ} c)
      Γ'' γ⊑ uₚ uₒ⊑
    with unmatch⇒-min-cov τₒ eq φ₁ uᵢ uₒ⊑ (match⇒ₛ uₚ eq)
  ... | φ₁⊑dom , uᵢ⊑cod
    with lift-pos c ((dom⇒ₛ uₚ eq) ∷ₛ Γ'') (⊑∷ φ₁⊑dom γ⊑)
           (cod⇒ₛ uₚ eq) uᵢ⊑cod
  ... | n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    n' , Γᶠ , φᶠ , focus⊑ , aλ⇒ (match⇒ₛ uₚ eq) cls , d

  lift-pos
      (minAλ: {τₒ = τₒ} {τ₁ = τ₁} {con = con} {eq = eq} {wf = wf}
               {φ₁ = φ₁} {uᵢ = uᵢ} c)
      Γ'' γ⊑ uₚ uₒ⊑
    with ⊔-ann-⇒-⊑ (uₚ .proof) (φ₁ .proof) eq
  ... | _ , bₚ , eqₚ , bₚ⊑τ₂
    with unmatch⇒-min-cov τₒ (proj₂ (ann-⇒-plain {τₒ} {τ₁} eq))
           ⊥ₛ uᵢ uₒ⊑
           (proj₂ (ann-⇒-plain {uₚ .↓} {φ₁ .↓} eqₚ))
  ... | _ , uᵢ⊑bₚ
    with lift-pos c (φ₁ ∷ₛ Γ'') (⊑∷ (⊑.refl {A = Typ}) γ⊑)
           (_ isSlice bₚ⊑τ₂) uᵢ⊑bₚ
  ... | n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    n' , Γᶠ , φᶠ , focus⊑ ,
    aλ: (~-⊑-down con (uₚ .proof) (⊑⇒ (φ₁ .proof) ⊑□))
      eqₚ (wf-⊑ wf (φ₁ .proof)) cls , d

  lift-pos (minAdef₁ c) Γ'' γ⊑ uₚ _ with lift-syn c Γ'' γ⊑
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    n' , Γᶠ , φᶠ , focus⊑ , adef₁ cls (⇓Sub ⇑□ ~?₁) , d

  lift-pos
      (minAdef₂ {τ' = τ'} {D₁ = D₁} {φ = φ} {γ₂ = γ₂}
                  {σ₁ = σ₁} {γ₁ = γ₁} c f)
      Γ'' γ⊑ uₚ uₒ⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ₁ .proof) D₁
  ... | ψγ , dγ , φ⊑ψγ | ψ' , d' , ψ'⊑τ'
    with lift-pos c ((_ isSlice ψ'⊑τ') ∷ₛ Γ'')
           (⊑∷
             (⊑.trans {A = Typ} φ⊑ψγ
               (syn-precision
                 (⊑.trans {A = Assms}
                   (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₁ γ₂) γ⊑)
                 (⊑.refl {A = Exp}) d' dγ))
             (⊑.trans {A = Assms}
               (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₁ γ₂) γ⊑))
           uₚ uₒ⊑
  ... | n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    n' , Γᶠ , φᶠ , focus⊑ , adef₂ d' cls , d

  lift-pos (minAcase₀ {eq = eq} c) Γ'' γ⊑ uₚ _ with lift-syn c Γ'' γ⊑
  ... | ψ₀ , n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    n' , Γᶠ , φᶠ , focus⊑ ,
    acase₀ cls (match+ₛ ψ₀ eq) (⇓Sub ⇑□ ~?₁) (⇓Sub ⇑□ ~?₁) , d

  lift-pos
      (minAcase₁ {τ₀ = τ₀} {D₀ = D₀} {eq = eq} {φ₁ = φ₁}
                  {γ₁ = γ₁} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      Γ'' γ⊑ uₚ uₒ⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ₀ .proof) D₀
  ... | ψγ , dγ , q⊑ψγ | ψ₀' , d₀' , ψ₀'⊑τ₀
    with unmatch+-min-cov τ₀ eq φ₁ ⊥ₛ
           (⊑.trans {A = Typ} q⊑ψγ
             (syn-precision
               (⊑.trans {A = Assms}
                 (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₀ γ₁) γ⊑)
               (⊑.refl {A = Exp}) d₀' dγ))
           (match+ₛ (_ isSlice ψ₀'⊑τ₀) eq)
  ... | φ₁⊑fst , _
    with lift-pos c ((fst+ₛ' (_ isSlice ψ₀'⊑τ₀) eq) ∷ₛ Γ'')
           (⊑∷ φ₁⊑fst
             (⊑.trans {A = Assms}
               (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₀ γ₁) γ⊑))
           uₚ uₒ⊑
  ... | n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    n' , Γᶠ , φᶠ , focus⊑ ,
    acase₁ d₀' (match+ₛ (_ isSlice ψ₀'⊑τ₀) eq) cls (⇓Sub ⇑□ ~?₁) , d

  lift-pos
      (minAcase₂ {τ₀ = τ₀} {D₀ = D₀} {eq = eq} {φ₂ = φ₂}
                  {γ₂ = γ₂} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      Γ'' γ⊑ uₚ uₒ⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ₀ .proof) D₀
  ... | ψγ , dγ , q⊑ψγ | ψ₀' , d₀' , ψ₀'⊑τ₀
    with unmatch+-min-cov τ₀ eq ⊥ₛ φ₂
           (⊑.trans {A = Typ} q⊑ψγ
             (syn-precision
               (⊑.trans {A = Assms}
                 (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₀ γ₂) γ⊑)
               (⊑.refl {A = Exp}) d₀' dγ))
           (match+ₛ (_ isSlice ψ₀'⊑τ₀) eq)
  ... | _ , φ₂⊑snd
    with lift-pos c ((snd+ₛ' (_ isSlice ψ₀'⊑τ₀) eq) ∷ₛ Γ'')
           (⊑∷ φ₂⊑snd
             (⊑.trans {A = Assms}
               (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₀ γ₂) γ⊑))
           uₚ uₒ⊑
  ... | n' , Γᶠ , φᶠ , focus⊑ , cls , d =
    n' , Γᶠ , φᶠ , focus⊑ ,
    acase₂ d₀' (match+ₛ (_ isSlice ψ₀'⊑τ₀) eq) (⇓Sub ⇑□ ~?₁) cls , d

mutual
  extract : ∀ {n Γ₀ C n_f Γ e τ τₚ}
              {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
              {D : n_f , Γ ⊢ e ⇑ τ}
              {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
          → (c : Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ)
          → SynTypeSlice Cls D u
  extract {κ = κ} {γ = γ} c with lift-syn c γ (⊑.refl {A = Assms})
  ... | ψₚ , n' , Γᶠ , φᶠ , focus⊑ , cls , d = record
    { κ = κ ; γ = γ ; outer = ψₚ ; focus-slice = focus c
    ; powered = n' , Γᶠ , φᶠ , focus⊑ , cls , d }

  extract-pos : ∀ {n Γ₀ C n_f Γ e τ τₚ}
                  {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                  {D : n_f , Γ ⊢ e ⇑ τ}
                  {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋}
                  {uₒ : ⌊ τₚ ⌋} {γ : ⌊ Γ₀ ⌋}
              → (c : Cls , D ◂ u ⤳ κ ∣ σ ⇓ uₒ ⊣ γ)
              → SynPosTypeSlice Cls D u
  extract-pos {κ = κ} {uₒ = uₒ} {γ = γ} c
    with lift-pos c γ (⊑.refl {A = Assms}) uₒ (⊑.refl {A = Typ})
  ... | n' , Γᶠ , φᶠ , focus⊑ , cls , d = record
    { pos-κ = κ ; pos-γ = γ ; pos-outer = uₒ
    ; pos-focus-slice = focus-pos c
    ; pos-powered = n' , Γᶠ , φᶠ , focus⊑ , cls , d }

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

syn-rival : ∀ {n Γ₀ C n_f Γ e τ τₚ}
              (Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ])
              {D : n_f , Γ ⊢ e ⇑ τ} {u : ⌊ τ ⌋}
              (κr : ⌊ C ⌋) (γr : ⌊ Γ₀ ⌋) (fr : SynSlice D ◂ u)
              {n'' : ℕ} {ψ : Typ} (Γᶠ : ⌊ Γ ⌋) (φᶠ : ⌊ τ ⌋)
          → SS._↓γₛ fr ⊑ₛ Γᶠ
          → n , γr .↓ ⊢ κr .↓ at synPos ψ ▷ n'' , Γᶠ .↓ [ ⇒mode (φᶠ .↓) ]
          → n'' , Γᶠ .↓ ⊢ SS._↓σ fr ⇑ φᶠ .↓
          → SynTypeSlice Cls D u
syn-rival Cls κr γr fr Γᶠ φᶠ focus⊑ cls d = record
  { κ = κr
  ; γ = γr
  ; outer = ↑ (syn-cls-precision (γr .proof) (κr .proof)
      (⇒mode-⊑ (φᶠ .proof)) cls Cls)
  ; focus-slice = fr
  ; powered = _ , Γᶠ , φᶠ , focus⊑ , cls , d
  }

pos-rival : ∀ {n Γ₀ C n_f Γ e τ τₚ}
              (Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n_f , Γ [ ⇒mode τ ])
              {D : n_f , Γ ⊢ e ⇑ τ} {u : ⌊ τ ⌋}
              (κr : ⌊ C ⌋) (γr : ⌊ Γ₀ ⌋) (uₚ : ⌊ τₚ ⌋)
              (fr : SynSlice D ◂ u)
              {n'' : ℕ} (Γᶠ : ⌊ Γ ⌋) (φᶠ : ⌊ τ ⌋)
          → SS._↓γₛ fr ⊑ₛ Γᶠ
          → n , γr .↓ ⊢ κr .↓ at anaPos (uₚ .↓) ▷ n'' , Γᶠ .↓
              [ ⇒mode (φᶠ .↓) ]
          → n'' , Γᶠ .↓ ⊢ SS._↓σ fr ⇑ φᶠ .↓
          → SynPosTypeSlice Cls D u
pos-rival Cls κr γr uₚ fr Γᶠ φᶠ focus⊑ cls d = record
  { pos-κ = κr ; pos-γ = γr ; pos-outer = uₚ ; pos-focus-slice = fr
  ; pos-powered = _ , Γᶠ , φᶠ , focus⊑ , cls , d }

mutual
  extract-least : ∀ {n Γ₀ C n_f Γ e τ τₚ}
                    {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                    {D : n_f , Γ ⊢ e ⇑ τ}
                    {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
                → (c : Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ)
                → (r : SynTypeSlice Cls D u)
                → SynTypeSlice.κ r ⊑ₛ κ
                → SS._↓σₛ (r .focus-slice) ⊑ₛ σ
                → extract c ⊑ r
  extract-least (minS○ {σ = σ} {γ = γ} c) r κr⊑ σr⊑
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

  extract-least (minSι₁ {Cls = Cls} c) r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | (_ isSlice ⊑ι₁ κr⊑C) | ⊑ι₁ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , sι₁ cls , d
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) (r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r = (⊑ι₁ κ⊑r , γ⊑r) , σ⊑r

  extract-least (minSι₂ {Cls = Cls} c) r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | (_ isSlice ⊑ι₂ κr⊑C) | ⊑ι₂ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , sι₂ cls , d
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) (r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r = (⊑ι₂ κ⊑r , γ⊑r) , σ⊑r

  extract-least (minS&₁ {Cls = Cls} c) r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | (_ isSlice ⊑&₁ κr⊑C er⊑) | ⊑&₁ κr⊑κ er⊑□
      | n' , Γᶠ , φᶠ , focus⊑ , s&₁ cls dr , d
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) (r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r = (⊑&₁ κ⊑r ⊑□ , γ⊑r) , σ⊑r

  extract-least (minS&₂ {Cls = Cls} c) r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | (_ isSlice ⊑&₂ er⊑ κr⊑C) | ⊑&₂ er⊑□ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , s&₂ dr cls , d
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) (r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r = (⊑&₂ ⊑□ κ⊑r , γ⊑r) , σ⊑r

  extract-least (minSπ₁ {Cls = Cls} c) r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | (_ isSlice ⊑π₁ κr⊑C) | ⊑π₁ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , sπ₁ cls eqr , d
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) (r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r = (⊑π₁ κ⊑r , γ⊑r) , σ⊑r

  extract-least (minSπ₂ {Cls = Cls} c) r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | (_ isSlice ⊑π₂ κr⊑C) | ⊑π₂ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , sπ₂ cls eqr , d
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) (r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r = (⊑π₂ κ⊑r , γ⊑r) , σ⊑r

  extract-least (minS∘₁ {Cls = Cls} c) r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | (_ isSlice ⊑∘₁ κr⊑C er⊑) | ⊑∘₁ κr⊑κ er⊑□
      | n' , Γᶠ , φᶠ , focus⊑ , s∘₁ cls eqr dr , d
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) (r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r = (⊑∘₁ κ⊑r ⊑□ , γ⊑r) , σ⊑r

  extract-least (minS<>₁ {Cls = Cls} c) r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | (_ isSlice ⊑<>₁ κr⊑C τr⊑) | ⊑<>₁ κr⊑κ τr⊑□
      | n' , Γᶠ , φᶠ , focus⊑ , s<>₁ cls eqr wfr , d
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) (r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r = (⊑<>₁ κ⊑r ⊑□ , γ⊑r) , σ⊑r

  extract-least (minSλ: {Cls = Cls} c) r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | ((λ: tr ⇒ _) isSlice ⊑λ tr⊑τ₁ κr⊑C) | ⊑λ tr⊑φ₁ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , sλ: wfr cls , d
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C)
             ((_ isSlice tr⊑τ₁) ∷ₛ r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , ⊑∷ φ₁⊑tr γ⊑r) , σ⊑r =
    (⊑λ φ₁⊑tr κ⊑r , γ⊑r) , σ⊑r

  extract-least {Γ₀ = Γ₀} {Cls = s∘₂ D₁ eq Cls}
      (minS∘₂ {τ₀ = τ₀} {D₁ = D₁} {eq = eq}
               {uₒ = uₒ} {γ' = γ'} {σ₁ = σ₁} {γ₁ = γ₁} c f)
      r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | ((_ ∘₂ _) isSlice ⊑∘₂ er⊑e κr⊑C)
      | ⊑∘₂ er⊑σ₁ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , s∘₂ Dr eqr clsr , d
    with syn-precision (r .γ .proof) er⊑e D₁ Dr
  ... | τr⊑τ₀
    with ⊔-⇒-⊑ τr⊑τ₀ eq
  ... | _ , _ , eqra , a⊑τ₁ , _
    with refl ← ⇒-inj-fst (trans (sym eqra) eqr)
    with refl ← ⇒-inj-snd (trans (sym eqra) eqr)
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C) (r .γ) (_ isSlice a⊑τ₁)
             (r .focus-slice) Γᶠ φᶠ focus⊑ clsr d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , γ'⊑r) , σ⊑r) , uₒ⊑a
    with static-gradual-syn (⊑.refl {A = Assms}) er⊑e D₁
  ... | ψr , dr , ψr⊑τ₀
    with ⊔-⇒-⊑ ψr⊑τ₀ eq
  ... | af , _ , eqf , _ , _
    with ⊔-⇒-⊑
           (syn-precision (r .γ .proof) (⊑.refl {A = Exp}) dr Dr) eqf
  ... | _ , _ , eqf₂ , a⊑af , _
    with refl ← ⇒-inj-fst (trans (sym eqf₂) eqr)
    with refl ← ⇒-inj-snd (trans (sym eqf₂) eqr)
    with FC.extract-minimal f
           (record
             { expₛ = _ isSlice er⊑e
             ; type = _ isSlice ψr⊑τ₀
             ; syn = dr
             ; valid = unmatch⇒-min-least τ₀ eq uₒ ⊥ₛ ψr⊑τ₀ eqf
                 (⊑.trans {A = Typ} uₒ⊑a a⊑af) ⊑□
             })
           (subst (_ ⊑e_)
             (sym (cong (λ x → x .↓) (FC.extract-σ f))) er⊑σ₁)
  ... | eqfix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) eqfix
  ... | eqσ₁ =
    ( ⊑∘₂ (⊑.reflexive {A = Exp} eqσ₁) κ⊑r
    , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₁} {γ'} {r .γ}
        (FC.extract-ctx-min f
          (subst (λ x → _ , r .γ .↓ ⊢ x ⇑ _) (sym eqσ₁) Dr)
          (unmatch⇒-min-least τ₀ eq uₒ ⊥ₛ τr⊑τ₀ eqr uₒ⊑a ⊑□)
          (r .γ .proof))
        γ'⊑r
    ) , σ⊑r

  extract-least (minSΛ {Cls = Cls} c) r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | (_ isSlice ⊑Λ κr⊑C) | ⊑Λ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , sΛ cls , d
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) (shiftΓₛ (r .γ))
             (r .focus-slice) Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ'⊑shift) , σ⊑r =
    ( ⊑Λ κ⊑r
    , ⊑.trans {A = Assms} (unshiftΓ-⊑ γ'⊑shift)
        (⊑.reflexive {A = Assms} (unshiftΓ-shiftΓ (r .γ .↓)))
    ) , σ⊑r

  extract-least (minSdef₁ {Cls = Cls} c) r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | (_ isSlice ⊑def₁ κr⊑C er⊑) | ⊑def₁ κr⊑κ er⊑□
      | n' , Γᶠ , φᶠ , focus⊑ , sdef₁ cls dr , d
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) (r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r = (⊑def₁ κ⊑r ⊑□ , γ⊑r) , σ⊑r

  extract-least {Γ₀ = Γ₀} {Cls = sdef₂ D₁ Cls}
      (minSdef₂ {τ' = τ'} {D₁ = D₁} {φ = φ} {γ₂ = γ₂}
                 {σ₁ = σ₁} {γ₁ = γ₁} c f)
      r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | ((def er ⊢₂ _) isSlice ⊑def₂ er⊑e κr⊑C)
      | ⊑def₂ er⊑σ₁ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , sdef₂ Dr cls , d
    with syn-precision (r .γ .proof) er⊑e D₁ Dr
  ... | τr⊑τ'
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C)
             ((_ isSlice τr⊑τ') ∷ₛ r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , ⊑∷ φ⊑τr γ₂⊑r) , σ⊑r
    with static-gradual-syn (⊑.refl {A = Assms}) er⊑e D₁
  ... | ψr , dr , ψr⊑τ'
    with FC.extract-minimal f
           (record
             { expₛ = _ isSlice er⊑e
             ; type = _ isSlice ψr⊑τ'
             ; syn = dr
             ; valid = ⊑.trans {A = Typ} φ⊑τr
                 (syn-precision (r .γ .proof) (⊑.refl {A = Exp}) dr Dr)
             })
           (subst (_ ⊑e_)
             (sym (cong (λ x → x .↓) (FC.extract-σ f))) er⊑σ₁)
  ... | eqfix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) eqfix
  ... | eqσ₁ =
    ( ⊑def₂ (⊑.reflexive {A = Exp} eqσ₁) κ⊑r
    , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₁} {γ₂} {r .γ}
        (FC.extract-ctx-min f
          (subst (λ x → _ , r .γ .↓ ⊢ x ⇑ _) (sym eqσ₁) Dr)
          φ⊑τr (r .γ .proof))
        γ₂⊑r
    ) , σ⊑r

  extract-least {Cls = scase₀ Cls eq d₁ d₂ con} (minScase₀ c) r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | (_ isSlice ⊑case₀ κr⊑C _ _)
      | ⊑case₀ κr⊑κ _ _
      | n' , Γᶠ , φᶠ , focus⊑ , scase₀ cls eqr d₁r d₂r conr , d
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) (r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r =
    (⊑case₀ κ⊑r ⊑□ ⊑□ , γ⊑r) , σ⊑r

  extract-least {Γ₀ = Γ₀} {Cls = scase₁ D₀ eq Cls d₂ con}
      (minScase₁ {τ₀ = τ₀} {D₀ = D₀} {eq = eq} {φ₁ = φ₁}
                  {γ₁ = γ₁} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | ((case er of _ ·₁ _) isSlice ⊑case₁ er⊑e κr⊑C br⊑)
      | ⊑case₁ er⊑σ₀ κr⊑κ br⊑□
      | n' , Γᶠ , φᶠ , focus⊑ , scase₁ Dr eqr cls d₂r conr , d
    with syn-precision (r .γ .proof) er⊑e D₀ Dr
  ... | τr⊑τ₀
    with ⊔-+-⊑ τr⊑τ₀ eq
  ... | _ , _ , eqra , a⊑τ₁ , _
    with refl ← +-inj-fst (trans (sym eqra) eqr)
    with refl ← +-inj-snd (trans (sym eqra) eqr)
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C)
             ((_ isSlice a⊑τ₁) ∷ₛ r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , ⊑∷ φ₁⊑a γ₁⊑r) , σ⊑r
    with static-gradual-syn (⊑.refl {A = Assms}) er⊑e D₀
  ... | ψr , dr , ψr⊑τ₀
    with ⊔-+-⊑ ψr⊑τ₀ eq
  ... | af , _ , eqf , _ , _
    with ⊔-+-⊑
           (syn-precision (r .γ .proof) (⊑.refl {A = Exp}) dr Dr) eqf
  ... | _ , _ , eqf₂ , a⊑af , _
    with refl ← +-inj-fst (trans (sym eqf₂) eqr)
    with refl ← +-inj-snd (trans (sym eqf₂) eqr)
    with FC.extract-minimal f
           (record
             { expₛ = _ isSlice er⊑e
             ; type = _ isSlice ψr⊑τ₀
             ; syn = dr
             ; valid = unmatch+-min-least τ₀ eq φ₁ ⊥ₛ ψr⊑τ₀ eqf
                 (⊑.trans {A = Typ} φ₁⊑a a⊑af) ⊑□
             })
           (subst (_ ⊑e_)
             (sym (cong (λ x → x .↓) (FC.extract-σ f))) er⊑σ₀)
  ... | eqfix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) eqfix
  ... | eqσ₀ =
    ( ⊑case₁ (⊑.reflexive {A = Exp} eqσ₀) κ⊑r ⊑□
    , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₀} {γ₁} {r .γ}
        (FC.extract-ctx-min f
          (subst (λ x → _ , r .γ .↓ ⊢ x ⇑ _) (sym eqσ₀) Dr)
          (unmatch+-min-least τ₀ eq φ₁ ⊥ₛ τr⊑τ₀ eqr φ₁⊑a ⊑□)
          (r .γ .proof))
        γ₁⊑r
    ) , σ⊑r

  extract-least {Γ₀ = Γ₀} {Cls = scase₂ D₀ eq d₁ Cls con}
      (minScase₂ {τ₀ = τ₀} {D₀ = D₀} {eq = eq} {φ₂ = φ₂}
                  {γ₂ = γ₂} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      r κr⊑ σr⊑
    with r .κ | κr⊑ | r .powered
  ... | ((case er of₂ _ · _) isSlice ⊑case₂ er⊑e ar⊑ κr⊑C)
      | ⊑case₂ er⊑σ₀ ar⊑□ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , scase₂ Dr eqr d₁r cls conr , d
    with syn-precision (r .γ .proof) er⊑e D₀ Dr
  ... | τr⊑τ₀
    with ⊔-+-⊑ τr⊑τ₀ eq
  ... | _ , _ , eqra , _ , b⊑τ₂
    with refl ← +-inj-fst (trans (sym eqra) eqr)
    with refl ← +-inj-snd (trans (sym eqra) eqr)
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C)
             ((_ isSlice b⊑τ₂) ∷ₛ r .γ) (r .focus-slice)
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , ⊑∷ φ₂⊑b γ₂⊑r) , σ⊑r
    with static-gradual-syn (⊑.refl {A = Assms}) er⊑e D₀
  ... | ψr , dr , ψr⊑τ₀
    with ⊔-+-⊑ ψr⊑τ₀ eq
  ... | _ , bf , eqf , _ , _
    with ⊔-+-⊑
           (syn-precision (r .γ .proof) (⊑.refl {A = Exp}) dr Dr) eqf
  ... | _ , _ , eqf₂ , _ , b⊑bf
    with refl ← +-inj-fst (trans (sym eqf₂) eqr)
    with refl ← +-inj-snd (trans (sym eqf₂) eqr)
    with FC.extract-minimal f
           (record
             { expₛ = _ isSlice er⊑e
             ; type = _ isSlice ψr⊑τ₀
             ; syn = dr
             ; valid = unmatch+-min-least τ₀ eq ⊥ₛ φ₂ ψr⊑τ₀ eqf
                 ⊑□ (⊑.trans {A = Typ} φ₂⊑b b⊑bf)
             })
           (subst (_ ⊑e_)
             (sym (cong (λ x → x .↓) (FC.extract-σ f))) er⊑σ₀)
  ... | eqfix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) eqfix
  ... | eqσ₀ =
    ( ⊑case₂ (⊑.reflexive {A = Exp} eqσ₀) ⊑□ κ⊑r
    , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₀} {γ₂} {r .γ}
        (FC.extract-ctx-min f
          (subst (λ x → _ , r .γ .↓ ⊢ x ⇑ _) (sym eqσ₀) Dr)
          (unmatch+-min-least τ₀ eq ⊥ₛ φ₂ τr⊑τ₀ eqr ⊑□ φ₂⊑b)
          (r .γ .proof))
        γ₂⊑r
    ) , σ⊑r

  extract-minimal : ∀ {n Γ₀ C n_f Γ e τ τₚ}
                      {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                      {D : n_f , Γ ⊢ e ⇑ τ}
                      {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋} {γ : ⌊ Γ₀ ⌋}
                  → (c : Cls , D ◂ u ⤳ κ ∣ σ ⊣ γ)
                  → IsMinimal (extract c)
  extract-minimal c r ((κr⊑ , γr⊑) , σr⊑)
    with extract-least c r κr⊑
           (subst (SS._↓σ (r .focus-slice) ⊑e_) (focus-σ c) σr⊑)
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
                    → r .pos-κ ⊑ₛ κ
                    → SS._↓σₛ (r .pos-focus-slice) ⊑ₛ σ
                    → extract-pos c ⊑ r
  extract-pos-least (minASub {Cls = Cls} {D = D} c) r κr⊑ σr⊑
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
           κr⊑ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r =
    ((κ⊑r , γ⊑r) , σ⊑r) , ⊑ₛLat.⊥ₛ-min {A = Typ} (r .pos-outer)

  extract-pos-least {Cls = aι₁ eq Cls}
      (minAι₁ {τₒ = τₒ} {eq = eq} {uᵢ = uᵢ} c)
      r κr⊑ σr⊑
    with r .pos-κ | κr⊑ | r .pos-powered

  ... | (_ isSlice ⊑ι₁ κr⊑C) | ⊑ι₁ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , aSub (sι₁ scls) conr , d
    =
    let ((κ⊑r , γ⊑r) , σ⊑r) , uᵢ⊑□ =
          extract-pos-least c
            (pos-rival Cls (_ isSlice κr⊑C) (r .pos-γ) ⊥ₛ
              (r .pos-focus-slice) Γᶠ φᶠ focus⊑ (aSub scls ~?₂) d)
            κr⊑κ σr⊑
    in ((⊑ι₁ κ⊑r , γ⊑r) , σ⊑r) ,
       subst (_⊑t (r .pos-outer .↓))
         (sym (unmatch+-min-□ eq uᵢ ⊥ₛ (⊑□-inv uᵢ⊑□) refl)) ⊑□
  ... | (_ isSlice ⊑ι₁ κr⊑C) | ⊑ι₁ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , aι₁ eqr cls , d
    with ⊔-+-⊑ (r .pos-outer .proof) eq
  ... | _ , _ , eq' , a⊑τ₁ , _
    with refl ← +-inj-fst (trans (sym eq') eqr)
    with refl ← +-inj-snd (trans (sym eq') eqr)
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C) (r .pos-γ) (_ isSlice a⊑τ₁)
             (r .pos-focus-slice) Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , γ⊑r) , σ⊑r) , uᵢ⊑a =
    ((⊑ι₁ κ⊑r , γ⊑r) , σ⊑r) ,
    unmatch+-min-least τₒ eq uᵢ ⊥ₛ (r .pos-outer .proof) eqr uᵢ⊑a ⊑□

  extract-pos-least {Cls = aι₂ eq Cls}
      (minAι₂ {τₒ = τₒ} {eq = eq} {uᵢ = uᵢ} c)
      r κr⊑ σr⊑
    with r .pos-κ | κr⊑ | r .pos-powered

  ... | (_ isSlice ⊑ι₂ κr⊑C) | ⊑ι₂ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , aSub (sι₂ scls) conr , d
    =
    let ((κ⊑r , γ⊑r) , σ⊑r) , uᵢ⊑□ =
          extract-pos-least c
            (pos-rival Cls (_ isSlice κr⊑C) (r .pos-γ) ⊥ₛ
              (r .pos-focus-slice) Γᶠ φᶠ focus⊑ (aSub scls ~?₂) d)
            κr⊑κ σr⊑
    in ((⊑ι₂ κ⊑r , γ⊑r) , σ⊑r) ,
       subst (_⊑t (r .pos-outer .↓))
         (sym (unmatch+-min-□ eq ⊥ₛ uᵢ refl (⊑□-inv uᵢ⊑□))) ⊑□
  ... | (_ isSlice ⊑ι₂ κr⊑C) | ⊑ι₂ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , aι₂ eqr cls , d
    with ⊔-+-⊑ (r .pos-outer .proof) eq
  ... | _ , _ , eq' , _ , b⊑τ₂
    with refl ← +-inj-fst (trans (sym eq') eqr)
    with refl ← +-inj-snd (trans (sym eq') eqr)
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C) (r .pos-γ) (_ isSlice b⊑τ₂)
             (r .pos-focus-slice) Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , γ⊑r) , σ⊑r) , uᵢ⊑b =
    ((⊑ι₂ κ⊑r , γ⊑r) , σ⊑r) ,
    unmatch+-min-least τₒ eq ⊥ₛ uᵢ (r .pos-outer .proof) eqr ⊑□ uᵢ⊑b

  extract-pos-least {Cls = a&₁ eq Cls d₂}
      (minA&₁ {τₒ = τₒ} {eq = eq} {uᵢ = uᵢ} c)
      r κr⊑ σr⊑
    with r .pos-κ | κr⊑ | r .pos-powered

  ... | (_ isSlice ⊑&₁ κr⊑C er⊑) | ⊑&₁ κr⊑κ er⊑□
      | n' , Γᶠ , φᶠ , focus⊑ , aSub (s&₁ scls dr) conr , d
    =
    let ((κ⊑r , γ⊑r) , σ⊑r) , uᵢ⊑□ =
          extract-pos-least c
            (pos-rival Cls (_ isSlice κr⊑C) (r .pos-γ) ⊥ₛ
              (r .pos-focus-slice) Γᶠ φᶠ focus⊑ (aSub scls ~?₂) d)
            κr⊑κ σr⊑
    in ((⊑&₁ κ⊑r ⊑□ , γ⊑r) , σ⊑r) ,
       subst (_⊑t (r .pos-outer .↓))
         (sym (unmatch×-min-□ eq uᵢ ⊥ₛ (⊑□-inv uᵢ⊑□) refl)) ⊑□
  ... | (_ isSlice ⊑&₁ κr⊑C er⊑) | ⊑&₁ κr⊑κ er⊑□
      | n' , Γᶠ , φᶠ , focus⊑ , a&₁ eqr cls dr , d
    with ⊔-×-⊑ (r .pos-outer .proof) eq
  ... | _ , _ , eq' , a⊑τ₁ , _
    with refl ← ×-inj-fst (trans (sym eq') eqr)
    with refl ← ×-inj-snd (trans (sym eq') eqr)
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C) (r .pos-γ) (_ isSlice a⊑τ₁)
             (r .pos-focus-slice) Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , γ⊑r) , σ⊑r) , uᵢ⊑a =
    ((⊑&₁ κ⊑r ⊑□ , γ⊑r) , σ⊑r) ,
    unmatch×-min-least τₒ eq uᵢ ⊥ₛ (r .pos-outer .proof) eqr uᵢ⊑a ⊑□

  extract-pos-least {Cls = a&₂ eq d₁ Cls}
      (minA&₂ {τₒ = τₒ} {eq = eq} {uᵢ = uᵢ} c)
      r κr⊑ σr⊑
    with r .pos-κ | κr⊑ | r .pos-powered

  ... | (_ isSlice ⊑&₂ er⊑ κr⊑C) | ⊑&₂ er⊑□ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , aSub (s&₂ dr scls) conr , d
    =
    let ((κ⊑r , γ⊑r) , σ⊑r) , uᵢ⊑□ =
          extract-pos-least c
            (pos-rival Cls (_ isSlice κr⊑C) (r .pos-γ) ⊥ₛ
              (r .pos-focus-slice) Γᶠ φᶠ focus⊑ (aSub scls ~?₂) d)
            κr⊑κ σr⊑
    in ((⊑&₂ ⊑□ κ⊑r , γ⊑r) , σ⊑r) ,
       subst (_⊑t (r .pos-outer .↓))
         (sym (unmatch×-min-□ eq ⊥ₛ uᵢ refl (⊑□-inv uᵢ⊑□))) ⊑□
  ... | (_ isSlice ⊑&₂ er⊑ κr⊑C) | ⊑&₂ er⊑□ κr⊑κ
      | n' , Γᶠ , φᶠ , focus⊑ , a&₂ eqr dr cls , d
    with ⊔-×-⊑ (r .pos-outer .proof) eq
  ... | _ , _ , eq' , _ , b⊑τ₂
    with refl ← ×-inj-fst (trans (sym eq') eqr)
    with refl ← ×-inj-snd (trans (sym eq') eqr)
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C) (r .pos-γ) (_ isSlice b⊑τ₂)
             (r .pos-focus-slice) Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , γ⊑r) , σ⊑r) , uᵢ⊑b =
    ((⊑&₂ ⊑□ κ⊑r , γ⊑r) , σ⊑r) ,
    unmatch×-min-least τₒ eq ⊥ₛ uᵢ (r .pos-outer .proof) eqr ⊑□ uᵢ⊑b

  extract-pos-least {Cls = aλ⇒ eq Cls}
      (minAλ⇒ {τₒ = τₒ} {eq = eq}
               {φ₁ = φ₁} {uᵢ = uᵢ} c)
      (record
        { pos-κ = _ isSlice ⊑λu κr⊑C
        ; pos-γ = γr
        ; pos-outer = ur
        ; pos-focus-slice = fr
        ; pos-powered = n' , Γᶠ , φᶠ , focus⊑ , aλ⇒ eqr cls , d
        })
      (⊑λu κr⊑κ) σr⊑
    with ⊔-⇒-⊑ (ur .proof) eq
  ... | _ , _ , eq' , a⊑τ₁ , b⊑τ₂
    with refl ← ⇒-inj-fst (trans (sym eq') eqr)
    with refl ← ⇒-inj-snd (trans (sym eq') eqr)
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C)
             ((_ isSlice a⊑τ₁) ∷ₛ γr) (_ isSlice b⊑τ₂)
             fr Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , ⊑∷ φ₁⊑a γ⊑r) , σ⊑r) , uᵢ⊑b =
    ((⊑λu κ⊑r , γ⊑r) , σ⊑r) ,
    unmatch⇒-min-least τₒ eq φ₁ uᵢ (ur .proof) eqr φ₁⊑a uᵢ⊑b

  extract-pos-least {Cls = aλ: con eq wf Cls}
      (minAλ: {τₒ = τₒ} {τ₁ = τ₁} {eq = eq}
               {φ₁ = φ₁} {uᵢ = uᵢ} c)
      (record
        { pos-κ = (λ: tr ⇒ _) isSlice ⊑λ tr⊑τ₁ κr⊑C
        ; pos-γ = γr
        ; pos-outer = ur
        ; pos-focus-slice = fr
        ; pos-powered = n' , Γᶠ , φᶠ , focus⊑ ,
            aSub (sλ: wfr cls) conr , d
        })
      (⊑λ tr⊑φ₁ κr⊑κ) σr⊑
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C)
             ((_ isSlice tr⊑τ₁) ∷ₛ γr) ⊥ₛ
             fr Γᶠ φᶠ focus⊑ (aSub cls ~?₂) d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , ⊑∷ φ₁⊑tr γ⊑r) , σ⊑r) , uᵢ⊑□ =
    ((⊑λ φ₁⊑tr κ⊑r , γ⊑r) , σ⊑r) ,
    subst (_⊑t (ur .↓))
      (sym (unmatch⇒-min-□
        (proj₂ (ann-⇒-plain {τₒ} {τ₁} eq)) ⊥ₛ uᵢ refl
        (⊑□-inv uᵢ⊑□))) ⊑□

  extract-pos-least {Cls = aλ: con eq wf Cls}
      (minAλ: {τₒ = τₒ} {τ₁ = τ₁} {eq = eq}
               {φ₁ = φ₁} {uᵢ = uᵢ} c)
      (record
        { pos-κ = (λ: tr ⇒ _) isSlice ⊑λ tr⊑τ₁ κr⊑C
        ; pos-γ = γr
        ; pos-outer = ur
        ; pos-focus-slice = fr
        ; pos-powered = n' , Γᶠ , φᶠ , focus⊑ ,
            aλ: conr eqr wfr cls , d
        })
      (⊑λ tr⊑φ₁ κr⊑κ) σr⊑
    with ⊔-ann-⇒-⊑ (ur .proof) tr⊑τ₁ eq
  ... | _ , b , eq' , b⊑τ₂
    with refl ← ⇒-inj-snd (trans (sym eq') eqr)
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C)
             ((_ isSlice tr⊑τ₁) ∷ₛ γr) (_ isSlice b⊑τ₂)
             fr Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , ⊑∷ φ₁⊑tr γ⊑r) , σ⊑r) , uᵢ⊑b =
    ((⊑λ φ₁⊑tr κ⊑r , γ⊑r) , σ⊑r) ,
    unmatch⇒-min-least τₒ (proj₂ (ann-⇒-plain {τₒ} {τ₁} eq))
      ⊥ₛ uᵢ (ur .proof)
      (proj₂ (ann-⇒-plain {ur .↓} {tr} eqr)) ⊑□ uᵢ⊑b

  extract-pos-least {Cls = adef₁ Cls d₂} (minAdef₁ c) r κr⊑ σr⊑
    with r .pos-κ | κr⊑ | r .pos-powered

  ... | (_ isSlice ⊑def₁ κr⊑C er⊑) | ⊑def₁ κr⊑κ er⊑□
      | n' , Γᶠ , φᶠ , focus⊑ , adef₁ scls dr , d
    =
    let (κ⊑r , γ⊑r) , σ⊑r =
          extract-least c
            (syn-rival Cls (_ isSlice κr⊑C) (r .pos-γ)
              (r .pos-focus-slice) Γᶠ φᶠ focus⊑ scls d)
            κr⊑κ σr⊑
    in ((⊑def₁ κ⊑r ⊑□ , γ⊑r) , σ⊑r) ,
       ⊑ₛLat.⊥ₛ-min {A = Typ} (r .pos-outer)
  ... | (_ isSlice ⊑def₁ κr⊑C er⊑) | ⊑def₁ κr⊑κ er⊑□
      | n' , Γᶠ , φᶠ , focus⊑ , aSub (sdef₁ scls dr) conr , d
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) (r .pos-γ)
             (r .pos-focus-slice) Γᶠ φᶠ focus⊑ scls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r =
    ((⊑def₁ κ⊑r ⊑□ , γ⊑r) , σ⊑r) ,
    ⊑ₛLat.⊥ₛ-min {A = Typ} (r .pos-outer)

  extract-pos-least {Γ₀ = Γ₀} {Cls = adef₂ D₁ Cls}
      (minAdef₂ {τ' = τ'} {D₁ = D₁} {φ = φ} {γ₂ = γ₂}
                  {σ₁ = σ₁} {γ₁ = γ₁} c f)
      (record
        { pos-κ = (def er ⊢₂ _) isSlice ⊑def₂ er⊑e κr⊑C
        ; pos-γ = γr
        ; pos-outer = ur
        ; pos-focus-slice = fr
        ; pos-powered = n' , Γᶠ , φᶠ , focus⊑ , adef₂ Dr cls , d
        })
      (⊑def₂ er⊑σ₁ κr⊑κ) σr⊑
    with syn-precision (γr .proof) er⊑e D₁ Dr
  ... | τr⊑τ'
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C)
             ((_ isSlice τr⊑τ') ∷ₛ γr) ur
             fr Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , ⊑∷ φ⊑τr γ₂⊑r) , σ⊑r) , uᵢ⊑r
    with static-gradual-syn (⊑.refl {A = Assms}) er⊑e D₁
  ... | ψr , dr , ψr⊑τ'
    with FC.extract-minimal f
           (record
             { expₛ = _ isSlice er⊑e
             ; type = _ isSlice ψr⊑τ'
             ; syn = dr
             ; valid = ⊑.trans {A = Typ} φ⊑τr
                 (syn-precision (γr .proof) (⊑.refl {A = Exp}) dr Dr)
             })
           (subst (_ ⊑e_)
             (sym (cong (λ x → x .↓) (FC.extract-σ f))) er⊑σ₁)
  ... | eqfix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) eqfix
  ... | eqσ₁ =
    ( ( ⊑def₂ (⊑.reflexive {A = Exp} eqσ₁) κ⊑r
      , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₁} {γ₂} {γr}
          (FC.extract-ctx-min f
            (subst (λ x → _ , γr .↓ ⊢ x ⇑ _) (sym eqσ₁) Dr)
            φ⊑τr (γr .proof))
          γ₂⊑r
      ) , σ⊑r
    ) , uᵢ⊑r

  extract-pos-least {Γ₀ = Γ₀} {Cls = adef₂ D₁ Cls}
      (minAdef₂ {τ' = τ'} {D₁ = D₁} {φ = φ} {γ₂ = γ₂}
                  {σ₁ = σ₁} {γ₁ = γ₁} c f)
      (record
        { pos-κ = (def er ⊢₂ _) isSlice ⊑def₂ er⊑e κr⊑C
        ; pos-γ = γr
        ; pos-outer = ur
        ; pos-focus-slice = fr
        ; pos-powered = n' , Γᶠ , φᶠ , focus⊑ ,
            aSub (sdef₂ Dr cls) conr , d
        })
      (⊑def₂ er⊑σ₁ κr⊑κ) σr⊑
    with syn-precision (γr .proof) er⊑e D₁ Dr
  ... | τr⊑τ'
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C)
             ((_ isSlice τr⊑τ') ∷ₛ γr) ⊥ₛ
             fr Γᶠ φᶠ focus⊑ (aSub cls ~?₂) d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , ⊑∷ φ⊑τr γ₂⊑r) , σ⊑r) , uᵢ⊑□
    with static-gradual-syn (⊑.refl {A = Assms}) er⊑e D₁
  ... | ψr , dr , ψr⊑τ'
    with FC.extract-minimal f
           (record
             { expₛ = _ isSlice er⊑e
             ; type = _ isSlice ψr⊑τ'
             ; syn = dr
             ; valid = ⊑.trans {A = Typ} φ⊑τr
                 (syn-precision (γr .proof) (⊑.refl {A = Exp}) dr Dr)
             })
           (subst (_ ⊑e_)
             (sym (cong (λ x → x .↓) (FC.extract-σ f))) er⊑σ₁)
  ... | eqfix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) eqfix
  ... | eqσ₁ =
    ( ( ⊑def₂ (⊑.reflexive {A = Exp} eqσ₁) κ⊑r
      , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₁} {γ₂} {γr}
          (FC.extract-ctx-min f
            (subst (λ x → _ , γr .↓ ⊢ x ⇑ _) (sym eqσ₁) Dr)
            φ⊑τr (γr .proof))
          γ₂⊑r
      ) , σ⊑r
    ) , subst (_⊑t (ur .↓)) (sym (⊑□-inv uᵢ⊑□)) ⊑□

  extract-pos-least {Cls = acase₀ Cls eq d₁ d₂} (minAcase₀ c)
      (record
        { pos-κ = (case₀ κr of ar · br) isSlice ⊑case₀ κr⊑C ar⊑ br⊑
        ; pos-γ = γr
        ; pos-outer = ur
        ; pos-focus-slice = fr
        ; pos-powered = n' , Γᶠ , φᶠ , focus⊑ ,
            acase₀ cls eqr d₁r d₂r , d
        })
      (⊑case₀ κr⊑κ ar⊑□ br⊑□) σr⊑
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) γr fr
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r =
    ((⊑case₀ κ⊑r ⊑□ ⊑□ , γ⊑r) , σ⊑r) ,
    ⊑ₛLat.⊥ₛ-min {A = Typ} ur

  extract-pos-least {Cls = acase₀ Cls eq d₁ d₂} (minAcase₀ c)
      (record
        { pos-κ = (case₀ κr of ar · br) isSlice ⊑case₀ κr⊑C ar⊑ br⊑
        ; pos-γ = γr
        ; pos-outer = ur
        ; pos-focus-slice = fr
        ; pos-powered = n' , Γᶠ , φᶠ , focus⊑ ,
            aSub (scase₀ cls eqr d₁r d₂r conr) con' , d
        })
      (⊑case₀ κr⊑κ ar⊑□ br⊑□) σr⊑
    with extract-least c
           (syn-rival Cls (_ isSlice κr⊑C) γr fr
             Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | (κ⊑r , γ⊑r) , σ⊑r =
    ((⊑case₀ κ⊑r ⊑□ ⊑□ , γ⊑r) , σ⊑r) ,
    ⊑ₛLat.⊥ₛ-min {A = Typ} ur

  extract-pos-least {Γ₀ = Γ₀} {Cls = acase₁ D₀ eq Cls d₂}
      (minAcase₁ {τ₀ = τ₀} {D₀ = D₀} {eq = eq} {φ₁ = φ₁}
                  {γ₁ = γ₁} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      (record
        { pos-κ = (case er of _ ·₁ _) isSlice ⊑case₁ er⊑e κr⊑C br⊑
        ; pos-γ = γr
        ; pos-outer = ur
        ; pos-focus-slice = fr
        ; pos-powered = n' , Γᶠ , φᶠ , focus⊑ ,
            acase₁ Dr eqr cls d₂r , d
        })
      (⊑case₁ er⊑σ₀ κr⊑κ br⊑□) σr⊑
    with syn-precision (γr .proof) er⊑e D₀ Dr
  ... | τr⊑τ₀
    with ⊔-+-⊑ τr⊑τ₀ eq
  ... | _ , _ , eqra , a⊑τ₁ , _
    with refl ← +-inj-fst (trans (sym eqra) eqr)
    with refl ← +-inj-snd (trans (sym eqra) eqr)
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C)
             ((_ isSlice a⊑τ₁) ∷ₛ γr) ur
             fr Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , ⊑∷ φ₁⊑a γ₁⊑r) , σ⊑r) , uᵢ⊑r
    with static-gradual-syn (⊑.refl {A = Assms}) er⊑e D₀
  ... | ψr , dr , ψr⊑τ₀
    with ⊔-+-⊑ ψr⊑τ₀ eq
  ... | af , _ , eqf , _ , _
    with ⊔-+-⊑
           (syn-precision (γr .proof) (⊑.refl {A = Exp}) dr Dr) eqf
  ... | _ , _ , eqf₂ , a⊑af , _
    with refl ← +-inj-fst (trans (sym eqf₂) eqr)
    with refl ← +-inj-snd (trans (sym eqf₂) eqr)
    with FC.extract-minimal f
           (record
             { expₛ = _ isSlice er⊑e
             ; type = _ isSlice ψr⊑τ₀
             ; syn = dr
             ; valid = unmatch+-min-least τ₀ eq φ₁ ⊥ₛ ψr⊑τ₀ eqf
                 (⊑.trans {A = Typ} φ₁⊑a a⊑af) ⊑□
             })
           (subst (_ ⊑e_)
             (sym (cong (λ x → x .↓) (FC.extract-σ f))) er⊑σ₀)
  ... | eqfix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) eqfix
  ... | eqσ₀ =
    ( ( ⊑case₁ (⊑.reflexive {A = Exp} eqσ₀) κ⊑r ⊑□
      , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₀} {γ₁} {γr}
          (FC.extract-ctx-min f
            (subst (λ x → _ , γr .↓ ⊢ x ⇑ _) (sym eqσ₀) Dr)
            (unmatch+-min-least τ₀ eq φ₁ ⊥ₛ τr⊑τ₀ eqr φ₁⊑a ⊑□)
            (γr .proof))
          γ₁⊑r
      ) , σ⊑r
    ) , uᵢ⊑r

  extract-pos-least {Γ₀ = Γ₀} {Cls = acase₁ D₀ eq Cls d₂}
      (minAcase₁ {τ₀ = τ₀} {D₀ = D₀} {eq = eq} {φ₁ = φ₁}
                  {γ₁ = γ₁} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      (record
        { pos-κ = (case er of _ ·₁ _) isSlice ⊑case₁ er⊑e κr⊑C br⊑
        ; pos-γ = γr
        ; pos-outer = ur
        ; pos-focus-slice = fr
        ; pos-powered = n' , Γᶠ , φᶠ , focus⊑ ,
            aSub (scase₁ Dr eqr cls d₂r conr) con' , d
        })
      (⊑case₁ er⊑σ₀ κr⊑κ br⊑□) σr⊑
    with syn-precision (γr .proof) er⊑e D₀ Dr
  ... | τr⊑τ₀
    with ⊔-+-⊑ τr⊑τ₀ eq
  ... | _ , _ , eqra , a⊑τ₁ , _
    with refl ← +-inj-fst (trans (sym eqra) eqr)
    with refl ← +-inj-snd (trans (sym eqra) eqr)
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C)
             ((_ isSlice a⊑τ₁) ∷ₛ γr) ⊥ₛ
             fr Γᶠ φᶠ focus⊑ (aSub cls ~?₂) d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , ⊑∷ φ₁⊑a γ₁⊑r) , σ⊑r) , uᵢ⊑□
    with static-gradual-syn (⊑.refl {A = Assms}) er⊑e D₀
  ... | ψr , dr , ψr⊑τ₀
    with ⊔-+-⊑ ψr⊑τ₀ eq
  ... | af , _ , eqf , _ , _
    with ⊔-+-⊑
           (syn-precision (γr .proof) (⊑.refl {A = Exp}) dr Dr) eqf
  ... | _ , _ , eqf₂ , a⊑af , _
    with refl ← +-inj-fst (trans (sym eqf₂) eqr)
    with refl ← +-inj-snd (trans (sym eqf₂) eqr)
    with FC.extract-minimal f
           (record
             { expₛ = _ isSlice er⊑e
             ; type = _ isSlice ψr⊑τ₀
             ; syn = dr
             ; valid = unmatch+-min-least τ₀ eq φ₁ ⊥ₛ ψr⊑τ₀ eqf
                 (⊑.trans {A = Typ} φ₁⊑a a⊑af) ⊑□
             })
           (subst (_ ⊑e_)
             (sym (cong (λ x → x .↓) (FC.extract-σ f))) er⊑σ₀)
  ... | eqfix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) eqfix
  ... | eqσ₀ =
    ( ( ⊑case₁ (⊑.reflexive {A = Exp} eqσ₀) κ⊑r ⊑□
      , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₀} {γ₁} {γr}
          (FC.extract-ctx-min f
            (subst (λ x → _ , γr .↓ ⊢ x ⇑ _) (sym eqσ₀) Dr)
            (unmatch+-min-least τ₀ eq φ₁ ⊥ₛ τr⊑τ₀ eqr φ₁⊑a ⊑□)
            (γr .proof))
          γ₁⊑r
      ) , σ⊑r
    ) , subst (_⊑t (ur .↓)) (sym (⊑□-inv uᵢ⊑□)) ⊑□

  extract-pos-least {Γ₀ = Γ₀} {Cls = acase₂ D₀ eq d₁ Cls}
      (minAcase₂ {τ₀ = τ₀} {D₀ = D₀} {eq = eq} {φ₂ = φ₂}
                  {γ₂ = γ₂} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      (record
        { pos-κ = (case er of₂ _ · _) isSlice ⊑case₂ er⊑e ar⊑ κr⊑C
        ; pos-γ = γr
        ; pos-outer = ur
        ; pos-focus-slice = fr
        ; pos-powered = n' , Γᶠ , φᶠ , focus⊑ ,
            acase₂ Dr eqr d₁r cls , d
        })
      (⊑case₂ er⊑σ₀ ar⊑□ κr⊑κ) σr⊑
    with syn-precision (γr .proof) er⊑e D₀ Dr
  ... | τr⊑τ₀
    with ⊔-+-⊑ τr⊑τ₀ eq
  ... | _ , _ , eqra , _ , b⊑τ₂
    with refl ← +-inj-fst (trans (sym eqra) eqr)
    with refl ← +-inj-snd (trans (sym eqra) eqr)
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C)
             ((_ isSlice b⊑τ₂) ∷ₛ γr) ur
             fr Γᶠ φᶠ focus⊑ cls d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , ⊑∷ φ₂⊑b γ₂⊑r) , σ⊑r) , uᵢ⊑r
    with static-gradual-syn (⊑.refl {A = Assms}) er⊑e D₀
  ... | ψr , dr , ψr⊑τ₀
    with ⊔-+-⊑ ψr⊑τ₀ eq
  ... | _ , bf , eqf , _ , _
    with ⊔-+-⊑
           (syn-precision (γr .proof) (⊑.refl {A = Exp}) dr Dr) eqf
  ... | _ , _ , eqf₂ , _ , b⊑bf
    with refl ← +-inj-fst (trans (sym eqf₂) eqr)
    with refl ← +-inj-snd (trans (sym eqf₂) eqr)
    with FC.extract-minimal f
           (record
             { expₛ = _ isSlice er⊑e
             ; type = _ isSlice ψr⊑τ₀
             ; syn = dr
             ; valid = unmatch+-min-least τ₀ eq ⊥ₛ φ₂ ψr⊑τ₀ eqf
                 ⊑□ (⊑.trans {A = Typ} φ₂⊑b b⊑bf)
             })
           (subst (_ ⊑e_)
             (sym (cong (λ x → x .↓) (FC.extract-σ f))) er⊑σ₀)
  ... | eqfix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) eqfix
  ... | eqσ₀ =
    ( ( ⊑case₂ (⊑.reflexive {A = Exp} eqσ₀) ⊑□ κ⊑r
      , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₀} {γ₂} {γr}
          (FC.extract-ctx-min f
            (subst (λ x → _ , γr .↓ ⊢ x ⇑ _) (sym eqσ₀) Dr)
            (unmatch+-min-least τ₀ eq ⊥ₛ φ₂ τr⊑τ₀ eqr ⊑□ φ₂⊑b)
            (γr .proof))
          γ₂⊑r
      ) , σ⊑r
    ) , uᵢ⊑r

  extract-pos-least {Γ₀ = Γ₀} {Cls = acase₂ D₀ eq d₁ Cls}
      (minAcase₂ {τ₀ = τ₀} {D₀ = D₀} {eq = eq} {φ₂ = φ₂}
                  {γ₂ = γ₂} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      (record
        { pos-κ = (case er of₂ _ · _) isSlice ⊑case₂ er⊑e ar⊑ κr⊑C
        ; pos-γ = γr
        ; pos-outer = ur
        ; pos-focus-slice = fr
        ; pos-powered = n' , Γᶠ , φᶠ , focus⊑ ,
            aSub (scase₂ Dr eqr d₁r cls conr) con' , d
        })
      (⊑case₂ er⊑σ₀ ar⊑□ κr⊑κ) σr⊑
    with syn-precision (γr .proof) er⊑e D₀ Dr
  ... | τr⊑τ₀
    with ⊔-+-⊑ τr⊑τ₀ eq
  ... | _ , _ , eqra , _ , b⊑τ₂
    with refl ← +-inj-fst (trans (sym eqra) eqr)
    with refl ← +-inj-snd (trans (sym eqra) eqr)
    with extract-pos-least c
           (pos-rival Cls (_ isSlice κr⊑C)
             ((_ isSlice b⊑τ₂) ∷ₛ γr) ⊥ₛ
             fr Γᶠ φᶠ focus⊑ (aSub cls ~?₂) d)
           κr⊑κ σr⊑
  ... | ((κ⊑r , ⊑∷ φ₂⊑b γ₂⊑r) , σ⊑r) , uᵢ⊑□
    with static-gradual-syn (⊑.refl {A = Assms}) er⊑e D₀
  ... | ψr , dr , ψr⊑τ₀
    with ⊔-+-⊑ ψr⊑τ₀ eq
  ... | _ , bf , eqf , _ , _
    with ⊔-+-⊑
           (syn-precision (γr .proof) (⊑.refl {A = Exp}) dr Dr) eqf
  ... | _ , _ , eqf₂ , _ , b⊑bf
    with refl ← +-inj-fst (trans (sym eqf₂) eqr)
    with refl ← +-inj-snd (trans (sym eqf₂) eqr)
    with FC.extract-minimal f
           (record
             { expₛ = _ isSlice er⊑e
             ; type = _ isSlice ψr⊑τ₀
             ; syn = dr
             ; valid = unmatch+-min-least τ₀ eq ⊥ₛ φ₂ ψr⊑τ₀ eqf
                 ⊑□ (⊑.trans {A = Typ} φ₂⊑b b⊑bf)
             })
           (subst (_ ⊑e_)
             (sym (cong (λ x → x .↓) (FC.extract-σ f))) er⊑σ₀)
  ... | eqfix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) eqfix
  ... | eqσ₀ =
    ( ( ⊑case₂ (⊑.reflexive {A = Exp} eqσ₀) ⊑□ κ⊑r
      , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₀} {γ₂} {γr}
          (FC.extract-ctx-min f
            (subst (λ x → _ , γr .↓ ⊢ x ⇑ _) (sym eqσ₀) Dr)
            (unmatch+-min-least τ₀ eq ⊥ₛ φ₂ τr⊑τ₀ eqr ⊑□ φ₂⊑b)
            (γr .proof))
          γ₂⊑r
      ) , σ⊑r
    ) , subst (_⊑t (ur .↓)) (sym (⊑□-inv uᵢ⊑□)) ⊑□

  extract-pos-minimal : ∀ {n Γ₀ C n_f Γ e τ τₚ}
                          {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n_f , Γ [ ⇒mode τ ]}
                          {D : n_f , Γ ⊢ e ⇑ τ}
                          {u : ⌊ τ ⌋} {κ : ⌊ C ⌋} {σ : ⌊ e ⌋}
                          {uₒ : ⌊ τₚ ⌋} {γ : ⌊ Γ₀ ⌋}
                      → (c : Cls , D ◂ u ⤳ κ ∣ σ ⇓ uₒ ⊣ γ)
                      → IsMinimal (extract-pos c)
  extract-pos-minimal c r (((κr⊑ , γr⊑) , σr⊑) , ur⊑)
    with extract-pos-least c r κr⊑
           (subst (SS._↓σ (r .pos-focus-slice) ⊑e_)
             (focus-pos-σ c) σr⊑)
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
