open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsEquivalence; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; subst; sym; cong; trans)
open import Data.List using (map; _∷_; length)
open import Data.List.Properties using (length-map)
open import Core
open import Semantics.Statics
open import Core.Typ.WellFormedness using (wf□)
open import Core.Typ.Consistency using (~?₁; ~?₂)
open import Core.Typ.Properties using (⊔-⇒-⊑; ⊔-×-⊑; ⊔-+-⊑; ⊔-∀-⊑; ⊔-ann-⇒-⊑; sub-⊑; ⊔t-zeroᵣ; ⊔t-zeroₗ)
open import Core.Typ.Lattice
open ~ using (⊔-ub₁; ⊔-ub₂)
open import Core.Typ.Substitution using (shift)

module Slicing.Analysis.Analysis where

private
  shift-□Assm : ∀ (a n : ℕ) → shiftΓ a (□Assm n) ≡ □Assm n
  shift-□Assm a zero    = refl
  shift-□Assm a (suc n) = cong (Typ.□ ∷_) (shift-□Assm a n)

-- Slice at a synthesising outer position, where the focus is analysed.
record AnaSlice {n : ℕ} {Γ₀ : Assms} {C : Ctx} {n' : ℕ} {Γ : Assms} {τ τ_p : Typ}
                (_ : n , Γ₀ ⊢ C at synPos τ_p ▷ n' , Γ [ ⇐mode τ ]) (υ : ⌊ τ ⌋) : Set where
  field
    κ     : ⌊ C ⌋
    γ     : ⌊ Γ₀ ⌋
    type  : ⌊ τ_p ⌋
    focus : ⌊ τ ⌋
    focus⊒ : υ ⊑ₛ focus
    valid : ∃[ n'' ] ∃[ Γ' ]
              n , γ .↓ ⊢ κ .↓ at synPos (type .↓) ▷ n'' , Γ' [ ⇐mode (focus .↓) ]
open AnaSlice public

-- Slice at an analysing outer position, jointly minimised over υ_outer.
record AnaPosSlice {n : ℕ} {Γ₀ : Assms} {C : Ctx} {n' : ℕ} {Γ : Assms} {τ τ_p : Typ}
                   (_ : n , Γ₀ ⊢ C at anaPos τ_p ▷ n' , Γ [ ⇐mode τ ]) (υ : ⌊ τ ⌋) : Set where
  field
    κ       : ⌊ C ⌋
    γ       : ⌊ Γ₀ ⌋
    υ_outer : ⌊ τ_p ⌋
    focus   : ⌊ τ ⌋
    focus⊒  : υ ⊑ₛ focus
    valid   : ∃[ n'' ] ∃[ Γ' ]
                n , γ .↓ ⊢ κ .↓ at anaPos (υ_outer .↓) ▷ n'' , Γ' [ ⇐mode (focus .↓) ]
open AnaPosSlice public
  renaming (κ to ana-κ; γ to ana-γ; υ_outer to ana-υ_outer;
            focus to ana-focus; focus⊒ to ana-focus⊒; valid to ana-valid)

private
  _⊑ana_ : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ₁ υ₂} →
             AnaSlice Cls υ₁ → AnaSlice Cls υ₂ → Set
  _⊑ana_ s₁ s₂ = s₁ .κ ⊑ₛ s₂ .κ ∧ s₁ .γ ⊑ₛ s₂ .γ

  _≈ana_ : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ₁ υ₂} →
              AnaSlice Cls υ₁ → AnaSlice Cls υ₂ → Set
  _≈ana_ s₁ s₂ = s₁ .κ ≈ₛ s₂ .κ ∧ s₁ .γ ≈ₛ s₂ .γ

  _≈ana?_ : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ}
            → (s₁ s₂ : AnaSlice Cls υ) → Relation.Nullary.Dec (s₁ ≈ana s₂)
  s₁ ≈ana? s₂ with s₁ .κ ≈ₛ? s₂ .κ | s₁ .γ ≈ₛ? s₂ .γ
  ...            | yes p          | yes q = yes (p , q)
  ...            | no ¬p          | _     = no λ where (p , _) → ¬p p
  ...            | _              | no ¬q = no λ where (_ , q) → ¬q q

  _⊑ana?_ : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ}
            → (s₁ s₂ : AnaSlice Cls υ) → Relation.Nullary.Dec (s₁ ⊑ana s₂)
  s₁ ⊑ana? s₂ with s₁ .κ ⊑ₛ? s₂ .κ | s₁ .γ ⊑ₛ? s₂ .γ
  ...            | yes p          | yes q = yes (p , q)
  ...            | no ¬p          | _     = no λ where (p , _) → ¬p p
  ...            | _              | no ¬q = no λ where (_ , q) → ¬q q

  ⊑ana-isDecPartialOrder : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ} →
                              IsDecPartialOrder (_≈ana_ {Cls = Cls} {υ₁ = υ} {υ₂ = υ}) _⊑ana_
  ⊑ana-isDecPartialOrder = record
                           { isPartialOrder = record
                                              { isPreorder = isPreorder
                                              ; antisym = λ (p₁ , q₁) (p₂ , q₂) → ⊑.antisym {Ctx} p₁ p₂ , ⊑.antisym {Assms} q₁ q₂
                                              }
                           ; _≟_  = _≈ana?_
                           ; _≤?_ = _⊑ana?_
                           }
    where isPreorder = record
                       { isEquivalence = record
                           { refl  = λ {_} → refl , refl
                           ; sym   = λ where (refl , refl) → refl , refl
                           ; trans = λ where (refl , refl) (refl , refl) → refl , refl
                           }
                       ; reflexive  = λ where (refl , refl) → ⊑.refl {Ctx} , ⊑.refl {Assms}
                       ; trans = λ (p₁ , q₁) (p₂ , q₂) → ⊑.trans {Ctx} p₁ p₂ , ⊑.trans {Assms} q₁ q₂
                       }

instance
  anaSlice-precision : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ} →
                         HasPrecision (AnaSlice Cls υ)
  anaSlice-precision = record
    { _≈_               = _≈ana_
    ; _⊑_               = _⊑ana_
    ; isDecPartialOrder = ⊑ana-isDecPartialOrder
    }

private
  _⊑ana-pos_ : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ₁ υ₂} →
                 AnaPosSlice Cls υ₁ → AnaPosSlice Cls υ₂ → Set
  _⊑ana-pos_ s₁ s₂ = ana-κ s₁ ⊑ₛ ana-κ s₂ ∧ ana-γ s₁ ⊑ₛ ana-γ s₂ ∧ ana-υ_outer s₁ ⊑ₛ ana-υ_outer s₂

  _≈ana-pos_ : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ₁ υ₂} →
                 AnaPosSlice Cls υ₁ → AnaPosSlice Cls υ₂ → Set
  _≈ana-pos_ s₁ s₂ = ana-κ s₁ ≈ₛ ana-κ s₂ ∧ ana-γ s₁ ≈ₛ ana-γ s₂ ∧ ana-υ_outer s₁ ≈ₛ ana-υ_outer s₂

  _≈ana-pos?_ : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ}
                → (s₁ s₂ : AnaPosSlice Cls υ) → Relation.Nullary.Dec (s₁ ≈ana-pos s₂)
  s₁ ≈ana-pos? s₂ with ana-κ s₁ ≈ₛ? ana-κ s₂ | ana-γ s₁ ≈ₛ? ana-γ s₂ | ana-υ_outer s₁ ≈ₛ? ana-υ_outer s₂
  ...                | yes p                  | yes q                  | yes r = yes (p , q , r)
  ...                | no ¬p                  | _                      | _     = no λ where (p , _ , _) → ¬p p
  ...                | _                      | no ¬q                  | _     = no λ where (_ , q , _) → ¬q q
  ...                | _                      | _                      | no ¬r = no λ where (_ , _ , r) → ¬r r

  _⊑ana-pos?_ : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ}
                → (s₁ s₂ : AnaPosSlice Cls υ) → Relation.Nullary.Dec (s₁ ⊑ana-pos s₂)
  s₁ ⊑ana-pos? s₂ with ana-κ s₁ ⊑ₛ? ana-κ s₂ | ana-γ s₁ ⊑ₛ? ana-γ s₂ | ana-υ_outer s₁ ⊑ₛ? ana-υ_outer s₂
  ...                | yes p                  | yes q                  | yes r = yes (p , q , r)
  ...                | no ¬p                  | _                      | _     = no λ where (p , _ , _) → ¬p p
  ...                | _                      | no ¬q                  | _     = no λ where (_ , q , _) → ¬q q
  ...                | _                      | _                      | no ¬r = no λ where (_ , _ , r) → ¬r r

  ⊑ana-pos-isDecPartialOrder : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ} →
                                  IsDecPartialOrder (_≈ana-pos_ {Cls = Cls} {υ₁ = υ} {υ₂ = υ}) _⊑ana-pos_
  ⊑ana-pos-isDecPartialOrder = record
                               { isPartialOrder = record
                                                  { isPreorder = isPreorder
                                                  ; antisym = λ (p₁ , q₁ , r₁) (p₂ , q₂ , r₂) →
                                                                ⊑.antisym {Ctx} p₁ p₂
                                                              , ⊑.antisym {Assms} q₁ q₂
                                                              , ⊑.antisym {Typ} r₁ r₂
                                                  }
                               ; _≟_  = _≈ana-pos?_
                               ; _≤?_ = _⊑ana-pos?_
                               }
    where isPreorder = record
                       { isEquivalence = record
                           { refl  = λ {_} → refl , refl , refl
                           ; sym   = λ where (refl , refl , refl) → refl , refl , refl
                           ; trans = λ where (refl , refl , refl) (refl , refl , refl) → refl , refl , refl
                           }
                       ; reflexive  = λ where (refl , refl , refl) → ⊑.refl {Ctx} , ⊑.refl {Assms} , ⊑.refl {Typ}
                       ; trans = λ (p₁ , q₁ , r₁) (p₂ , q₂ , r₂) →
                                  ⊑.trans {Ctx} p₁ p₂
                                , ⊑.trans {Assms} q₁ q₂
                                , ⊑.trans {Typ} r₁ r₂
                       }

instance
  anaPosSlice-precision : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ} →
                            HasPrecision (AnaPosSlice Cls υ)
  anaPosSlice-precision = record
    { _≈_               = _≈ana-pos_
    ; _⊑_               = _⊑ana-pos_
    ; isDecPartialOrder = ⊑ana-pos-isDecPartialOrder
    }

mutual
  ⊥-ana-valid : ∀ {n Γ₀ C n' Γ τ τ_p}
              → (Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n' , Γ [ ⇐mode τ ])
              → ∃[ n'' ] ∃[ Γ' ] ∃[ τp' ]
                  (τp' ⊑ τ_p) ∧
                  (n , (⊥ₛ {a = Γ₀}) .↓ ⊢ (⊥ₛ {a = C}) .↓ at synPos τp' ▷ n'' , Γ' [ ⇐mode ((⊥ₛ {a = τ}) .↓) ])

  ⊥-ana-pos-valid : ∀ {n Γ₀ C n' Γ τ τ_p}
                  → (Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n' , Γ [ ⇐mode τ ])
                  → ∃[ n'' ] ∃[ Γ' ]
                      n , (⊥ₛ {a = Γ₀}) .↓ ⊢ (⊥ₛ {a = C}) .↓ at anaPos ((⊥ₛ {a = τ_p}) .↓) ▷ n'' , Γ' [ ⇐mode ((⊥ₛ {a = τ}) .↓) ]

  ⊥-ana-valid (sλ: wf Cls') with ⊥-ana-valid Cls'
  ... | _ , _ , τb' , τb'⊑ , Cls'-lifted =
        _ , _ , _ , ⊑⇒ ⊑□ τb'⊑ , sλ: wf□ Cls'-lifted

  ⊥-ana-valid (s∘₁ Cls' eq d₂) with ⊥-ana-valid Cls'
  ... | _ , _ , τa' , τa'⊑ , Cls'-lifted
    with ⊔-⇒-⊑ τa'⊑ eq
  ... | _ , _ , eq-lifted , _ , pb =
        _ , _ , _ , pb , s∘₁ Cls'-lifted eq-lifted (⇓Sub ⇑□ ~?₁)

  ⊥-ana-valid (s∘₂ D eq Cls') with ⊥-ana-pos-valid Cls'
  ... | _ , _ , Cls'-lifted =
        _ , _ , _ , ⊑□ , s∘₂ ⇑□ refl Cls'-lifted

  ⊥-ana-valid (s<>₁ Cls' eq wf) with ⊥-ana-valid Cls'
  ... | _ , _ , τ' , τ'⊑ , Cls'-lifted
    with ⊔-∀-⊑ τ'⊑ eq
  ... | _ , eq-lifted , p =
        _ , _ , _ , sub-⊑ zero ⊑□ p , s<>₁ Cls'-lifted eq-lifted wf□

  ⊥-ana-valid (s&₁ Cls' d₂) with ⊥-ana-valid Cls'
  ... | _ , _ , τ' , τ'⊑ , Cls'-lifted =
        _ , _ , _ , ⊑× τ'⊑ ⊑□ , s&₁ Cls'-lifted ⇑□

  ⊥-ana-valid (s&₂ d₁ Cls') with ⊥-ana-valid Cls'
  ... | _ , _ , τ' , τ'⊑ , Cls'-lifted =
        _ , _ , _ , ⊑× ⊑□ τ'⊑ , s&₂ ⇑□ Cls'-lifted

  ⊥-ana-valid (sι₁ Cls') with ⊥-ana-valid Cls'
  ... | _ , _ , τ' , τ'⊑ , Cls'-lifted =
        _ , _ , _ , ⊑+ τ'⊑ ⊑□ , sι₁ Cls'-lifted

  ⊥-ana-valid (sι₂ Cls') with ⊥-ana-valid Cls'
  ... | _ , _ , τ' , τ'⊑ , Cls'-lifted =
        _ , _ , _ , ⊑+ ⊑□ τ'⊑ , sι₂ Cls'-lifted

  ⊥-ana-valid (scase₁ D eq Cls' d₂ con) with ⊥-ana-valid Cls'
  ... | _ , _ , τ₁' , τ₁'⊑ , Cls'-lifted =
        _ , _ , _
          , subst (_⊑ _) (sym (⊔t-zeroᵣ {τ₁'})) (⊑.trans {A = Typ} τ₁'⊑ (⊔-ub₁ con))
          , scase₁ ⇑□ refl Cls'-lifted ⇑□ ~?₁

  ⊥-ana-valid (scase₂ D eq d₁ Cls' con) with ⊥-ana-valid Cls'
  ... | _ , _ , τ₂' , τ₂'⊑ , Cls'-lifted =
        _ , _ , _
          , subst (_⊑ _) (sym (⊔t-zeroₗ {τ₂'})) (⊑.trans {A = Typ} τ₂'⊑ (⊔-ub₂ con))
          , scase₂ ⇑□ refl ⇑□ Cls'-lifted ~?₂

  ⊥-ana-valid (sπ₁ Cls' eq) with ⊥-ana-valid Cls'
  ... | _ , _ , τ' , τ'⊑ , Cls'-lifted
    with ⊔-×-⊑ τ'⊑ eq
  ... | _ , _ , eq-lifted , pa , _ =
        _ , _ , _ , pa , sπ₁ Cls'-lifted eq-lifted

  ⊥-ana-valid (sπ₂ Cls' eq) with ⊥-ana-valid Cls'
  ... | _ , _ , τ' , τ'⊑ , Cls'-lifted
    with ⊔-×-⊑ τ'⊑ eq
  ... | _ , _ , eq-lifted , _ , pb =
        _ , _ , _ , pb , sπ₂ Cls'-lifted eq-lifted

  ⊥-ana-valid {Γ₀ = Γ₀} (sΛ Cls') with ⊥-ana-valid Cls'
  ... | _ , _ , τ' , τ'⊑ , Cls'-lifted =
        _ , _ , _ , ⊑∀ τ'⊑
          , sΛ (subst (λ Γ' → _ , Γ' ⊢ _ at synPos _ ▷ _ , _ [ ⇐mode _ ])
                      (trans (cong □Assm (length-map (shift 0 1) Γ₀))
                             (sym (shift-□Assm 1 (length Γ₀))))
                      Cls'-lifted)

  ⊥-ana-valid (sdef₁ Cls' d₂) with ⊥-ana-valid Cls'
  ... | _ , _ , _ , _ , Cls'-lifted =
        _ , _ , _ , ⊑□ , sdef₁ Cls'-lifted ⇑□

  ⊥-ana-valid (sdef₂ D Cls') with ⊥-ana-valid Cls'
  ... | _ , _ , _ , τ'⊑ , Cls'-lifted =
        _ , _ , _ , τ'⊑ , sdef₂ ⇑□ Cls'-lifted

  ⊥-ana-pos-valid a○ = _ , _ , a○

  ⊥-ana-pos-valid (aSub Cls' c) with ⊥-ana-valid Cls'
  ... | _ , _ , _ , _ , Cls'-lifted =
        _ , _ , aSub Cls'-lifted ~?₂

  ⊥-ana-pos-valid (aλ: c eq wf Cls') with ⊥-ana-pos-valid Cls'
  ... | _ , _ , Cls'-lifted =
        _ , _ , aλ: ~?₂ refl wf□ Cls'-lifted

  ⊥-ana-pos-valid (aλ⇒ eq Cls') with ⊥-ana-pos-valid Cls'
  ... | _ , _ , Cls'-lifted =
        _ , _ , aλ⇒ refl Cls'-lifted

  ⊥-ana-pos-valid (aι₁ eq Cls') with ⊥-ana-pos-valid Cls'
  ... | _ , _ , Cls'-lifted =
        _ , _ , aι₁ refl Cls'-lifted

  ⊥-ana-pos-valid (aι₂ eq Cls') with ⊥-ana-pos-valid Cls'
  ... | _ , _ , Cls'-lifted =
        _ , _ , aι₂ refl Cls'-lifted

  ⊥-ana-pos-valid (a&₁ eq Cls' d₂) with ⊥-ana-pos-valid Cls'
  ... | _ , _ , Cls'-lifted =
        _ , _ , a&₁ refl Cls'-lifted (⇓Sub ⇑□ ~?₁)

  ⊥-ana-pos-valid (a&₂ eq d₁ Cls') with ⊥-ana-pos-valid Cls'
  ... | _ , _ , Cls'-lifted =
        _ , _ , a&₂ refl (⇓Sub ⇑□ ~?₁) Cls'-lifted

  ⊥-ana-pos-valid (acase₁ D eq Cls' d₂) with ⊥-ana-pos-valid Cls'
  ... | _ , _ , Cls'-lifted =
        _ , _ , acase₁ ⇑□ refl Cls'-lifted (⇓Sub ⇑□ ~?₁)

  ⊥-ana-pos-valid (acase₂ D eq d₁ Cls') with ⊥-ana-pos-valid Cls'
  ... | _ , _ , Cls'-lifted =
        _ , _ , acase₂ ⇑□ refl (⇓Sub ⇑□ ~?₁) Cls'-lifted

  ⊥-ana-pos-valid (adef₁ Cls' d₂) with ⊥-ana-valid Cls'
  ... | _ , _ , _ , _ , Cls'-lifted =
        _ , _ , adef₁ Cls'-lifted (⇓Sub ⇑□ ~?₁)

  ⊥-ana-pos-valid (adef₂ D Cls') with ⊥-ana-pos-valid Cls'
  ... | _ , _ , Cls'-lifted =
        _ , _ , adef₂ ⇑□ Cls'-lifted

⊥-ana : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n' , Γ [ ⇐mode τ ]} → AnaSlice Cls ⊥ₛ
⊥-ana {τ = τ} {Cls = Cls} with ⊥-ana-valid Cls
... | n'' , Γ' , _ , τp'⊑ , Cls'  =
      record { κ = ⊥ₛ ; γ = ⊥ₛ ; type = _ isSlice τp'⊑ ; focus = ⊥ₛ {a = τ} ; focus⊒ = ⊑ₛ.refl {A = Typ} {x = ⊥ₛ {a = τ}} ; valid = n'' , Γ' , Cls' }

⊥-ana-pos : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n' , Γ [ ⇐mode τ ]} → AnaPosSlice Cls ⊥ₛ
⊥-ana-pos {τ = τ} {Cls = Cls} = record { κ = ⊥ₛ ; γ = ⊥ₛ ; υ_outer = ⊥ₛ ; focus = ⊥ₛ {a = τ} ; focus⊒ = ⊑ₛ.refl {A = Typ} {x = ⊥ₛ {a = τ}} ; valid = ⊥-ana-pos-valid Cls }

⊤-ana : ∀ {n Γ₀ C n' Γ τ τ_p} (Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n' , Γ [ ⇐mode τ ]) → AnaSlice Cls ⊤ₛ
⊤-ana Cls = record { κ = ⊤ₛ ; γ = ⊤ₛ ; type = ⊤ₛ ; focus = ⊤ₛ ; focus⊒ = ⊑ₛ.refl {A = Typ} {x = ⊤ₛ} ; valid = _ , _ , Cls }

⊤-ana-pos : ∀ {n Γ₀ C n' Γ τ τ_p} (Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n' , Γ [ ⇐mode τ ]) → AnaPosSlice Cls ⊤ₛ
⊤-ana-pos Cls = record { κ = ⊤ₛ ; γ = ⊤ₛ ; υ_outer = ⊤ₛ ; focus = ⊤ₛ ; focus⊒ = ⊑ₛ.refl {A = Typ} {x = ⊤ₛ} ; valid = _ , _ , Cls }

IsMinimal : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ} → AnaSlice Cls υ → Set
IsMinimal {Cls = Cls} {υ = υ} s = ∀ (s' : AnaSlice Cls υ) → s' ⊑ana s → s ⊑ana s'

IsMinimalPos : ∀ {n Γ₀ C n' Γ τ τ_p} {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n' , Γ [ ⇐mode τ ]} {υ} → AnaPosSlice Cls υ → Set
IsMinimalPos {Cls = Cls} {υ = υ} s = ∀ (s' : AnaPosSlice Cls υ) → s' ⊑ana-pos s → s ⊑ana-pos s'

MinAnaSlice : ∀ {n Γ₀ C n' Γ τ τ_p} → (Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n' , Γ [ ⇐mode τ ]) → ⌊ τ ⌋ → Set
MinAnaSlice Cls υ = Σ[ s ∈ AnaSlice Cls υ ] IsMinimal s

MinAnaPosSlice : ∀ {n Γ₀ C n' Γ τ τ_p} → (Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n' , Γ [ ⇐mode τ ]) → ⌊ τ ⌋ → Set
MinAnaPosSlice Cls υ = Σ[ s ∈ AnaPosSlice Cls υ ] IsMinimalPos s
