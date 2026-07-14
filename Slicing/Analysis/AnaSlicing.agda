open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Core
open import Core.Typ.Lift using (_⇒ₛ_; _×ₛ_; _+ₛ_; ∀·ₛ;
                                  match⇒ₛ; dom⇒ₛ; cod⇒ₛ;
                                  match×ₛ; fst×ₛ'; snd×ₛ;
                                  match+ₛ; fst+ₛ'; snd+ₛ';
                                  match∀ₛ; body∀ₛ;
                                  unmatch⇒-min; unmatch×-min; unmatch+-min;
                                  unmatch⇒-min-cov; unmatch×-min-cov; unmatch+-min-cov;
                                  unmatch⇒-min-mono; unmatch×-min-mono; unmatch+-min-mono;
                                  unmatch⇒-min-least; unmatch×-min-least; unmatch+-min-least;
                                  unmatch⇒-min-□; unmatch×-min-□; unmatch+-min-□;
                                  ann-⇒-plain)
open import Core.Typ.Properties using (⊔-⇒-⊑; ⊔-+-⊑; ⊔-×-⊑; ⊔-∀-⊑; ⊔-mono-⊑; sub-⊑; ⊔-ann-⇒-⊑)
open import Core.Typ.Precision using (~-⊑-down)
open import Core.Typ.WellFormedness using (wf□; wf-⊑)
open import Core.Typ.Consistency using (~?₁; ~?₂)
open import Core.Assms.Precision using (shiftΓ-⊑; unshiftΓ-⊑; unshiftΓ-shiftΓ)
open import Semantics.Statics
open import Semantics.Graduality using (mode-⊑; ⇐mode-⊑; ⇒mode-⊑;
                                          static-gradual-syn; static-gradual-ana;
                                          static-gradual-syn-cls; static-gradual-ana-cls;
                                          syn-unicity; syn-precision)
open import Slicing.Synthesis.FixedAssmsSynthesis using (FixedAssmsSynSlice; _⇑_∈_⊒_)
import Slicing.Synthesis.FixedAssmsCalc as FC
open import Slicing.Analysis.Analysis
open import Slicing.Analysis.AnaSliceCalc

-- Soundness and minimality of the analysis slice calculi: bounded upward
-- lifts (lift-syn, lift-pos), extraction to AnaSlice / AnaPosSlice, and
-- minimality of extraction.  Dissertation §8.6.
module Slicing.Analysis.AnaSlicing where

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

  ⇒-inj-fst : ∀ {a b c d : Typ} → a ⇒ b ≡ c ⇒ d → a ≡ c
  ⇒-inj-fst refl = refl

  ⊑□-inv : ∀ {x : Typ} → x ⊑t □ → x ≡ □
  ⊑□-inv ⊑□ = refl

-- A sliced classification's root type is below any less-sliced one.
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

-- A classification of a context slice at an analysis position with a checked focus is
-- backed by a synthesis-position classification with the same focus: the
-- pure-analysis path to a○ is impossible since the original classification's
-- mode is ⇐mode (its path never ends at s○).
ana-cls-to-syn : ∀ {n Γ Γ₀ κ C n_f Γ_f τ_a τ_m n_f₀ Γ_f₀ τ_p₀ m₀}
  → Γ ⊑a Γ₀ → κ ⊑c C
  → mode-⊑ (⇐mode τ_m) m₀
  → n , Γ₀ ⊢ C at synPos τ_p₀ ▷ n_f₀ , Γ_f₀ [ m₀ ]
  → n , Γ ⊢ κ at anaPos τ_a ▷ n_f , Γ_f [ ⇐mode τ_m ]
  → ∃[ ψ ] ∃[ n' ] ∃[ Γ' ] (n , Γ ⊢ κ at synPos ψ ▷ n' , Γ' [ ⇐mode τ_m ])

ana-cls-to-syn Γ⊑ ⊑○ () s○ a○

ana-cls-to-syn Γ⊑ (⊑λu _) m⊑ () (aλ⇒ _ _)

ana-cls-to-syn Γ⊑ κ⊑ m⊑ Cls₀ (aSub scls con) =
  _ , _ , _ , scls

ana-cls-to-syn Γ⊑ (⊑λ t⊑τa κ₁⊑) m⊑ (sλ: wf₀ cls₀) (aλ: con_r eq_r wf_r acls')
  with ana-cls-to-syn (⊑∷ t⊑τa Γ⊑) κ₁⊑ m⊑ cls₀ acls'
... | _ , _ , _ , cls₁ =
      _ , _ , _ , sλ: wf_r cls₁

ana-cls-to-syn Γ⊑ (⊑ι₁ κ₁⊑) m⊑ (sι₁ cls₀) (aι₁ eq_r acls')
  with ana-cls-to-syn Γ⊑ κ₁⊑ m⊑ cls₀ acls'
... | _ , _ , _ , cls₁ =
      _ , _ , _ , sι₁ cls₁

ana-cls-to-syn Γ⊑ (⊑ι₂ κ₁⊑) m⊑ (sι₂ cls₀) (aι₂ eq_r acls')
  with ana-cls-to-syn Γ⊑ κ₁⊑ m⊑ cls₀ acls'
... | _ , _ , _ , cls₁ =
      _ , _ , _ , sι₂ cls₁

ana-cls-to-syn Γ⊑ (⊑&₁ κ₁⊑ σ₂⊑) m⊑ (s&₁ cls₀ d₀) (a&₁ eq_r acls' d_r)
  with ana-cls-to-syn Γ⊑ κ₁⊑ m⊑ cls₀ acls'
     | static-gradual-syn Γ⊑ σ₂⊑ d₀
... | _ , _ , _ , cls₁ | _ , d₂' , _ =
      _ , _ , _ , s&₁ cls₁ d₂'

ana-cls-to-syn Γ⊑ (⊑&₂ σ₁⊑ κ₁⊑) m⊑ (s&₂ d₀ cls₀) (a&₂ eq_r d_r acls')
  with ana-cls-to-syn Γ⊑ κ₁⊑ m⊑ cls₀ acls'
     | static-gradual-syn Γ⊑ σ₁⊑ d₀
... | _ , _ , _ , cls₁ | _ , d₁' , _ =
      _ , _ , _ , s&₂ d₁' cls₁

ana-cls-to-syn Γ⊑ (⊑case₁ σ₀⊑ κ₁⊑ σ₂⊑) m⊑ (scase₁ D₀ eq₀ cls₀ d₀ con₀) (acase₁ D_r eq_r acls' d_r)
  with static-gradual-syn Γ⊑ σ₀⊑ D₀
... | _ , D₀' , τ₀⊑
  with refl ← syn-unicity D_r D₀'
  with ⊔-+-⊑ τ₀⊑ eq₀
... | _ , _ , eq'' , pa , pb
  with refl ← +-inj-fst (trans (sym eq'') eq_r)
  with refl ← +-inj-snd (trans (sym eq'') eq_r)
  with ana-cls-to-syn (⊑∷ pa Γ⊑) κ₁⊑ m⊑ cls₀ acls'
     | static-gradual-syn (⊑∷ pb Γ⊑) σ₂⊑ d₀
... | _ , _ , _ , cls₁ | _ , d₂' , ϕ₂⊑ =
      _ , _ , _ ,
      scase₁ D_r eq_r cls₁ d₂'
        (~-⊑-down con₀ (syn-cls-precision (⊑∷ pa Γ⊑) κ₁⊑ m⊑ cls₁ cls₀) ϕ₂⊑)

ana-cls-to-syn Γ⊑ (⊑case₂ σ₀⊑ σ₁⊑ κ₁⊑) m⊑ (scase₂ D₀ eq₀ d₀ cls₀ con₀) (acase₂ D_r eq_r d_r acls')
  with static-gradual-syn Γ⊑ σ₀⊑ D₀
... | _ , D₀' , τ₀⊑
  with refl ← syn-unicity D_r D₀'
  with ⊔-+-⊑ τ₀⊑ eq₀
... | _ , _ , eq'' , pa , pb
  with refl ← +-inj-fst (trans (sym eq'') eq_r)
  with refl ← +-inj-snd (trans (sym eq'') eq_r)
  with ana-cls-to-syn (⊑∷ pb Γ⊑) κ₁⊑ m⊑ cls₀ acls'
     | static-gradual-syn (⊑∷ pa Γ⊑) σ₁⊑ d₀
... | _ , _ , _ , cls₁ | _ , d₁' , ϕ₁⊑ =
      _ , _ , _ ,
      scase₂ D_r eq_r d₁' cls₁
        (~-⊑-down con₀ ϕ₁⊑ (syn-cls-precision (⊑∷ pb Γ⊑) κ₁⊑ m⊑ cls₁ cls₀))

ana-cls-to-syn Γ⊑ (⊑def₁ κ₁⊑ σ₂⊑) m⊑ (sdef₁ cls₀ d₀) (adef₁ scls' d_r)
  with static-gradual-syn
         (⊑∷ (syn-cls-precision Γ⊑ κ₁⊑ m⊑ scls' cls₀) Γ⊑) σ₂⊑ d₀
... | _ , d₂' , _ =
      _ , _ , _ , sdef₁ scls' d₂'

ana-cls-to-syn Γ⊑ (⊑def₂ σ₁⊑ κ₁⊑) m⊑ (sdef₂ D₀ cls₀) (adef₂ D_r acls')
  with static-gradual-syn Γ⊑ σ₁⊑ D₀
... | _ , D₀' , τ'⊑
  with refl ← syn-unicity D_r D₀'
  with ana-cls-to-syn (⊑∷ τ'⊑ Γ⊑) κ₁⊑ m⊑ cls₀ acls'
... | _ , _ , _ , cls₁ =
      _ , _ , _ , sdef₂ D_r cls₁

-- Bounded upward lifts: a calculus derivation classifies its context slice κ
-- under any assumption slice above γ (and, at analysis positions, any outer
-- type above υ_outer), with a focus above the query.
mutual
  lift-syn : ∀ {n Γ₀ C n_f Γ τ τ_p}
               {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]}
               {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
           → Cls ◂ υ ⤳ κ ⊣ γ
           → (Γ'' : ⌊ Γ₀ ⌋) → γ ⊑ₛ Γ''
           → Σ[ ψ_p ∈ ⌊ τ_p ⌋ ] Σ[ ϕ ∈ ⌊ τ ⌋ ] (υ ⊑ₛ ϕ) ∧ ∃[ n' ] ∃[ Γ' ]
               (n , Γ'' .↓ ⊢ κ .↓ at synPos (ψ_p .↓) ▷ n' , Γ' [ ⇐mode (ϕ .↓) ])

  lift-pos : ∀ {n Γ₀ C n_f Γ τ τ_p}
               {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]}
               {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {υ_outer : ⌊ τ_p ⌋} {γ : ⌊ Γ₀ ⌋}
           → Cls ◂ υ ⤳ κ ⇓ υ_outer ⊣ γ
           → (Γ'' : ⌊ Γ₀ ⌋) → γ ⊑ₛ Γ''
           → (υ_p : ⌊ τ_p ⌋) → υ_outer ⊑ₛ υ_p
           → Σ[ ϕ ∈ ⌊ τ ⌋ ] (υ ⊑ₛ ϕ) ∧ ∃[ n' ] ∃[ Γ' ]
               (n , Γ'' .↓ ⊢ κ .↓ at anaPos (υ_p .↓) ▷ n' , Γ' [ ⇐mode (ϕ .↓) ])

  lift-syn {Cls = Cls} min□ Γ'' _
    with static-gradual-syn-cls (Γ'' .proof) ((⊥ₛ {a = _}) .proof) Cls
  ... | _ , _ , _ , _ , ψ_p⊑ , _ , ⇐mode-⊑ ϕ⊑ , cls =
        ↑ ψ_p⊑ , ↑ ϕ⊑ , ⊑□ , _ , _ , cls

  lift-syn (minSι₁ c) Γ'' γ⊑
    with lift-syn c Γ'' γ⊑
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        ψ_p +ₛ ⊥ₛ , ϕ , υ⊑ϕ , _ , _ , sι₁ cls

  lift-syn (minSι₂ c) Γ'' γ⊑
    with lift-syn c Γ'' γ⊑
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        ⊥ₛ +ₛ ψ_p , ϕ , υ⊑ϕ , _ , _ , sι₂ cls

  lift-syn (minS&₁ c) Γ'' γ⊑
    with lift-syn c Γ'' γ⊑
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        ψ_p ×ₛ ⊥ₛ , ϕ , υ⊑ϕ , _ , _ , s&₁ cls ⇑□

  lift-syn (minS&₂ c) Γ'' γ⊑
    with lift-syn c Γ'' γ⊑
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        ⊥ₛ ×ₛ ψ_p , ϕ , υ⊑ϕ , _ , _ , s&₂ ⇑□ cls

  lift-syn (minSπ₁ {eq = eq} c) Γ'' γ⊑
    with lift-syn c Γ'' γ⊑
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        fst×ₛ' ψ_p eq , ϕ , υ⊑ϕ , _ , _ , sπ₁ cls (match×ₛ ψ_p eq)

  lift-syn (minSπ₂ {eq = eq} c) Γ'' γ⊑
    with lift-syn c Γ'' γ⊑
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        snd×ₛ ψ_p eq , ϕ , υ⊑ϕ , _ , _ , sπ₂ cls (match×ₛ ψ_p eq)

  lift-syn (minS∘₁ {eq = eq} c) Γ'' γ⊑
    with lift-syn c Γ'' γ⊑
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        cod⇒ₛ ψ_p eq , ϕ , υ⊑ϕ , _ , _ , s∘₁ cls (match⇒ₛ ψ_p eq) (⇓Sub ⇑□ ~?₁)

  lift-syn (minS<>₁ {eq = eq} c) Γ'' γ⊑
    with lift-syn c Γ'' γ⊑
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        ↑ (sub-⊑ zero ⊑□ (body∀ₛ ψ_p eq .proof)) , ϕ , υ⊑ϕ , _ , _ ,
        s<>₁ cls (match∀ₛ ψ_p eq) wf□

  lift-syn (minSλ: {wf = wf} {ϕ₁ = ϕ₁} c) Γ'' γ⊑
    with lift-syn c (ϕ₁ ∷ₛ Γ'') (⊑∷ (⊑.refl {A = Typ}) γ⊑)
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        ϕ₁ ⇒ₛ ψ_p , ϕ , υ⊑ϕ , _ , _ , sλ: (wf-⊑ wf (ϕ₁ .proof)) cls

  lift-syn (minS∘₂ {τ₀ = τ₀} {D₁ = D₁} {eq = eq} {υ_outer = υ_outer} {γ' = γ'} {σ = σ} {γ₁ = γ₁} cₚ f) Γ'' γ⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ .proof) D₁
  ... | ψγ , dγ , q⊑ψγ | ψ'' , d'' , ψ''⊑τ₀
    with unmatch⇒-min-cov τ₀ eq υ_outer ⊥ₛ
           (⊑.trans {A = Typ} q⊑ψγ
              (syn-precision
                 (⊑.trans {A = Assms} (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₁ γ') γ⊑)
                 (⊑.refl {A = Exp}) d'' dγ))
           (match⇒ₛ (_ isSlice ψ''⊑τ₀) eq)
  ... | υ_outer⊑dom , _
    with lift-pos cₚ Γ'' (⊑.trans {A = Assms} (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₁ γ') γ⊑)
           (dom⇒ₛ (_ isSlice ψ''⊑τ₀) eq) υ_outer⊑dom
  ... | ϕ , υ⊑ϕ , _ , _ , cls =
        cod⇒ₛ (_ isSlice ψ''⊑τ₀) eq , ϕ , υ⊑ϕ , _ , _ ,
        s∘₂ d'' (match⇒ₛ (_ isSlice ψ''⊑τ₀) eq) cls

  lift-syn (minSΛ {γ' = γ'} c) Γ'' γ⊑
    with lift-syn c (shiftΓₛ Γ'')
           (⊑.trans {A = Assms}
              (⊑.reflexive {A = Assms} (sym (shift-unshiftΓ (γ' .↓) (γ' .proof))))
              (shiftΓ-⊑ γ⊑))
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        ∀·ₛ ψ_p , ϕ , υ⊑ϕ , _ , _ , sΛ cls

  lift-syn (minSdef₁ c) Γ'' γ⊑
    with lift-syn c Γ'' γ⊑
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        ⊥ₛ , ϕ , υ⊑ϕ , _ , _ , sdef₁ cls ⇑□

  lift-syn (minSdef₂ {τ' = τ'} {D = D} {ς = ς} {γ₂ = γ₂} {σ₁ = σ₁} {γ₁ = γ₁} c f) Γ'' γ⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ₁ .proof) D
  ... | ψγ , dγ , ς⊑ψγ | ψ'' , d'' , ψ''⊑τ'
    with lift-syn c ((_ isSlice ψ''⊑τ') ∷ₛ Γ'')
           (⊑∷ (⊑.trans {A = Typ} ς⊑ψγ
                  (syn-precision
                     (⊑.trans {A = Assms} (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₁ γ₂) γ⊑)
                     (⊑.refl {A = Exp}) d'' dγ))
               (⊑.trans {A = Assms} (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₁ γ₂) γ⊑))
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        ψ_p , ϕ , υ⊑ϕ , _ , _ , sdef₂ d'' cls

  lift-syn (minScase₁ {τ₀ = τ₀} {D = D} {eq = eq} {con = con} {ς₁ = ς₁} {γ₁ = γ₁} {σ₀ = σ₀} {γ₀ = γ₀} c f) Γ'' γ⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ₀ .proof) D
  ... | ψγ , dγ , q⊑ψγ | ψ₀'' , d₀'' , ψ₀''⊑τ₀
    with unmatch+-min-cov τ₀ eq ς₁ ⊥ₛ
           (⊑.trans {A = Typ} q⊑ψγ
              (syn-precision
                 (⊑.trans {A = Assms} (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₀ γ₁) γ⊑)
                 (⊑.refl {A = Exp}) d₀'' dγ))
           (match+ₛ (_ isSlice ψ₀''⊑τ₀) eq)
  ... | ς₁⊑fst , _
    with lift-syn c ((fst+ₛ' (_ isSlice ψ₀''⊑τ₀) eq) ∷ₛ Γ'')
           (⊑∷ ς₁⊑fst (⊑.trans {A = Assms} (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₀ γ₁) γ⊑))
  ... | ψ₁' , ϕ , υ⊑ϕ , _ , _ , cls =
        ↑ (⊔-mono-⊑ con (ψ₁' .proof) ⊑□) , ϕ , υ⊑ϕ , _ , _ ,
        scase₁ d₀'' (match+ₛ (_ isSlice ψ₀''⊑τ₀) eq) cls ⇑□ ~?₁

  lift-syn (minScase₂ {τ₀ = τ₀} {D = D} {eq = eq} {con = con} {ς₂ = ς₂} {γ₂ = γ₂} {σ₀ = σ₀} {γ₀ = γ₀} c f) Γ'' γ⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ₀ .proof) D
  ... | ψγ , dγ , q⊑ψγ | ψ₀'' , d₀'' , ψ₀''⊑τ₀
    with unmatch+-min-cov τ₀ eq ⊥ₛ ς₂
           (⊑.trans {A = Typ} q⊑ψγ
              (syn-precision
                 (⊑.trans {A = Assms} (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₀ γ₂) γ⊑)
                 (⊑.refl {A = Exp}) d₀'' dγ))
           (match+ₛ (_ isSlice ψ₀''⊑τ₀) eq)
  ... | _ , ς₂⊑snd
    with lift-syn c ((snd+ₛ' (_ isSlice ψ₀''⊑τ₀) eq) ∷ₛ Γ'')
           (⊑∷ ς₂⊑snd (⊑.trans {A = Assms} (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₀ γ₂) γ⊑))
  ... | ψ₂' , ϕ , υ⊑ϕ , _ , _ , cls =
        ↑ (⊔-mono-⊑ con ⊑□ (ψ₂' .proof)) , ϕ , υ⊑ϕ , _ , _ ,
        scase₂ d₀'' (match+ₛ (_ isSlice ψ₀''⊑τ₀) eq) ⇑□ cls ~?₂

  lift-pos {Cls = Cls} min□Pos Γ'' _ υ_p _
    with static-gradual-ana-cls (Γ'' .proof) ((⊥ₛ {a = _}) .proof) (υ_p .proof) Cls
  ... | _ , _ , _ , _ , ⇐mode-⊑ ϕ⊑ , cls =
        ↑ ϕ⊑ , ⊑□ , _ , _ , cls

  lift-pos (minA○ υ) Γ'' _ υ_p υ⊑υ_p =
    υ_p , υ⊑υ_p , _ , _ , a○

  lift-pos (minASub {con = con} c) Γ'' γ⊑ υ_p _
    with lift-syn c Γ'' γ⊑
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        ϕ , υ⊑ϕ , _ , _ , aSub cls (~-⊑-down con (υ_p .proof) (ψ_p .proof))

  lift-pos (minAι₁ {τ = τ} {eq = eq} {υ_b = υ_b} c) Γ'' γ⊑ υ_p υo⊑
    with unmatch+-min-cov τ eq υ_b ⊥ₛ υo⊑ (match+ₛ υ_p eq)
  ... | υ_b⊑fst , _
    with lift-pos c Γ'' γ⊑ (fst+ₛ' υ_p eq) υ_b⊑fst
  ... | ϕ , υ⊑ϕ , _ , _ , cls =
        ϕ , υ⊑ϕ , _ , _ , aι₁ (match+ₛ υ_p eq) cls

  lift-pos (minAι₂ {τ = τ} {eq = eq} {υ_b = υ_b} c) Γ'' γ⊑ υ_p υo⊑
    with unmatch+-min-cov τ eq ⊥ₛ υ_b υo⊑ (match+ₛ υ_p eq)
  ... | _ , υ_b⊑snd
    with lift-pos c Γ'' γ⊑ (snd+ₛ' υ_p eq) υ_b⊑snd
  ... | ϕ , υ⊑ϕ , _ , _ , cls =
        ϕ , υ⊑ϕ , _ , _ , aι₂ (match+ₛ υ_p eq) cls

  lift-pos (minA&₁ {τ = τ} {eq = eq} {υ_b = υ_b} c) Γ'' γ⊑ υ_p υo⊑
    with unmatch×-min-cov τ eq υ_b ⊥ₛ υo⊑ (match×ₛ υ_p eq)
  ... | υ_b⊑fst , _
    with lift-pos c Γ'' γ⊑ (fst×ₛ' υ_p eq) υ_b⊑fst
  ... | ϕ , υ⊑ϕ , _ , _ , cls =
        ϕ , υ⊑ϕ , _ , _ , a&₁ (match×ₛ υ_p eq) cls (⇓Sub ⇑□ ~?₁)

  lift-pos (minA&₂ {τ = τ} {eq = eq} {υ_b = υ_b} c) Γ'' γ⊑ υ_p υo⊑
    with unmatch×-min-cov τ eq ⊥ₛ υ_b υo⊑ (match×ₛ υ_p eq)
  ... | _ , υ_b⊑snd
    with lift-pos c Γ'' γ⊑ (snd×ₛ υ_p eq) υ_b⊑snd
  ... | ϕ , υ⊑ϕ , _ , _ , cls =
        ϕ , υ⊑ϕ , _ , _ , a&₂ (match×ₛ υ_p eq) (⇓Sub ⇑□ ~?₁) cls

  lift-pos (minAλ⇒ {τ = τ} {eq = eq} {ς₁ = ς₁} {υ_b = υ_b} c) Γ'' γ⊑ υ_p υo⊑
    with unmatch⇒-min-cov τ eq ς₁ υ_b υo⊑ (match⇒ₛ υ_p eq)
  ... | ς₁⊑dom , υ_b⊑cod
    with lift-pos c ((dom⇒ₛ υ_p eq) ∷ₛ Γ'') (⊑∷ ς₁⊑dom γ⊑) (cod⇒ₛ υ_p eq) υ_b⊑cod
  ... | ϕ , υ⊑ϕ , _ , _ , cls =
        ϕ , υ⊑ϕ , _ , _ , aλ⇒ (match⇒ₛ υ_p eq) cls

  lift-pos (minAλ: {τ = τ} {τ₁ = τ₁} {con = con} {eq = eq} {wf = wf} {ς₁ = ς₁} {υ_b = υ_b} c) Γ'' γ⊑ υ_p υo⊑
    with ⊔-ann-⇒-⊑ (υ_p .proof) (ς₁ .proof) eq
  ... | _ , b_p , eq_p , b_p⊑τ₂
    with unmatch⇒-min-cov τ (proj₂ (ann-⇒-plain {τ} {τ₁} eq)) ⊥ₛ υ_b υo⊑
           (proj₂ (ann-⇒-plain {υ_p .↓} {ς₁ .↓} eq_p))
  ... | _ , υ_b⊑b_p
    with lift-pos c (ς₁ ∷ₛ Γ'') (⊑∷ (⊑.refl {A = Typ}) γ⊑) (_ isSlice b_p⊑τ₂) υ_b⊑b_p
  ... | ϕ , υ⊑ϕ , _ , _ , cls =
        ϕ , υ⊑ϕ , _ , _ ,
        aλ: (~-⊑-down con (υ_p .proof) (⊑⇒ (ς₁ .proof) ⊑□)) eq_p (wf-⊑ wf (ς₁ .proof)) cls

  lift-pos (minAdef₁ c) Γ'' γ⊑ υ_p _
    with lift-syn c Γ'' γ⊑
  ... | ψ_p , ϕ , υ⊑ϕ , _ , _ , cls =
        ϕ , υ⊑ϕ , _ , _ , adef₁ cls (⇓Sub ⇑□ ~?₁)

  lift-pos (minAdef₂ {τ' = τ'} {D = D} {ς = ς} {γ₂ = γ₂} {σ₁ = σ₁} {γ₁ = γ₁} c f) Γ'' γ⊑ υ_p υo⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ₁ .proof) D
  ... | ψγ , dγ , ς⊑ψγ | ψ'' , d'' , ψ''⊑τ'
    with lift-pos c ((_ isSlice ψ''⊑τ') ∷ₛ Γ'')
           (⊑∷ (⊑.trans {A = Typ} ς⊑ψγ
                  (syn-precision
                     (⊑.trans {A = Assms} (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₁ γ₂) γ⊑)
                     (⊑.refl {A = Exp}) d'' dγ))
               (⊑.trans {A = Assms} (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₁ γ₂) γ⊑))
           υ_p υo⊑
  ... | ϕ , υ⊑ϕ , _ , _ , cls =
        ϕ , υ⊑ϕ , _ , _ , adef₂ d'' cls

  lift-pos (minAcase₁ {τ₀ = τ₀} {D = D} {eq = eq} {ς₁ = ς₁} {γ₁ = γ₁} {σ₀ = σ₀} {γ₀ = γ₀} c f) Γ'' γ⊑ υ_p υo⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ₀ .proof) D
  ... | ψγ , dγ , q⊑ψγ | ψ₀'' , d₀'' , ψ₀''⊑τ₀
    with unmatch+-min-cov τ₀ eq ς₁ ⊥ₛ
           (⊑.trans {A = Typ} q⊑ψγ
              (syn-precision
                 (⊑.trans {A = Assms} (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₀ γ₁) γ⊑)
                 (⊑.refl {A = Exp}) d₀'' dγ))
           (match+ₛ (_ isSlice ψ₀''⊑τ₀) eq)
  ... | ς₁⊑fst , _
    with lift-pos c ((fst+ₛ' (_ isSlice ψ₀''⊑τ₀) eq) ∷ₛ Γ'')
           (⊑∷ ς₁⊑fst (⊑.trans {A = Assms} (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₀ γ₁) γ⊑))
           υ_p υo⊑
  ... | ϕ , υ⊑ϕ , _ , _ , cls =
        ϕ , υ⊑ϕ , _ , _ ,
        acase₁ d₀'' (match+ₛ (_ isSlice ψ₀''⊑τ₀) eq) cls (⇓Sub ⇑□ ~?₁)

  lift-pos (minAcase₂ {τ₀ = τ₀} {D = D} {eq = eq} {ς₂ = ς₂} {γ₂ = γ₂} {σ₀ = σ₀} {γ₀ = γ₀} c f) Γ'' γ⊑ υ_p υo⊑
    with FC.extract-ctx f | static-gradual-syn (Γ'' .proof) (σ₀ .proof) D
  ... | ψγ , dγ , q⊑ψγ | ψ₀'' , d₀'' , ψ₀''⊑τ₀
    with unmatch+-min-cov τ₀ eq ⊥ₛ ς₂
           (⊑.trans {A = Typ} q⊑ψγ
              (syn-precision
                 (⊑.trans {A = Assms} (⊑ₛLat.x⊑ₛx⊔ₛy {A = Assms} γ₀ γ₂) γ⊑)
                 (⊑.refl {A = Exp}) d₀'' dγ))
           (match+ₛ (_ isSlice ψ₀''⊑τ₀) eq)
  ... | _ , ς₂⊑snd
    with lift-pos c ((snd+ₛ' (_ isSlice ψ₀''⊑τ₀) eq) ∷ₛ Γ'')
           (⊑∷ ς₂⊑snd (⊑.trans {A = Assms} (⊑ₛLat.y⊑ₛx⊔ₛy {A = Assms} γ₀ γ₂) γ⊑))
           υ_p υo⊑
  ... | ϕ , υ⊑ϕ , _ , _ , cls =
        ϕ , υ⊑ϕ , _ , _ ,
        acase₂ d₀'' (match+ₛ (_ isSlice ψ₀''⊑τ₀) eq) (⇓Sub ⇑□ ~?₁) cls

extract : ∀ {n Γ₀ C n_f Γ τ τ_p}
            {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]}
            {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
        → Cls ◂ υ ⤳ κ ⊣ γ → AnaSlice Cls υ
extract {κ = κ} {γ = γ} c =
  let (ψ_p , ϕ , υ⊑ϕ , n' , Γ' , cls) = lift-syn c γ (⊑.refl {A = Assms})
  in record { κ = κ ; γ = γ ; type = ψ_p ; focus = ϕ ; focus⊒ = υ⊑ϕ
            ; valid = n' , Γ' , cls }

extract-pos : ∀ {n Γ₀ C n_f Γ τ τ_p}
                {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]}
                {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {υ_outer : ⌊ τ_p ⌋} {γ : ⌊ Γ₀ ⌋}
            → Cls ◂ υ ⤳ κ ⇓ υ_outer ⊣ γ → AnaPosSlice Cls υ
extract-pos {κ = κ} {υ_outer = υ_outer} {γ = γ} c =
  let (ϕ , υ⊑ϕ , n' , Γ' , cls) = lift-pos c γ (⊑.refl {A = Assms}) υ_outer (⊑.refl {A = Typ})
  in record { κ = κ ; γ = γ ; υ_outer = υ_outer ; focus = ϕ ; focus⊒ = υ⊑ϕ
            ; valid = n' , Γ' , cls }

-- Least-ness of calculus outputs: any valid classification of a context
-- slice below κ (under an arbitrary assumption slice, at an arbitrary outer
-- analysis type) bounds κ, γ, and υ_outer from above.  Minimality of
-- extraction is the corollary at the rival's own components.
mutual
  extract-least : ∀ {n Γ₀ C n_f Γ τ τ_p}
                    {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]}
                    {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
                → Cls ◂ υ ⤳ κ ⊣ γ
                → ∀ {n' Γ' ψ_r ϕ_r} (κ_r : ⌊ C ⌋) (Γ_r : ⌊ Γ₀ ⌋)
                → κ_r ⊑ₛ κ
                → υ .↓ ⊑t ϕ_r
                → ϕ_r ⊑t τ
                → n , Γ_r .↓ ⊢ κ_r .↓ at synPos ψ_r ▷ n' , Γ' [ ⇐mode ϕ_r ]
                → (κ ⊑ₛ κ_r) ∧ (γ ⊑ₛ Γ_r)

  extract-pos-least : ∀ {n Γ₀ C n_f Γ τ τ_p}
                        {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]}
                        {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {υ_outer : ⌊ τ_p ⌋} {γ : ⌊ Γ₀ ⌋}
                    → Cls ◂ υ ⤳ κ ⇓ υ_outer ⊣ γ
                    → ∀ {n' Γ' ϕ_r} (κ_r : ⌊ C ⌋) (Γ_r : ⌊ Γ₀ ⌋) (υ_or : ⌊ τ_p ⌋)
                    → κ_r ⊑ₛ κ
                    → υ .↓ ⊑t ϕ_r
                    → ϕ_r ⊑t τ
                    → n , Γ_r .↓ ⊢ κ_r .↓ at anaPos (υ_or .↓) ▷ n' , Γ' [ ⇐mode ϕ_r ]
                    → (κ ⊑ₛ κ_r) ∧ (γ ⊑ₛ Γ_r) ∧ (υ_outer ⊑ₛ υ_or)

  extract-least min□ κ_r Γ_r _ _ _ _ =
    ⊑ₛLat.⊥ₛ-min {A = Ctx} κ_r , ⊑ₛLat.⊥ₛ-min {A = Assms} Γ_r

  extract-least (minSι₁ c) (_ isSlice ⊑ι₁ κ_r₁⊑C) Γ_r (⊑ι₁ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (sι₁ cls_r)
    with extract-least c (_ isSlice κ_r₁⊑C) Γ_r κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ = ⊑ι₁ ih-κ , ih-γ

  extract-least (minSι₂ c) (_ isSlice ⊑ι₂ κ_r₁⊑C) Γ_r (⊑ι₂ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (sι₂ cls_r)
    with extract-least c (_ isSlice κ_r₁⊑C) Γ_r κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ = ⊑ι₂ ih-κ , ih-γ

  extract-least (minS&₁ c) (_ isSlice ⊑&₁ κ_r₁⊑C _) Γ_r (⊑&₁ κ_r₁⊑κ _) υ⊑ϕ ϕ⊑τ (s&₁ cls_r d_r)
    with extract-least c (_ isSlice κ_r₁⊑C) Γ_r κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ = ⊑&₁ ih-κ ⊑□ , ih-γ

  extract-least (minS&₂ c) (_ isSlice ⊑&₂ _ κ_r₁⊑C) Γ_r (⊑&₂ _ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (s&₂ d_r cls_r)
    with extract-least c (_ isSlice κ_r₁⊑C) Γ_r κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ = ⊑&₂ ⊑□ ih-κ , ih-γ

  extract-least (minSπ₁ c) (_ isSlice ⊑π₁ κ_r₁⊑C) Γ_r (⊑π₁ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (sπ₁ cls_r eq_r)
    with extract-least c (_ isSlice κ_r₁⊑C) Γ_r κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ = ⊑π₁ ih-κ , ih-γ

  extract-least (minSπ₂ c) (_ isSlice ⊑π₂ κ_r₁⊑C) Γ_r (⊑π₂ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (sπ₂ cls_r eq_r)
    with extract-least c (_ isSlice κ_r₁⊑C) Γ_r κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ = ⊑π₂ ih-κ , ih-γ

  extract-least (minS∘₁ c) (_ isSlice ⊑∘₁ κ_r₁⊑C _) Γ_r (⊑∘₁ κ_r₁⊑κ _) υ⊑ϕ ϕ⊑τ (s∘₁ cls_r eq_r d_r)
    with extract-least c (_ isSlice κ_r₁⊑C) Γ_r κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ = ⊑∘₁ ih-κ ⊑□ , ih-γ

  extract-least (minS<>₁ c) (_ isSlice ⊑<>₁ κ_r₁⊑C _) Γ_r (⊑<>₁ κ_r₁⊑κ _) υ⊑ϕ ϕ⊑τ (s<>₁ cls_r eq_r wf_r)
    with extract-least c (_ isSlice κ_r₁⊑C) Γ_r κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ = ⊑<>₁ ih-κ ⊑□ , ih-γ

  extract-least (minSλ: c) (_ isSlice ⊑λ t_r⊑τ₁ κ_r₁⊑C) Γ_r (⊑λ t_r⊑ϕ₁ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (sλ: wf_r cls_r)
    with extract-least c (_ isSlice κ_r₁⊑C) ((↑ t_r⊑τ₁) ∷ₛ Γ_r) κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ⊑∷ ih-hd ih-tl = ⊑λ ih-hd ih-κ , ih-tl

  extract-least (minSΛ c) (_ isSlice ⊑Λ κ_r₁⊑C) Γ_r (⊑Λ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (sΛ cls_r)
    with extract-least c (_ isSlice κ_r₁⊑C) (shiftΓₛ Γ_r) κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ =
        ⊑Λ ih-κ ,
        ⊑.trans {A = Assms} (unshiftΓ-⊑ ih-γ)
          (⊑.reflexive {A = Assms} (unshiftΓ-shiftΓ (Γ_r .↓)))

  extract-least {Γ₀ = Γ₀}
      (minS∘₂ {τ₀ = τ₀} {D₁ = D₁} {eq = eq} {υ_outer = υ_outer} {γ' = γ'} {σ = σ} {γ₁ = γ₁} cₚ f)
      ((σ_r₀ ∘₂ _) isSlice ⊑∘₂ σ_r⊑e κ_r₁⊑C) Γ_r (⊑∘₂ σ_r⊑σ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (s∘₂ D_r eq_r cls_r)
    with syn-precision (Γ_r .proof) σ_r⊑e D₁ D_r
  ... | τ₀r⊑τ₀
    with ⊔-⇒-⊑ τ₀r⊑τ₀ eq
  ... | _ , _ , eq_ra , a⊑τ₁ , _
    with refl ← ⇒-inj-fst (trans (sym eq_ra) eq_r)
    with refl ← ⇒-inj-snd (trans (sym eq_ra) eq_r)
    with extract-pos-least cₚ (_ isSlice κ_r₁⊑C) Γ_r (_ isSlice a⊑τ₁) κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ' , ih-υ
    with static-gradual-syn (⊑.refl {A = Assms}) σ_r⊑e D₁
  ... | ψ_rf , d_rf , ψ_rf⊑τ₀
    with ⊔-⇒-⊑ ψ_rf⊑τ₀ eq
  ... | a_f , _ , eq_f , _ , _
    with ⊔-⇒-⊑ (syn-precision (Γ_r .proof) (⊑.refl {A = Exp}) d_rf D_r) eq_f
  ... | _ , _ , eq_f2 , a⊑a_f , _
    with refl ← ⇒-inj-fst (trans (sym eq_f2) eq_r)
    with refl ← ⇒-inj-snd (trans (sym eq_f2) eq_r)
    with FC.extract-minimal f
           ((_ isSlice σ_r⊑e) ⇑ (_ isSlice ψ_rf⊑τ₀) ∈ d_rf ⊒
              unmatch⇒-min-least τ₀ eq υ_outer ⊥ₛ ψ_rf⊑τ₀ eq_f
                (⊑.trans {A = Typ} ih-υ a⊑a_f) ⊑□)
           (subst (σ_r₀ ⊑e_) (sym (cong (λ x → x .↓) (FC.extract-σ f))) σ_r⊑σ)
  ... | ih-fix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) ih-fix
  ... | eqσ =
        ⊑∘₂ (⊑.reflexive {A = Exp} eqσ) ih-κ ,
        ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₁} {γ'} {Γ_r}
          (FC.extract-ctx-min f
             (subst (λ x → _ , Γ_r .↓ ⊢ x ⇑ _) (sym eqσ) D_r)
             (unmatch⇒-min-least τ₀ eq υ_outer ⊥ₛ τ₀r⊑τ₀ eq_r ih-υ ⊑□)
             (Γ_r .proof))
          ih-γ'

  extract-least (minSdef₁ c) (_ isSlice ⊑def₁ κ_r₁⊑C _) Γ_r (⊑def₁ κ_r₁⊑κ _) υ⊑ϕ ϕ⊑τ (sdef₁ cls_r d_r)
    with extract-least c (_ isSlice κ_r₁⊑C) Γ_r κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ = ⊑def₁ ih-κ ⊑□ , ih-γ

  extract-least {Γ₀ = Γ₀} (minSdef₂ {τ' = τ'} {D = D} {ς = ς} {γ₂ = γ₂} {σ₁ = σ₁} {γ₁ = γ₁} c f)
      ((def σ_r₀ ⊢₂ _) isSlice ⊑def₂ σ_r⊑e κ_r₁⊑C) Γ_r (⊑def₂ σ_r⊑σ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (sdef₂ D_r cls_r)
    with syn-precision (Γ_r .proof) σ_r⊑e D D_r
  ... | τ'r⊑τ'
    with extract-least c (_ isSlice κ_r₁⊑C) ((_ isSlice τ'r⊑τ') ∷ₛ Γ_r) κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ⊑∷ ih-hd ih-tl
    with static-gradual-syn (⊑.refl {A = Assms}) σ_r⊑e D
  ... | ψ_rf , d_rf , ψ_rf⊑τ'
    with FC.extract-minimal f
           ((_ isSlice σ_r⊑e) ⇑ (_ isSlice ψ_rf⊑τ') ∈ d_rf ⊒
              ⊑.trans {A = Typ} ih-hd (syn-precision (Γ_r .proof) (⊑.refl {A = Exp}) d_rf D_r))
           (subst (σ_r₀ ⊑e_) (sym (cong (λ x → x .↓) (FC.extract-σ f))) σ_r⊑σ)
  ... | ih-fix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) ih-fix
  ... | eqσ =
        ⊑def₂ (⊑.reflexive {A = Exp} eqσ) ih-κ ,
        ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₁} {γ₂} {Γ_r}
          (FC.extract-ctx-min f
             (subst (λ x → _ , Γ_r .↓ ⊢ x ⇑ _) (sym eqσ) D_r)
             ih-hd (Γ_r .proof))
          ih-tl

  extract-least {Γ₀ = Γ₀} (minScase₁ {τ₀ = τ₀} {D = D} {eq = eq} {ς₁ = ς₁} {γ₁ = γ₁} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      ((case σ_r₀ of _ ·₁ _) isSlice ⊑case₁ σ₀_r⊑e κ_r₁⊑C _) Γ_r
      (⊑case₁ σ_r⊑σ₀ κ_r₁⊑κ _) υ⊑ϕ ϕ⊑τ (scase₁ D_r eq_r cls_r d₂_r con_r)
    with syn-precision (Γ_r .proof) σ₀_r⊑e D D_r
  ... | τ₀r⊑τ₀
    with ⊔-+-⊑ τ₀r⊑τ₀ eq
  ... | _ , _ , eq_ra , a⊑τ₁ , _
    with refl ← +-inj-fst (trans (sym eq_ra) eq_r)
    with refl ← +-inj-snd (trans (sym eq_ra) eq_r)
    with extract-least c (_ isSlice κ_r₁⊑C) ((_ isSlice a⊑τ₁) ∷ₛ Γ_r) κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ⊑∷ ih-hd ih-tl
    with static-gradual-syn (⊑.refl {A = Assms}) σ₀_r⊑e D
  ... | ψ_rf , d_rf , ψ_rf⊑τ₀
    with ⊔-+-⊑ ψ_rf⊑τ₀ eq
  ... | a_f , _ , eq_f , _ , _
    with ⊔-+-⊑ (syn-precision (Γ_r .proof) (⊑.refl {A = Exp}) d_rf D_r) eq_f
  ... | _ , _ , eq_f2 , a⊑a_f , _
    with refl ← +-inj-fst (trans (sym eq_f2) eq_r)
    with refl ← +-inj-snd (trans (sym eq_f2) eq_r)
    with FC.extract-minimal f
           ((_ isSlice σ₀_r⊑e) ⇑ (_ isSlice ψ_rf⊑τ₀) ∈ d_rf ⊒
              unmatch+-min-least τ₀ eq ς₁ ⊥ₛ ψ_rf⊑τ₀ eq_f
                (⊑.trans {A = Typ} ih-hd a⊑a_f) ⊑□)
           (subst (σ_r₀ ⊑e_) (sym (cong (λ x → x .↓) (FC.extract-σ f))) σ_r⊑σ₀)
  ... | ih-fix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) ih-fix
  ... | eqσ =
        ⊑case₁ (⊑.reflexive {A = Exp} eqσ) ih-κ ⊑□ ,
        ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₀} {γ₁} {Γ_r}
          (FC.extract-ctx-min f
             (subst (λ x → _ , Γ_r .↓ ⊢ x ⇑ _) (sym eqσ) D_r)
             (unmatch+-min-least τ₀ eq ς₁ ⊥ₛ τ₀r⊑τ₀ eq_r ih-hd ⊑□)
             (Γ_r .proof))
          ih-tl

  extract-least {Γ₀ = Γ₀} (minScase₂ {τ₀ = τ₀} {D = D} {eq = eq} {ς₂ = ς₂} {γ₂ = γ₂} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      ((case σ_r₀ of₂ _ · _) isSlice ⊑case₂ σ₀_r⊑e _ κ_r₁⊑C) Γ_r
      (⊑case₂ σ_r⊑σ₀ _ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (scase₂ D_r eq_r d₁_r cls_r con_r)
    with syn-precision (Γ_r .proof) σ₀_r⊑e D D_r
  ... | τ₀r⊑τ₀
    with ⊔-+-⊑ τ₀r⊑τ₀ eq
  ... | _ , _ , eq_ra , _ , b⊑τ₂
    with refl ← +-inj-fst (trans (sym eq_ra) eq_r)
    with refl ← +-inj-snd (trans (sym eq_ra) eq_r)
    with extract-least c (_ isSlice κ_r₁⊑C) ((_ isSlice b⊑τ₂) ∷ₛ Γ_r) κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ⊑∷ ih-hd ih-tl
    with static-gradual-syn (⊑.refl {A = Assms}) σ₀_r⊑e D
  ... | ψ_rf , d_rf , ψ_rf⊑τ₀
    with ⊔-+-⊑ ψ_rf⊑τ₀ eq
  ... | _ , b_f , eq_f , _ , _
    with ⊔-+-⊑ (syn-precision (Γ_r .proof) (⊑.refl {A = Exp}) d_rf D_r) eq_f
  ... | _ , _ , eq_f2 , _ , b⊑b_f
    with refl ← +-inj-fst (trans (sym eq_f2) eq_r)
    with refl ← +-inj-snd (trans (sym eq_f2) eq_r)
    with FC.extract-minimal f
           ((_ isSlice σ₀_r⊑e) ⇑ (_ isSlice ψ_rf⊑τ₀) ∈ d_rf ⊒
              unmatch+-min-least τ₀ eq ⊥ₛ ς₂ ψ_rf⊑τ₀ eq_f ⊑□
                (⊑.trans {A = Typ} ih-hd b⊑b_f))
           (subst (σ_r₀ ⊑e_) (sym (cong (λ x → x .↓) (FC.extract-σ f))) σ_r⊑σ₀)
  ... | ih-fix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) ih-fix
  ... | eqσ =
        ⊑case₂ (⊑.reflexive {A = Exp} eqσ) ⊑□ ih-κ ,
        ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₀} {γ₂} {Γ_r}
          (FC.extract-ctx-min f
             (subst (λ x → _ , Γ_r .↓ ⊢ x ⇑ _) (sym eqσ) D_r)
             (unmatch+-min-least τ₀ eq ⊥ₛ ς₂ τ₀r⊑τ₀ eq_r ⊑□ ih-hd)
             (Γ_r .proof))
          ih-tl

  extract-pos-least min□Pos κ_r Γ_r υ_or _ _ _ _ =
    ⊑ₛLat.⊥ₛ-min {A = Ctx} κ_r , ⊑ₛLat.⊥ₛ-min {A = Assms} Γ_r ,
    ⊑ₛLat.⊥ₛ-min {A = Typ} υ_or

  extract-pos-least (minA○ υ) (_ isSlice ⊑○) Γ_r υ_or ⊑○ υ⊑ϕ ϕ⊑τ a○ =
    ⊑○ , ⊑ₛLat.⊥ₛ-min {A = Assms} Γ_r , υ⊑ϕ

  extract-pos-least (minASub {Cls' = Cls'} c) κ_r Γ_r υ_or κ_r⊑ υ⊑ϕ ϕ⊑τ cls
    with ana-cls-to-syn (Γ_r .proof) (κ_r .proof) (⇐mode-⊑ ϕ⊑τ) Cls' cls
  ... | _ , _ , _ , scls_r
    with extract-least c κ_r Γ_r κ_r⊑ υ⊑ϕ ϕ⊑τ scls_r
  ... | ih-κ , ih-γ = ih-κ , ih-γ , ⊑ₛLat.⊥ₛ-min {A = Typ} υ_or

  extract-pos-least (minAι₁ {τ = τ'} {eq = eq} {υ_b = υ_b} c)
      (_ isSlice ⊑ι₁ κ_r₁⊑C) Γ_r υ_or (⊑ι₁ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (aSub (sι₁ scls_r) con_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) Γ_r ⊥ₛ κ_r₁⊑κ υ⊑ϕ ϕ⊑τ (aSub scls_r ~?₂)
  ... | ih-κ , ih-γ , ih-υ =
        ⊑ι₁ ih-κ , ih-γ ,
        subst (_⊑t (υ_or .↓)) (sym (unmatch+-min-□ eq υ_b ⊥ₛ (⊑□-inv ih-υ) refl)) ⊑□
  extract-pos-least (minAι₁ {τ = τ'} {eq = eq} {υ_b = υ_b} c)
      (_ isSlice ⊑ι₁ κ_r₁⊑C) Γ_r υ_or (⊑ι₁ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (aι₁ eq_r cls_r)
    with ⊔-+-⊑ (υ_or .proof) eq
  ... | _ , _ , eq'' , a⊑τ₁ , _
    with refl ← +-inj-fst (trans (sym eq'') eq_r)
    with refl ← +-inj-snd (trans (sym eq'') eq_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) Γ_r (_ isSlice a⊑τ₁) κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ , ih-υ =
        ⊑ι₁ ih-κ , ih-γ ,
        unmatch+-min-least τ' eq υ_b ⊥ₛ (υ_or .proof) eq_r ih-υ ⊑□

  extract-pos-least (minAι₂ {τ = τ'} {eq = eq} {υ_b = υ_b} c)
      (_ isSlice ⊑ι₂ κ_r₁⊑C) Γ_r υ_or (⊑ι₂ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (aSub (sι₂ scls_r) con_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) Γ_r ⊥ₛ κ_r₁⊑κ υ⊑ϕ ϕ⊑τ (aSub scls_r ~?₂)
  ... | ih-κ , ih-γ , ih-υ =
        ⊑ι₂ ih-κ , ih-γ ,
        subst (_⊑t (υ_or .↓)) (sym (unmatch+-min-□ eq ⊥ₛ υ_b refl (⊑□-inv ih-υ))) ⊑□
  extract-pos-least (minAι₂ {τ = τ'} {eq = eq} {υ_b = υ_b} c)
      (_ isSlice ⊑ι₂ κ_r₁⊑C) Γ_r υ_or (⊑ι₂ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (aι₂ eq_r cls_r)
    with ⊔-+-⊑ (υ_or .proof) eq
  ... | _ , _ , eq'' , _ , b⊑τ₂
    with refl ← +-inj-fst (trans (sym eq'') eq_r)
    with refl ← +-inj-snd (trans (sym eq'') eq_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) Γ_r (_ isSlice b⊑τ₂) κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ , ih-υ =
        ⊑ι₂ ih-κ , ih-γ ,
        unmatch+-min-least τ' eq ⊥ₛ υ_b (υ_or .proof) eq_r ⊑□ ih-υ

  extract-pos-least (minA&₁ {τ = τ'} {eq = eq} {υ_b = υ_b} c)
      (_ isSlice ⊑&₁ κ_r₁⊑C _) Γ_r υ_or (⊑&₁ κ_r₁⊑κ _) υ⊑ϕ ϕ⊑τ (aSub (s&₁ scls_r d_r) con_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) Γ_r ⊥ₛ κ_r₁⊑κ υ⊑ϕ ϕ⊑τ (aSub scls_r ~?₂)
  ... | ih-κ , ih-γ , ih-υ =
        ⊑&₁ ih-κ ⊑□ , ih-γ ,
        subst (_⊑t (υ_or .↓)) (sym (unmatch×-min-□ eq υ_b ⊥ₛ (⊑□-inv ih-υ) refl)) ⊑□
  extract-pos-least (minA&₁ {τ = τ'} {eq = eq} {υ_b = υ_b} c)
      (_ isSlice ⊑&₁ κ_r₁⊑C _) Γ_r υ_or (⊑&₁ κ_r₁⊑κ _) υ⊑ϕ ϕ⊑τ (a&₁ eq_r cls_r d_r)
    with ⊔-×-⊑ (υ_or .proof) eq
  ... | _ , _ , eq'' , a⊑τ₁ , _
    with refl ← ×-inj-fst (trans (sym eq'') eq_r)
    with refl ← ×-inj-snd (trans (sym eq'') eq_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) Γ_r (_ isSlice a⊑τ₁) κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ , ih-υ =
        ⊑&₁ ih-κ ⊑□ , ih-γ ,
        unmatch×-min-least τ' eq υ_b ⊥ₛ (υ_or .proof) eq_r ih-υ ⊑□

  extract-pos-least (minA&₂ {τ = τ'} {eq = eq} {υ_b = υ_b} c)
      (_ isSlice ⊑&₂ _ κ_r₁⊑C) Γ_r υ_or (⊑&₂ _ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (aSub (s&₂ d_r scls_r) con_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) Γ_r ⊥ₛ κ_r₁⊑κ υ⊑ϕ ϕ⊑τ (aSub scls_r ~?₂)
  ... | ih-κ , ih-γ , ih-υ =
        ⊑&₂ ⊑□ ih-κ , ih-γ ,
        subst (_⊑t (υ_or .↓)) (sym (unmatch×-min-□ eq ⊥ₛ υ_b refl (⊑□-inv ih-υ))) ⊑□
  extract-pos-least (minA&₂ {τ = τ'} {eq = eq} {υ_b = υ_b} c)
      (_ isSlice ⊑&₂ _ κ_r₁⊑C) Γ_r υ_or (⊑&₂ _ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (a&₂ eq_r d_r cls_r)
    with ⊔-×-⊑ (υ_or .proof) eq
  ... | _ , _ , eq'' , _ , b⊑τ₂
    with refl ← ×-inj-fst (trans (sym eq'') eq_r)
    with refl ← ×-inj-snd (trans (sym eq'') eq_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) Γ_r (_ isSlice b⊑τ₂) κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ih-γ , ih-υ =
        ⊑&₂ ⊑□ ih-κ , ih-γ ,
        unmatch×-min-least τ' eq ⊥ₛ υ_b (υ_or .proof) eq_r ⊑□ ih-υ

  extract-pos-least (minAλ⇒ {τ = τ'} {eq = eq} {ς₁ = ς₁} {υ_b = υ_b} c)
      (_ isSlice ⊑λu κ_r₁⊑C) Γ_r υ_or (⊑λu κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (aλ⇒ eq_r cls_r)
    with ⊔-⇒-⊑ (υ_or .proof) eq
  ... | _ , _ , eq'' , a⊑τ₁ , b⊑τ₂
    with refl ← ⇒-inj-fst (trans (sym eq'') eq_r)
    with refl ← ⇒-inj-snd (trans (sym eq'') eq_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) ((_ isSlice a⊑τ₁) ∷ₛ Γ_r) (_ isSlice b⊑τ₂)
           κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ⊑∷ ih-hd ih-tl , ih-υ =
        ⊑λu ih-κ , ih-tl ,
        unmatch⇒-min-least τ' eq ς₁ υ_b (υ_or .proof) eq_r ih-hd ih-υ

  extract-pos-least (minAλ: {τ = τ'} {τ₁ = τ₁} {eq = eq} {ς₁ = ς₁} {υ_b = υ_b} c)
      ((λ: t_r ⇒ _) isSlice ⊑λ t_r⊑τ₁ κ_r₁⊑C) Γ_r υ_or (⊑λ t_r⊑ς₁ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ
      (aSub (sλ: wf_r scls_r) con_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) ((↑ t_r⊑τ₁) ∷ₛ Γ_r) ⊥ₛ
           κ_r₁⊑κ υ⊑ϕ ϕ⊑τ (aSub scls_r ~?₂)
  ... | ih-κ , ⊑∷ ih-hd ih-tl , ih-υ =
        ⊑λ ih-hd ih-κ , ih-tl ,
        subst (_⊑t (υ_or .↓))
              (sym (unmatch⇒-min-□ (proj₂ (ann-⇒-plain {τ'} {τ₁} eq)) ⊥ₛ υ_b refl (⊑□-inv ih-υ))) ⊑□
  extract-pos-least (minAλ: {τ = τ'} {τ₁ = τ₁} {eq = eq} {ς₁ = ς₁} {υ_b = υ_b} c)
      ((λ: t_r ⇒ _) isSlice ⊑λ t_r⊑τ₁ κ_r₁⊑C) Γ_r υ_or (⊑λ t_r⊑ς₁ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ
      (aλ: con_r eq_r wf_r cls_r)
    with ⊔-ann-⇒-⊑ (υ_or .proof) t_r⊑τ₁ eq
  ... | _ , b_x , eq_x , b_x⊑τ₂
    with refl ← ⇒-inj-snd (trans (sym eq_x) eq_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) ((↑ t_r⊑τ₁) ∷ₛ Γ_r) (_ isSlice b_x⊑τ₂)
           κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ⊑∷ ih-hd ih-tl , ih-υ =
        ⊑λ ih-hd ih-κ , ih-tl ,
        unmatch⇒-min-least τ' (proj₂ (ann-⇒-plain {τ'} {τ₁} eq)) ⊥ₛ υ_b
          (υ_or .proof) (proj₂ (ann-⇒-plain {υ_or .↓} {t_r} eq_r)) ⊑□ ih-υ

  extract-pos-least (minAdef₁ c) (_ isSlice ⊑def₁ κ_r₁⊑C _) Γ_r υ_or (⊑def₁ κ_r₁⊑κ _) υ⊑ϕ ϕ⊑τ
      (adef₁ scls_r d_r)
    with extract-least c (_ isSlice κ_r₁⊑C) Γ_r κ_r₁⊑κ υ⊑ϕ ϕ⊑τ scls_r
  ... | ih-κ , ih-γ = ⊑def₁ ih-κ ⊑□ , ih-γ , ⊑ₛLat.⊥ₛ-min {A = Typ} υ_or
  extract-pos-least (minAdef₁ c) (_ isSlice ⊑def₁ κ_r₁⊑C _) Γ_r υ_or (⊑def₁ κ_r₁⊑κ _) υ⊑ϕ ϕ⊑τ
      (aSub (sdef₁ scls_r d_r) con_r)
    with extract-least c (_ isSlice κ_r₁⊑C) Γ_r κ_r₁⊑κ υ⊑ϕ ϕ⊑τ scls_r
  ... | ih-κ , ih-γ = ⊑def₁ ih-κ ⊑□ , ih-γ , ⊑ₛLat.⊥ₛ-min {A = Typ} υ_or

  extract-pos-least {Γ₀ = Γ₀} (minAdef₂ {τ' = τ'} {D = D} {ς = ς} {γ₂ = γ₂} {σ₁ = σ₁} {γ₁ = γ₁} c f)
      ((def σ_r₀ ⊢₂ _) isSlice ⊑def₂ σ_r⊑e κ_r₁⊑C) Γ_r υ_or (⊑def₂ σ_r⊑σ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ
      (adef₂ D_r cls_r)
    with syn-precision (Γ_r .proof) σ_r⊑e D D_r
  ... | τ'r⊑τ'
    with extract-pos-least c (_ isSlice κ_r₁⊑C) ((_ isSlice τ'r⊑τ') ∷ₛ Γ_r) υ_or κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ⊑∷ ih-hd ih-tl , ih-υ
    with static-gradual-syn (⊑.refl {A = Assms}) σ_r⊑e D
  ... | ψ_rf , d_rf , ψ_rf⊑τ'
    with FC.extract-minimal f
           ((_ isSlice σ_r⊑e) ⇑ (_ isSlice ψ_rf⊑τ') ∈ d_rf ⊒
              ⊑.trans {A = Typ} ih-hd (syn-precision (Γ_r .proof) (⊑.refl {A = Exp}) d_rf D_r))
           (subst (σ_r₀ ⊑e_) (sym (cong (λ x → x .↓) (FC.extract-σ f))) σ_r⊑σ)
  ... | ih-fix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) ih-fix
  ... | eqσ =
        ⊑def₂ (⊑.reflexive {A = Exp} eqσ) ih-κ ,
        ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₁} {γ₂} {Γ_r}
          (FC.extract-ctx-min f
             (subst (λ x → _ , Γ_r .↓ ⊢ x ⇑ _) (sym eqσ) D_r)
             ih-hd (Γ_r .proof))
          ih-tl ,
        ih-υ
  extract-pos-least {Γ₀ = Γ₀} (minAdef₂ {τ' = τ'} {D = D} {ς = ς} {γ₂ = γ₂} {σ₁ = σ₁} {γ₁ = γ₁} c f)
      ((def σ_r₀ ⊢₂ _) isSlice ⊑def₂ σ_r⊑e κ_r₁⊑C) Γ_r υ_or (⊑def₂ σ_r⊑σ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ
      (aSub (sdef₂ D_r cls_r) con_r)
    with syn-precision (Γ_r .proof) σ_r⊑e D D_r
  ... | τ'r⊑τ'
    with extract-pos-least c (_ isSlice κ_r₁⊑C) ((_ isSlice τ'r⊑τ') ∷ₛ Γ_r) ⊥ₛ κ_r₁⊑κ υ⊑ϕ ϕ⊑τ
           (aSub cls_r ~?₂)
  ... | ih-κ , ⊑∷ ih-hd ih-tl , ih-υ
    with static-gradual-syn (⊑.refl {A = Assms}) σ_r⊑e D
  ... | ψ_rf , d_rf , ψ_rf⊑τ'
    with FC.extract-minimal f
           ((_ isSlice σ_r⊑e) ⇑ (_ isSlice ψ_rf⊑τ') ∈ d_rf ⊒
              ⊑.trans {A = Typ} ih-hd (syn-precision (Γ_r .proof) (⊑.refl {A = Exp}) d_rf D_r))
           (subst (σ_r₀ ⊑e_) (sym (cong (λ x → x .↓) (FC.extract-σ f))) σ_r⊑σ)
  ... | ih-fix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) ih-fix
  ... | eqσ =
        ⊑def₂ (⊑.reflexive {A = Exp} eqσ) ih-κ ,
        ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₁} {γ₂} {Γ_r}
          (FC.extract-ctx-min f
             (subst (λ x → _ , Γ_r .↓ ⊢ x ⇑ _) (sym eqσ) D_r)
             ih-hd (Γ_r .proof))
          ih-tl ,
        subst (_⊑t (υ_or .↓)) (sym (⊑□-inv ih-υ)) ⊑□

  extract-pos-least {Γ₀ = Γ₀} (minAcase₁ {τ₀ = τ₀} {D = D} {eq = eq} {ς₁ = ς₁} {γ₁ = γ₁} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      ((case σ_r₀ of _ ·₁ _) isSlice ⊑case₁ σ₀_r⊑e κ_r₁⊑C _) Γ_r υ_or
      (⊑case₁ σ_r⊑σ₀ κ_r₁⊑κ _) υ⊑ϕ ϕ⊑τ (acase₁ D_r eq_r cls_r d₂_r)
    with syn-precision (Γ_r .proof) σ₀_r⊑e D D_r
  ... | τ₀r⊑τ₀
    with ⊔-+-⊑ τ₀r⊑τ₀ eq
  ... | _ , _ , eq_ra , a⊑τ₁ , _
    with refl ← +-inj-fst (trans (sym eq_ra) eq_r)
    with refl ← +-inj-snd (trans (sym eq_ra) eq_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) ((_ isSlice a⊑τ₁) ∷ₛ Γ_r) υ_or κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ⊑∷ ih-hd ih-tl , ih-υ
    with static-gradual-syn (⊑.refl {A = Assms}) σ₀_r⊑e D
  ... | ψ_rf , d_rf , ψ_rf⊑τ₀
    with ⊔-+-⊑ ψ_rf⊑τ₀ eq
  ... | a_f , _ , eq_f , _ , _
    with ⊔-+-⊑ (syn-precision (Γ_r .proof) (⊑.refl {A = Exp}) d_rf D_r) eq_f
  ... | _ , _ , eq_f2 , a⊑a_f , _
    with refl ← +-inj-fst (trans (sym eq_f2) eq_r)
    with refl ← +-inj-snd (trans (sym eq_f2) eq_r)
    with FC.extract-minimal f
           ((_ isSlice σ₀_r⊑e) ⇑ (_ isSlice ψ_rf⊑τ₀) ∈ d_rf ⊒
              unmatch+-min-least τ₀ eq ς₁ ⊥ₛ ψ_rf⊑τ₀ eq_f
                (⊑.trans {A = Typ} ih-hd a⊑a_f) ⊑□)
           (subst (σ_r₀ ⊑e_) (sym (cong (λ x → x .↓) (FC.extract-σ f))) σ_r⊑σ₀)
  ... | ih-fix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) ih-fix
  ... | eqσ =
        ⊑case₁ (⊑.reflexive {A = Exp} eqσ) ih-κ ⊑□ ,
        ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₀} {γ₁} {Γ_r}
          (FC.extract-ctx-min f
             (subst (λ x → _ , Γ_r .↓ ⊢ x ⇑ _) (sym eqσ) D_r)
             (unmatch+-min-least τ₀ eq ς₁ ⊥ₛ τ₀r⊑τ₀ eq_r ih-hd ⊑□)
             (Γ_r .proof))
          ih-tl ,
        ih-υ
  extract-pos-least {Γ₀ = Γ₀} (minAcase₁ {τ₀ = τ₀} {D = D} {eq = eq} {ς₁ = ς₁} {γ₁ = γ₁} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      ((case σ_r₀ of _ ·₁ _) isSlice ⊑case₁ σ₀_r⊑e κ_r₁⊑C _) Γ_r υ_or
      (⊑case₁ σ_r⊑σ₀ κ_r₁⊑κ _) υ⊑ϕ ϕ⊑τ (aSub (scase₁ D_r eq_r cls_r d₂_r con_r) con')
    with syn-precision (Γ_r .proof) σ₀_r⊑e D D_r
  ... | τ₀r⊑τ₀
    with ⊔-+-⊑ τ₀r⊑τ₀ eq
  ... | _ , _ , eq_ra , a⊑τ₁ , _
    with refl ← +-inj-fst (trans (sym eq_ra) eq_r)
    with refl ← +-inj-snd (trans (sym eq_ra) eq_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) ((_ isSlice a⊑τ₁) ∷ₛ Γ_r) ⊥ₛ κ_r₁⊑κ υ⊑ϕ ϕ⊑τ
           (aSub cls_r ~?₂)
  ... | ih-κ , ⊑∷ ih-hd ih-tl , ih-υ
    with static-gradual-syn (⊑.refl {A = Assms}) σ₀_r⊑e D
  ... | ψ_rf , d_rf , ψ_rf⊑τ₀
    with ⊔-+-⊑ ψ_rf⊑τ₀ eq
  ... | a_f , _ , eq_f , _ , _
    with ⊔-+-⊑ (syn-precision (Γ_r .proof) (⊑.refl {A = Exp}) d_rf D_r) eq_f
  ... | _ , _ , eq_f2 , a⊑a_f , _
    with refl ← +-inj-fst (trans (sym eq_f2) eq_r)
    with refl ← +-inj-snd (trans (sym eq_f2) eq_r)
    with FC.extract-minimal f
           ((_ isSlice σ₀_r⊑e) ⇑ (_ isSlice ψ_rf⊑τ₀) ∈ d_rf ⊒
              unmatch+-min-least τ₀ eq ς₁ ⊥ₛ ψ_rf⊑τ₀ eq_f
                (⊑.trans {A = Typ} ih-hd a⊑a_f) ⊑□)
           (subst (σ_r₀ ⊑e_) (sym (cong (λ x → x .↓) (FC.extract-σ f))) σ_r⊑σ₀)
  ... | ih-fix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) ih-fix
  ... | eqσ =
        ⊑case₁ (⊑.reflexive {A = Exp} eqσ) ih-κ ⊑□ ,
        ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₀} {γ₁} {Γ_r}
          (FC.extract-ctx-min f
             (subst (λ x → _ , Γ_r .↓ ⊢ x ⇑ _) (sym eqσ) D_r)
             (unmatch+-min-least τ₀ eq ς₁ ⊥ₛ τ₀r⊑τ₀ eq_r ih-hd ⊑□)
             (Γ_r .proof))
          ih-tl ,
        subst (_⊑t (υ_or .↓)) (sym (⊑□-inv ih-υ)) ⊑□

  extract-pos-least {Γ₀ = Γ₀} (minAcase₂ {τ₀ = τ₀} {D = D} {eq = eq} {ς₂ = ς₂} {γ₂ = γ₂} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      ((case σ_r₀ of₂ _ · _) isSlice ⊑case₂ σ₀_r⊑e _ κ_r₁⊑C) Γ_r υ_or
      (⊑case₂ σ_r⊑σ₀ _ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (acase₂ D_r eq_r d₁_r cls_r)
    with syn-precision (Γ_r .proof) σ₀_r⊑e D D_r
  ... | τ₀r⊑τ₀
    with ⊔-+-⊑ τ₀r⊑τ₀ eq
  ... | _ , _ , eq_ra , _ , b⊑τ₂
    with refl ← +-inj-fst (trans (sym eq_ra) eq_r)
    with refl ← +-inj-snd (trans (sym eq_ra) eq_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) ((_ isSlice b⊑τ₂) ∷ₛ Γ_r) υ_or κ_r₁⊑κ υ⊑ϕ ϕ⊑τ cls_r
  ... | ih-κ , ⊑∷ ih-hd ih-tl , ih-υ
    with static-gradual-syn (⊑.refl {A = Assms}) σ₀_r⊑e D
  ... | ψ_rf , d_rf , ψ_rf⊑τ₀
    with ⊔-+-⊑ ψ_rf⊑τ₀ eq
  ... | _ , b_f , eq_f , _ , _
    with ⊔-+-⊑ (syn-precision (Γ_r .proof) (⊑.refl {A = Exp}) d_rf D_r) eq_f
  ... | _ , _ , eq_f2 , _ , b⊑b_f
    with refl ← +-inj-fst (trans (sym eq_f2) eq_r)
    with refl ← +-inj-snd (trans (sym eq_f2) eq_r)
    with FC.extract-minimal f
           ((_ isSlice σ₀_r⊑e) ⇑ (_ isSlice ψ_rf⊑τ₀) ∈ d_rf ⊒
              unmatch+-min-least τ₀ eq ⊥ₛ ς₂ ψ_rf⊑τ₀ eq_f ⊑□
                (⊑.trans {A = Typ} ih-hd b⊑b_f))
           (subst (σ_r₀ ⊑e_) (sym (cong (λ x → x .↓) (FC.extract-σ f))) σ_r⊑σ₀)
  ... | ih-fix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) ih-fix
  ... | eqσ =
        ⊑case₂ (⊑.reflexive {A = Exp} eqσ) ⊑□ ih-κ ,
        ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₀} {γ₂} {Γ_r}
          (FC.extract-ctx-min f
             (subst (λ x → _ , Γ_r .↓ ⊢ x ⇑ _) (sym eqσ) D_r)
             (unmatch+-min-least τ₀ eq ⊥ₛ ς₂ τ₀r⊑τ₀ eq_r ⊑□ ih-hd)
             (Γ_r .proof))
          ih-tl ,
        ih-υ
  extract-pos-least {Γ₀ = Γ₀} (minAcase₂ {τ₀ = τ₀} {D = D} {eq = eq} {ς₂ = ς₂} {γ₂ = γ₂} {σ₀ = σ₀} {γ₀ = γ₀} c f)
      ((case σ_r₀ of₂ _ · _) isSlice ⊑case₂ σ₀_r⊑e _ κ_r₁⊑C) Γ_r υ_or
      (⊑case₂ σ_r⊑σ₀ _ κ_r₁⊑κ) υ⊑ϕ ϕ⊑τ (aSub (scase₂ D_r eq_r d₁_r cls_r con_r) con')
    with syn-precision (Γ_r .proof) σ₀_r⊑e D D_r
  ... | τ₀r⊑τ₀
    with ⊔-+-⊑ τ₀r⊑τ₀ eq
  ... | _ , _ , eq_ra , _ , b⊑τ₂
    with refl ← +-inj-fst (trans (sym eq_ra) eq_r)
    with refl ← +-inj-snd (trans (sym eq_ra) eq_r)
    with extract-pos-least c (_ isSlice κ_r₁⊑C) ((_ isSlice b⊑τ₂) ∷ₛ Γ_r) ⊥ₛ κ_r₁⊑κ υ⊑ϕ ϕ⊑τ
           (aSub cls_r ~?₂)
  ... | ih-κ , ⊑∷ ih-hd ih-tl , ih-υ
    with static-gradual-syn (⊑.refl {A = Assms}) σ₀_r⊑e D
  ... | ψ_rf , d_rf , ψ_rf⊑τ₀
    with ⊔-+-⊑ ψ_rf⊑τ₀ eq
  ... | _ , b_f , eq_f , _ , _
    with ⊔-+-⊑ (syn-precision (Γ_r .proof) (⊑.refl {A = Exp}) d_rf D_r) eq_f
  ... | _ , _ , eq_f2 , _ , b⊑b_f
    with refl ← +-inj-fst (trans (sym eq_f2) eq_r)
    with refl ← +-inj-snd (trans (sym eq_f2) eq_r)
    with FC.extract-minimal f
           ((_ isSlice σ₀_r⊑e) ⇑ (_ isSlice ψ_rf⊑τ₀) ∈ d_rf ⊒
              unmatch+-min-least τ₀ eq ⊥ₛ ς₂ ψ_rf⊑τ₀ eq_f ⊑□
                (⊑.trans {A = Typ} ih-hd b⊑b_f))
           (subst (σ_r₀ ⊑e_) (sym (cong (λ x → x .↓) (FC.extract-σ f))) σ_r⊑σ₀)
  ... | ih-fix
    with trans (sym (cong (λ x → x .↓) (FC.extract-σ f))) ih-fix
  ... | eqσ =
        ⊑case₂ (⊑.reflexive {A = Exp} eqσ) ⊑□ ih-κ ,
        ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ₀} {γ₀} {γ₂} {Γ_r}
          (FC.extract-ctx-min f
             (subst (λ x → _ , Γ_r .↓ ⊢ x ⇑ _) (sym eqσ) D_r)
             (unmatch+-min-least τ₀ eq ⊥ₛ ς₂ τ₀r⊑τ₀ eq_r ⊑□ ih-hd)
             (Γ_r .proof))
          ih-tl ,
        subst (_⊑t (υ_or .↓)) (sym (⊑□-inv ih-υ)) ⊑□

extract-minimal : ∀ {n Γ₀ C n_f Γ τ τ_p}
                    {Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ]}
                    {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {γ : ⌊ Γ₀ ⌋}
                → (c : Cls ◂ υ ⤳ κ ⊣ γ)
                → IsMinimal (extract c)
extract-minimal c s' (κ⊑ , γ⊑)
  with s' .valid
... | _ , _ , cls
  with extract-least c (s' .κ) (s' .γ) κ⊑ (s' .focus⊒) (s' .focus .proof) cls
... | ih-κ , ih-γ = ih-κ , ih-γ

extract-pos-minimal : ∀ {n Γ₀ C n_f Γ τ τ_p}
                        {Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ]}
                        {υ : ⌊ τ ⌋} {κ : ⌊ C ⌋} {υ_outer : ⌊ τ_p ⌋} {γ : ⌊ Γ₀ ⌋}
                    → (c : Cls ◂ υ ⤳ κ ⇓ υ_outer ⊣ γ)
                    → IsMinimalPos (extract-pos c)
extract-pos-minimal c s' (κ⊑ , γ⊑ , υo⊑)
  with ana-valid s'
... | _ , _ , cls
  with extract-pos-least c (ana-κ s') (ana-γ s') (ana-υ_outer s')
         κ⊑ (ana-focus⊒ s') (ana-focus s' .proof) cls
... | ih-κ , ih-γ , ih-υ = ih-κ , ih-γ , ih-υ

-- Totality: every classification and query has a calculus derivation.
-- Parametrised by a total fixedassms slicer (FixedAssmsSlicing.slice once
-- its case fixed point is complete) so this module stays free of its
-- unsolved parts.
module Total
    (fixslice : ∀ {n Γ e τ} (D : n , Γ ⊢ e ⇑ τ) (q : ⌊ τ ⌋)
                → ∃[ σ ] ∃[ ψ ] ∃[ γ ] (D FC.◂ q ⤳ σ ⇑ ψ ⊣ γ))
    where

  mutual
    ana-slice : ∀ {n Γ₀ C n_f Γ τ τ_p}
              → (Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ])
              → (υ : ⌊ τ ⌋)
              → ∃[ κ ] ∃[ γ ] (Cls ◂ υ ⤳ κ ⊣ γ)

    ana-slice-pos : ∀ {n Γ₀ C n_f Γ τ τ_p}
                  → (Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ])
                  → (υ : ⌊ τ ⌋)
                  → ∃[ κ ] Σ[ υ_outer ∈ ⌊ τ_p ⌋ ] ∃[ γ ] (Cls ◂ υ ⤳ κ ⇓ υ_outer ⊣ γ)

    ana-slice (sλ: wf Cls') υ
      with ana-slice Cls' υ
    ... | κ , ((_ ∷ _) isSlice ⊑∷ h t) , c = _ , _ , minSλ: c
    ana-slice (s∘₁ Cls' eq d₂) υ
      with ana-slice Cls' υ
    ... | κ , γ , c = _ , _ , minS∘₁ c
    ana-slice (s∘₂ D₁ eq Cls') υ
      with ana-slice-pos Cls' υ
    ... | κ , υo , γ' , cₚ
      with fixslice D₁ (unmatch⇒-min eq υo ⊥ₛ)
    ... | σ , ψ , γ₁ , f = _ , _ , minS∘₂ cₚ f
    ana-slice (s<>₁ Cls' eq wf) υ
      with ana-slice Cls' υ
    ... | κ , γ , c = _ , _ , minS<>₁ c
    ana-slice (s&₁ Cls' d₂) υ
      with ana-slice Cls' υ
    ... | κ , γ , c = _ , _ , minS&₁ c
    ana-slice (s&₂ d₁ Cls') υ
      with ana-slice Cls' υ
    ... | κ , γ , c = _ , _ , minS&₂ c
    ana-slice (sι₁ Cls') υ
      with ana-slice Cls' υ
    ... | κ , γ , c = _ , _ , minSι₁ c
    ana-slice (sι₂ Cls') υ
      with ana-slice Cls' υ
    ... | κ , γ , c = _ , _ , minSι₂ c
    ana-slice (scase₁ D eq Cls' d₂ con) υ
      with ana-slice Cls' υ
    ... | κ , ((_ ∷ _) isSlice ⊑∷ h t) , c
      with fixslice D (unmatch+-min eq (_ isSlice h) ⊥ₛ)
    ... | σ₀ , ψ₀ , γ₀ , f = _ , _ , minScase₁ c f
    ana-slice (scase₂ D eq d₁ Cls' con) υ
      with ana-slice Cls' υ
    ... | κ , ((_ ∷ _) isSlice ⊑∷ h t) , c
      with fixslice D (unmatch+-min eq ⊥ₛ (_ isSlice h))
    ... | σ₀ , ψ₀ , γ₀ , f = _ , _ , minScase₂ c f
    ana-slice (sπ₁ Cls' eq) υ
      with ana-slice Cls' υ
    ... | κ , γ , c = _ , _ , minSπ₁ c
    ana-slice (sπ₂ Cls' eq) υ
      with ana-slice Cls' υ
    ... | κ , γ , c = _ , _ , minSπ₂ c
    ana-slice (sΛ Cls') υ
      with ana-slice Cls' υ
    ... | κ , γ , c = _ , _ , minSΛ c
    ana-slice (sdef₁ Cls' d₂) υ
      with ana-slice Cls' υ
    ... | κ , γ , c = _ , _ , minSdef₁ c
    ana-slice (sdef₂ D Cls') υ
      with ana-slice Cls' υ
    ... | κ , ((_ ∷ _) isSlice ⊑∷ h t) , c
      with fixslice D (_ isSlice h)
    ... | σ₁ , ψ₁ , γ₁ , f = _ , _ , minSdef₂ c f

    ana-slice-pos a○ υ = _ , _ , _ , minA○ υ
    ana-slice-pos (aSub Cls' con) υ
      with ana-slice Cls' υ
    ... | κ , γ , c = _ , _ , _ , minASub c
    ana-slice-pos (aλ: con eq wf Cls') υ
      with ana-slice-pos Cls' υ
    ... | κ , υ_b , ((_ ∷ _) isSlice ⊑∷ h t) , c = _ , _ , _ , minAλ: c
    ana-slice-pos (aλ⇒ eq Cls') υ
      with ana-slice-pos Cls' υ
    ... | κ , υ_b , ((_ ∷ _) isSlice ⊑∷ h t) , c = _ , _ , _ , minAλ⇒ c
    ana-slice-pos (a&₁ eq Cls' d₂) υ
      with ana-slice-pos Cls' υ
    ... | κ , υ_b , γ , c = _ , _ , _ , minA&₁ c
    ana-slice-pos (a&₂ eq d₁ Cls') υ
      with ana-slice-pos Cls' υ
    ... | κ , υ_b , γ , c = _ , _ , _ , minA&₂ c
    ana-slice-pos (aι₁ eq Cls') υ
      with ana-slice-pos Cls' υ
    ... | κ , υ_b , γ , c = _ , _ , _ , minAι₁ c
    ana-slice-pos (aι₂ eq Cls') υ
      with ana-slice-pos Cls' υ
    ... | κ , υ_b , γ , c = _ , _ , _ , minAι₂ c
    ana-slice-pos (acase₁ D eq Cls' d₂) υ
      with ana-slice-pos Cls' υ
    ... | κ , υ_b , ((_ ∷ _) isSlice ⊑∷ h t) , c
      with fixslice D (unmatch+-min eq (_ isSlice h) ⊥ₛ)
    ... | σ₀ , ψ₀ , γ₀ , f = _ , _ , _ , minAcase₁ c f
    ana-slice-pos (acase₂ D eq d₁ Cls') υ
      with ana-slice-pos Cls' υ
    ... | κ , υ_b , ((_ ∷ _) isSlice ⊑∷ h t) , c
      with fixslice D (unmatch+-min eq ⊥ₛ (_ isSlice h))
    ... | σ₀ , ψ₀ , γ₀ , f = _ , _ , _ , minAcase₂ c f
    ana-slice-pos (adef₁ Cls' d₂) υ
      with ana-slice Cls' υ
    ... | κ , γ , c = _ , _ , _ , minAdef₁ c
    ana-slice-pos (adef₂ D Cls') υ
      with ana-slice-pos Cls' υ
    ... | κ , υ_b , ((_ ∷ _) isSlice ⊑∷ h t) , c
      with fixslice D (_ isSlice h)
    ... | σ₁ , ψ₁ , γ₁ , f = _ , _ , _ , minAdef₂ c f

  slice-ana : ∀ {n Γ₀ C n_f Γ τ τ_p}
            → (Cls : n , Γ₀ ⊢ C at synPos τ_p ▷ n_f , Γ [ ⇐mode τ ])
            → (υ : ⌊ τ ⌋)
            → AnaSlice Cls υ
  slice-ana Cls υ with ana-slice Cls υ
  ... | _ , _ , c = extract c

  slice-ana-pos : ∀ {n Γ₀ C n_f Γ τ τ_p}
                → (Cls : n , Γ₀ ⊢ C at anaPos τ_p ▷ n_f , Γ [ ⇐mode τ ])
                → (υ : ⌊ τ ⌋)
                → AnaPosSlice Cls υ
  slice-ana-pos Cls υ with ana-slice-pos Cls υ
  ... | _ , _ , _ , c = extract-pos c
