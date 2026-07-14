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

