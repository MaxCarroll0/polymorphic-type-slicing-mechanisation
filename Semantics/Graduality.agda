-- Static gradual guarantee for the core calculus (synthesis, analysis, and the context-classified
-- variants), plus synthesis unicity (Theorem 4.17) and precision (Corollary 4.18).
-- Dissertation: §4.5 Metatheory: Graduality & Unicity.
module Semantics.Graduality where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.List using ([]; _∷_)
open import Data.Product using (∃; Σ; _,_; Σ-syntax; ∃-syntax)
open import Data.Product using () renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂; trans; cong)
open import Core
open import Semantics.Statics.Typing
open import Semantics.Statics.CtxTyping

-- Precision relation on focus modes. A classification's focus mode tracks
-- the type the focus hole is checked at. Modes are propagated unchanged
-- through every classification rule, so the relation just lifts τ-precision
data mode-⊑ : CtxMode → CtxMode → Set where
  ⇒mode-⊑ : ∀ {τ₁ τ₂} → τ₁ ⊑ τ₂ → mode-⊑ (⇒mode τ₁) (⇒mode τ₂)
  ⇐mode-⊑ : ∀ {τ₁ τ₂} → τ₁ ⊑ τ₂ → mode-⊑ (⇐mode τ₁) (⇐mode τ₂)



-- Static gradual guarantee
-- Dissertation: Theorem 4.13 thm:graduality-syn (Static Gradual Guarantee - Synthesis), §4.5.
-- The companion analysis case (static-gradual-ana below) is Theorem 4.14 thm:graduality-ana.
mutual
  static-gradual-syn : ∀ {n Γ₁ Γ₂ e₁ e₂ τ₂} →
    Γ₁ ⊑ Γ₂ → e₁ ⊑ e₂ →
    n , Γ₂ ⊢ e₂ ⇑ τ₂ →
    Σ[ τ₁ ∈ Typ ] n , Γ₁ ⊢ e₁ ⇑ τ₁ ∧ τ₁ ⊑ τ₂

  static-gradual-syn Γ⊑ ⊑□ _ = □ , ⇑□ , ⊑□
  static-gradual-syn Γ⊑ ⊑* ⇑* = * , ⇑* , ⊑*
  static-gradual-syn Γ⊑ ⊑Var (⇑Var p)
    with lookup-⊑ Γ⊑ p
  ...  | τ₁ , p₁ , τ⊑ = τ₁ , ⇑Var p₁ , τ⊑
  static-gradual-syn Γ⊑ (⊑λ τ⊑ e⊑) (⇑λ: wf₂ D₂)
    with static-gradual-syn (⊑∷ τ⊑ Γ⊑) e⊑ D₂
  ...  | τ₁b , D₁ , τb⊑ = _ ⇒ τ₁b , ⇑λ: (wf-⊑ wf₂ τ⊑) D₁ , ⊑⇒ τ⊑ τb⊑
  static-gradual-syn Γ⊑ (⊑& p q) (⇑& D₁ D₂)
    with static-gradual-syn Γ⊑ p D₁ | static-gradual-syn Γ⊑ q D₂
  ...  | τ₁ , D₁' , p₁ | τ₂ , D₂' , p₂ = (τ₁ × τ₂) , ⇑& D₁' D₂' , ⊑× p₁ p₂
  static-gradual-syn Γ⊑ (⊑Λ e⊑) (⇑Λ D₂)
    with static-gradual-syn (shiftΓ-⊑ Γ⊑) e⊑ D₂
  ...  | τ₁ , D₁ , τ⊑ = ∀· τ₁ , ⇑Λ D₁ , ⊑∀ τ⊑
  static-gradual-syn Γ⊑ (⊑def p q) (⇑def D₁ D₂)
    with static-gradual-syn Γ⊑ p D₁
  ...  | τ₁' , D₁'  , p₁ with static-gradual-syn (⊑∷ p₁ Γ⊑) q D₂
  ...                       | τ₁  , D₁'' , q₁ = τ₁ , ⇑def D₁' D₁'' , q₁
  static-gradual-syn Γ⊑ (⊑∘ p q) (⇑∘ D₂ m Da₂)
    with static-gradual-syn Γ⊑ p D₂
  ...  | τ₁ , D₁ , τ⊑ with ⊔-⇒-⊑ τ⊑ m
  ...                   | τ₁a , τ₁b , m₁ , pa , pb
                        with static-gradual-ana Γ⊑ q pa Da₂
  ...                      | Da₁ = τ₁b , ⇑∘ D₁ m₁ Da₁ , pb
  static-gradual-syn Γ⊑ (⊑<> e⊑ σ⊑) (⇑<> D₂ m wf₂)
    with static-gradual-syn Γ⊑ e⊑ D₂
  ...  | τ₁ , D₁ , τ⊑ with ⊔-∀-⊑ τ⊑ m
  ...                    | τ₁' , m₁ , p
                         = _ , ⇑<> D₁ m₁ (wf-⊑ wf₂ σ⊑) , sub-⊑ zero σ⊑ p
  static-gradual-syn Γ⊑ (⊑π₁ e⊑) (⇑π₁ D₂ m)
    with static-gradual-syn Γ⊑ e⊑ D₂
  ...  | τ₁ , D₁ , τ⊑ with ⊔-×-⊑ τ⊑ m
  ...                    | τ₁a , τ₁b , m₁ , pa , pb
                         = τ₁a , ⇑π₁ D₁ m₁ , pa

  static-gradual-syn Γ⊑ (⊑π₂ e⊑) (⇑π₂ D₂ m)
    with static-gradual-syn Γ⊑ e⊑ D₂
  ... | τ₁ , D₁ , τ⊑ with ⊔-×-⊑ τ⊑ m
  ...                   | τ₁a , τ₁b , m₁ , pa , pb
                        = τ₁b , ⇑π₂ D₁ m₁ , pb

  static-gradual-syn Γ⊑ (⊑ι₁ e⊑) (⇑ι₁ D₂)
    with static-gradual-syn Γ⊑ e⊑ D₂
  ...  | τ₁ , D₁ , τ⊑ = τ₁ + □ , ⇑ι₁ D₁ , ⊑+ τ⊑ ⊑□

  static-gradual-syn Γ⊑ (⊑ι₂ e⊑) (⇑ι₂ D₂)
    with static-gradual-syn Γ⊑ e⊑ D₂
  ...  | τ₁ , D₁ , τ⊑ = □ + τ₁ , ⇑ι₂ D₁ , ⊑+ ⊑□ τ⊑

  static-gradual-syn Γ⊑ (⊑case e⊑ e₁⊑ e₂⊑) (⇑case D₂ m D₂₁ D₂₂ c)
    with static-gradual-syn Γ⊑ e⊑ D₂
  ...  | τs , Ds , τs⊑
    with ⊔-+-⊑ τs⊑ m
  ...  | τa , τb , m₁ , pa , pb
    with static-gradual-syn (⊑∷ pa Γ⊑) e₁⊑ D₂₁ | static-gradual-syn (⊑∷ pb Γ⊑) e₂⊑ D₂₂
  ...  | τl , Dl , pl                          | τr , Dr , pr
       = τl ⊔ τr , ⇑case Ds m₁ Dl Dr (~-⊑-down c pl pr) , ⊔-mono-⊑ c pl pr

  -- Analysis gradual guarantee
  static-gradual-ana : ∀ {n Γ₁ Γ₂ e₁ e₂ τ₁ τ₂} →
    Γ₁ ⊑ Γ₂ → e₁ ⊑ e₂ → τ₁ ⊑ τ₂ →
    n , Γ₂ ⊢ e₂ ⇓ τ₂ →
    n , Γ₁ ⊢ e₁ ⇓ τ₁

  static-gradual-ana Γ⊑ ⊑□ τ⊑ _ = ⇓Sub ⇑□ ~?₁
  -- Subsumption
  static-gradual-ana Γ⊑ e⊑ τ⊑ (⇓Sub D₂ c)
    with static-gradual-syn Γ⊑ e⊑ D₂
  ...  | τ₁' , D₁ , τ'⊑ = ⇓Sub D₁ (~-⊑-down c τ⊑ τ'⊑)
  static-gradual-ana Γ⊑ (⊑λu e⊑) τ⊑ (⇓λ m Da₂)
    with ⊔-⇒-⊑ τ⊑ m
  ...  | τ₁a , τ₁b , m₁ , pa , pb
       = ⇓λ m₁ (static-gradual-ana (⊑∷ pa Γ⊑) e⊑ pb Da₂)
  static-gradual-ana Γ⊑ (⊑λ τa⊑ e⊑) τ⊑ (⇓λ: c₂ m₂ wf₂ Da₂)
    with ⊔-ann-⇒-⊑ τ⊑ τa⊑ m₂
  ...  | _ , _ , m₁ , pb
       = ⇓λ: (~-⊑-down c₂ τ⊑ (⊑⇒ τa⊑ ⊑□)) m₁ (wf-⊑ wf₂ τa⊑)
                (static-gradual-ana (⊑∷ τa⊑ Γ⊑) e⊑ pb Da₂)
  static-gradual-ana Γ⊑ (⊑ι₁ e⊑) τ⊑ (⇓ι₁ m Da₂)
    with ⊔-+-⊑ τ⊑ m
  ...  | τ₁a , τ₁b , m₁ , pa , pb
       = ⇓ι₁ m₁ (static-gradual-ana Γ⊑ e⊑ pa Da₂)
  static-gradual-ana Γ⊑ (⊑ι₂ e⊑) τ⊑ (⇓ι₂ m Da₂)
    with ⊔-+-⊑ τ⊑ m
  ...  | τ₁a , τ₁b , m₁ , pa , pb
       = ⇓ι₂ m₁ (static-gradual-ana Γ⊑ e⊑ pb Da₂)
  static-gradual-ana Γ⊑ (⊑& e₁⊑ e₂⊑) τ⊑ (⇓& m Da₁ Da₂)
    with ⊔-×-⊑ τ⊑ m
  ...  | τ₁a , τ₁b , m₁ , pa , pb
       = ⇓& m₁ (static-gradual-ana Γ⊑ e₁⊑ pa Da₁)
               (static-gradual-ana Γ⊑ e₂⊑ pb Da₂)
  static-gradual-ana Γ⊑ (⊑case e⊑ e₁⊑ e₂⊑) τ⊑ (⇓case Ds₂ m Da₁ Da₂)
    with static-gradual-syn Γ⊑ e⊑ Ds₂
  ...  | τs , Ds , τs⊑ with ⊔-+-⊑ τs⊑ m
  ...  | τa , τb , m₁ , pa , pb
       = ⇓case Ds m₁ (static-gradual-ana (⊑∷ pa Γ⊑) e₁⊑ τ⊑ Da₁)
                     (static-gradual-ana (⊑∷ pb Γ⊑) e₂⊑ τ⊑ Da₂)
  static-gradual-ana Γ⊑ (⊑def e₁⊑ e₂⊑) τ⊑ (⇓def Ds₂ Da₂)
    with static-gradual-syn Γ⊑ e₁⊑ Ds₂
  ...  | τ₁' , Ds₁ , p₁
       = ⇓def Ds₁ (static-gradual-ana (⊑∷ p₁ Γ⊑) e₂⊑ τ⊑ Da₂)

-- Static gradual guarantee for context classifications.
--
-- For ana-cls, τ_p₁ is INPUT (caller specifies the desired position type at
-- level 1, with τ_p₁ ⊑ τ_p₂); for syn-cls, τ_p₁ is OUTPUT. m₁ and the
-- mode-⊑ proof are OUTPUT for both — the leaf rule (s○ or a○) couples the
-- focus mode's type with the leaf position type, so both are determined by
-- the lemma's recursive construction.
--
-- The asymmetry mirrors `static-gradual-{syn,ana}` and is essential for the
-- s∘₂ case in syn-cls, where the function's lifted dom (from ⊔-⇒-⊑) must
-- become the inner ana-cls's position type.
mutual
  static-gradual-syn-cls : ∀ {n Γ₁ Γ₂ C₁ C₂ n_f Γ_f τ_p₂ m₂}
    → Γ₁ ⊑ Γ₂ → C₁ ⊑c C₂
    → n , Γ₂ ⊢ C₂ at synPos τ_p₂ ▷ n_f , Γ_f [ m₂ ]
    → ∃[ τ_p₁ ] ∃[ Γ_f₁ ] ∃[ n_f₁ ] ∃[ m₁ ]
        (τ_p₁ ⊑ τ_p₂) ∧ (Γ_f₁ ⊑ Γ_f) ∧ mode-⊑ m₁ m₂ ∧
        (n , Γ₁ ⊢ C₁ at synPos τ_p₁ ▷ n_f₁ , Γ_f₁ [ m₁ ])

  static-gradual-ana-cls : ∀ {n Γ₁ Γ₂ C₁ C₂ n_f Γ_f τ_p₁ τ_p₂ m₂}
    → Γ₁ ⊑ Γ₂ → C₁ ⊑c C₂ → τ_p₁ ⊑ τ_p₂
    → n , Γ₂ ⊢ C₂ at anaPos τ_p₂ ▷ n_f , Γ_f [ m₂ ]
    → ∃[ Γ_f₁ ] ∃[ n_f₁ ] ∃[ m₁ ]
        (Γ_f₁ ⊑ Γ_f) ∧ mode-⊑ m₁ m₂ ∧
        (n , Γ₁ ⊢ C₁ at anaPos τ_p₁ ▷ n_f₁ , Γ_f₁ [ m₁ ])

  -- s○: synthesis hole. Outer τ_p = focus τ. Use τ_p₁ := τ_p₂ (refl).
  static-gradual-syn-cls Γ⊑ ⊑○ s○
    = _ , _ , _ , _ , ⊑.refl {Typ} , Γ⊑ , ⇒mode-⊑ (⊑.refl {Typ}) , s○

  -- sλ:: annotated lambda. Inner over (τ_a ∷ Γ); ⊑λ gives τ_a₁ ⊑ τ_a.
  static-gradual-syn-cls Γ⊑ (⊑λ τ_a⊑ C'⊑) (sλ: wf₂ Cls')
    with static-gradual-syn-cls (⊑∷ τ_a⊑ Γ⊑) C'⊑ Cls'
  ... | τ₂_₁ , _ , _ , _ , τ₂⊑ , Γ_f⊑ , m⊑ , inner-cls
      = _ ⇒ τ₂_₁ , _ , _ , _ , ⊑⇒ τ_a⊑ τ₂⊑ , Γ_f⊑ , m⊑
          , sλ: (wf-⊑ wf₂ τ_a⊑) inner-cls

  -- s∘₁: outer C ∘₁ e. Recurse on cls; lift sibling d₂ via static-gradual-ana
  -- with the lifted dom precision.
  static-gradual-syn-cls Γ⊑ (⊑∘₁ C'⊑ e⊑) (s∘₁ Cls' eq d₂)
    with static-gradual-syn-cls Γ⊑ C'⊑ Cls'
  ... | τ_₁ , _ , _ , _ , τ⊑ , Γ_f⊑ , m⊑ , inner-cls
    with ⊔-⇒-⊑ τ⊑ eq
  ... | τ_a , τ_b , eq_₁ , pa , pb
      = τ_b , _ , _ , _ , pb , Γ_f⊑ , m⊑
          , s∘₁ inner-cls eq_₁ (static-gradual-ana Γ⊑ e⊑ pa d₂)

  -- s∘₂: outer e ∘₂ C. Lift D₁ via static-gradual-syn → τ_₁ ⊑ τ; decompose
  -- ⊔-⇒-⊑ τ_₁⊑τ eq → τ_₁_a ⊑ τ_a, τ_₁_b ⊑ τ_b, eq_₁. Use INPUT-style
  -- ana-cls with target τ_₁_a to get the inner cls at exactly the dom we
  -- need. This is the case that motivated the asymmetric design.
  static-gradual-syn-cls Γ⊑ (⊑∘₂ e⊑ C'⊑) (s∘₂ D₁ eq Cls')
    with static-gradual-syn Γ⊑ e⊑ D₁
  ... | τ_₁ , D₁_₁ , τ_₁⊑τ
    with ⊔-⇒-⊑ τ_₁⊑τ eq
  ... | τ_₁_a , τ_₁_b , eq_₁ , pa , pb
    with static-gradual-ana-cls Γ⊑ C'⊑ pa Cls'
  ... | _ , _ , _ , Γ_f⊑ , m⊑ , inner-cls
      = τ_₁_b , _ , _ , _ , pb , Γ_f⊑ , m⊑ , s∘₂ D₁_₁ eq_₁ inner-cls

  static-gradual-syn-cls Γ⊑ (⊑<>₁ C'⊑ σ⊑) (s<>₁ Cls' eq wf)
    with static-gradual-syn-cls Γ⊑ C'⊑ Cls'
  ... | τ_₁ , _ , _ , _ , τ⊑ , Γ_f⊑ , m⊑ , inner-cls
    with ⊔-∀-⊑ τ⊑ eq
  ... | τ'_₁ , eq_₁ , p
      = _ , _ , _ , _ , sub-⊑ zero σ⊑ p , Γ_f⊑ , m⊑
          , s<>₁ inner-cls eq_₁ (wf-⊑ wf σ⊑)

  static-gradual-syn-cls Γ⊑ (⊑&₁ C'⊑ e⊑) (s&₁ Cls' d₂)
    with static-gradual-syn-cls Γ⊑ C'⊑ Cls'
       | static-gradual-syn Γ⊑ e⊑ d₂
  ... | τ₁_₁ , _ , _ , _ , τ₁⊑ , Γ_f⊑ , m⊑ , inner-cls
      | τ₂_₁ , d₂_₁ , τ₂⊑
      = (τ₁_₁ × τ₂_₁) , _ , _ , _ , ⊑× τ₁⊑ τ₂⊑ , Γ_f⊑ , m⊑ , s&₁ inner-cls d₂_₁

  static-gradual-syn-cls Γ⊑ (⊑&₂ e⊑ C'⊑) (s&₂ d₁ Cls')
    with static-gradual-syn Γ⊑ e⊑ d₁
       | static-gradual-syn-cls Γ⊑ C'⊑ Cls'
  ... | τ₁_₁ , d₁_₁ , τ₁⊑
      | τ₂_₁ , _ , _ , _ , τ₂⊑ , Γ_f⊑ , m⊑ , inner-cls
      = (τ₁_₁ × τ₂_₁) , _ , _ , _ , ⊑× τ₁⊑ τ₂⊑ , Γ_f⊑ , m⊑ , s&₂ d₁_₁ inner-cls

  static-gradual-syn-cls Γ⊑ (⊑ι₁ C'⊑) (sι₁ Cls')
    with static-gradual-syn-cls Γ⊑ C'⊑ Cls'
  ... | τ_₁ , _ , _ , _ , τ⊑ , Γ_f⊑ , m⊑ , inner-cls
      = (τ_₁ + □) , _ , _ , _ , ⊑+ τ⊑ ⊑□ , Γ_f⊑ , m⊑ , sι₁ inner-cls

  static-gradual-syn-cls Γ⊑ (⊑ι₂ C'⊑) (sι₂ Cls')
    with static-gradual-syn-cls Γ⊑ C'⊑ Cls'
  ... | τ_₁ , _ , _ , _ , τ⊑ , Γ_f⊑ , m⊑ , inner-cls
      = (□ + τ_₁) , _ , _ , _ , ⊑+ ⊑□ τ⊑ , Γ_f⊑ , m⊑ , sι₂ inner-cls

  static-gradual-syn-cls Γ⊑ (⊑case₀ C'⊑ e₁⊑ e₂⊑) (scase₀ Cls' eq d₁ d₂ con)
    with static-gradual-syn-cls Γ⊑ C'⊑ Cls'
  ... | τ₀_₁ , _ , _ , _ , τ₀⊑ , Γ_f⊑ , m⊑ , inner-cls
    with ⊔-+-⊑ τ₀⊑ eq
  ... | τ₁_₁ , τ₂_₁ , eq_₁ , p₁ , p₂
    with static-gradual-syn (⊑∷ p₁ Γ⊑) e₁⊑ d₁
       | static-gradual-syn (⊑∷ p₂ Γ⊑) e₂⊑ d₂
  ... | τ₁'_₁ , d₁_₁ , τ₁'⊑
      | τ₂'_₁ , d₂_₁ , τ₂'⊑
      = (τ₁'_₁ ⊔ τ₂'_₁) , _ , _ , _ , ⊔-mono-⊑ con τ₁'⊑ τ₂'⊑ , Γ_f⊑ , m⊑
          , scase₀ inner-cls eq_₁ d₁_₁ d₂_₁ (~-⊑-down con τ₁'⊑ τ₂'⊑)

  static-gradual-syn-cls Γ⊑ (⊑case₁ e⊑ C'⊑ e'⊑) (scase₁ D eq Cls' d₂ con)
    with static-gradual-syn Γ⊑ e⊑ D
  ... | τ_₁ , D_₁ , τ⊑
    with ⊔-+-⊑ τ⊑ eq
  ... | τ₁_₁ , τ₂_₁ , eq_₁ , p₁ , p₂
    with static-gradual-syn-cls (⊑∷ p₁ Γ⊑) C'⊑ Cls'
       | static-gradual-syn (⊑∷ p₂ Γ⊑) e'⊑ d₂
  ... | τ₁'_₁ , _ , _ , _ , τ₁'⊑ , Γ_f⊑ , m⊑ , inner-cls
      | τ₂'_₁ , d₂_₁ , τ₂'⊑
      = (τ₁'_₁ ⊔ τ₂'_₁) , _ , _ , _ , ⊔-mono-⊑ con τ₁'⊑ τ₂'⊑ , Γ_f⊑ , m⊑
          , scase₁ D_₁ eq_₁ inner-cls d₂_₁ (~-⊑-down con τ₁'⊑ τ₂'⊑)

  static-gradual-syn-cls Γ⊑ (⊑case₂ e⊑ e'⊑ C'⊑) (scase₂ D eq d₁ Cls' con)
    with static-gradual-syn Γ⊑ e⊑ D
  ... | τ_₁ , D_₁ , τ⊑
    with ⊔-+-⊑ τ⊑ eq
  ... | τ₁_₁ , τ₂_₁ , eq_₁ , p₁ , p₂
    with static-gradual-syn (⊑∷ p₁ Γ⊑) e'⊑ d₁
       | static-gradual-syn-cls (⊑∷ p₂ Γ⊑) C'⊑ Cls'
  ... | τ₁'_₁ , d₁_₁ , τ₁'⊑
      | τ₂'_₁ , _ , _ , _ , τ₂'⊑ , Γ_f⊑ , m⊑ , inner-cls
      = (τ₁'_₁ ⊔ τ₂'_₁) , _ , _ , _ , ⊔-mono-⊑ con τ₁'⊑ τ₂'⊑ , Γ_f⊑ , m⊑
          , scase₂ D_₁ eq_₁ d₁_₁ inner-cls (~-⊑-down con τ₁'⊑ τ₂'⊑)

  static-gradual-syn-cls Γ⊑ (⊑π₁ C'⊑) (sπ₁ Cls' eq)
    with static-gradual-syn-cls Γ⊑ C'⊑ Cls'
  ... | τ_₁ , _ , _ , _ , τ⊑ , Γ_f⊑ , m⊑ , inner-cls
    with ⊔-×-⊑ τ⊑ eq
  ... | τ_a , τ_b , eq_₁ , pa , pb
      = τ_a , _ , _ , _ , pa , Γ_f⊑ , m⊑ , sπ₁ inner-cls eq_₁

  static-gradual-syn-cls Γ⊑ (⊑π₂ C'⊑) (sπ₂ Cls' eq)
    with static-gradual-syn-cls Γ⊑ C'⊑ Cls'
  ... | τ_₁ , _ , _ , _ , τ⊑ , Γ_f⊑ , m⊑ , inner-cls
    with ⊔-×-⊑ τ⊑ eq
  ... | τ_a , τ_b , eq_₁ , pa , pb
      = τ_b , _ , _ , _ , pb , Γ_f⊑ , m⊑ , sπ₂ inner-cls eq_₁

  static-gradual-syn-cls Γ⊑ (⊑Λ C'⊑) (sΛ Cls')
    with static-gradual-syn-cls (shiftΓ-⊑ Γ⊑) C'⊑ Cls'
  ... | τ_₁ , _ , _ , _ , τ⊑ , Γ_f⊑ , m⊑ , inner-cls
      = ∀· τ_₁ , _ , _ , _ , ⊑∀ τ⊑ , Γ_f⊑ , m⊑ , sΛ inner-cls

  static-gradual-syn-cls Γ⊑ (⊑def₁ C'⊑ e⊑) (sdef₁ Cls' d₂)
    with static-gradual-syn-cls Γ⊑ C'⊑ Cls'
  ... | τ'_₁ , _ , _ , _ , τ'⊑ , Γ_f⊑ , m⊑ , inner-cls
    with static-gradual-syn (⊑∷ τ'⊑ Γ⊑) e⊑ d₂
  ... | τ_₁ , d₂_₁ , τ⊑
      = τ_₁ , _ , _ , _ , τ⊑ , Γ_f⊑ , m⊑ , sdef₁ inner-cls d₂_₁

  static-gradual-syn-cls Γ⊑ (⊑def₂ e⊑ C'⊑) (sdef₂ D Cls')
    with static-gradual-syn Γ⊑ e⊑ D
  ... | τ'_₁ , D_₁ , τ'⊑
    with static-gradual-syn-cls (⊑∷ τ'⊑ Γ⊑) C'⊑ Cls'
  ... | τ_₁ , _ , _ , _ , τ⊑ , Γ_f⊑ , m⊑ , inner-cls
      = τ_₁ , _ , _ , _ , τ⊑ , Γ_f⊑ , m⊑ , sdef₂ D_₁ inner-cls

  -- a○: analysis hole. Apply a○ at level 1 with τ := τ_p₁; m₁ = [⇐mode τ_p₁].
  static-gradual-ana-cls Γ⊑ ⊑○ τ_p⊑ a○ = _ , _ , _ , Γ⊑ , ⇐mode-⊑ τ_p⊑ , a○

  -- aSub: cross from anaPos to synPos via consistency. Inner is syn-cls.
  static-gradual-ana-cls Γ⊑ C⊑ τ_p⊑ (aSub Cls'_syn c)
    with static-gradual-syn-cls Γ⊑ C⊑ Cls'_syn
  ... | τ'_₁ , _ , _ , _ , τ'⊑ , Γ_f⊑ , m⊑ , inner-cls
      = _ , _ , _ , Γ_f⊑ , m⊑ , aSub inner-cls (~-⊑-down c τ_p⊑ τ'⊑)

  -- aλ:: annotated lambda. Decompose τ_p_⊑ via outer eq and the annotation
  -- precision using ⊔-ann-⇒-⊑ to get τ_b₁ ⊑ τ_b and the lifted match eq_₁.
  -- Recurse with τ_b₁ as INPUT.
  static-gradual-ana-cls Γ⊑ (⊑λ τ_h⊑ C'⊑) τ_p⊑ (aλ: c eq wf Cls')
    with ⊔-ann-⇒-⊑ τ_p⊑ τ_h⊑ eq
  ... | τ_a₁ , τ_b₁ , eq_₁ , pb
    with static-gradual-ana-cls (⊑∷ τ_h⊑ Γ⊑) C'⊑ pb Cls'
  ... | _ , _ , _ , Γ_f⊑ , m⊑ , inner-cls
      = _ , _ , _ , Γ_f⊑ , m⊑
          , aλ: (~-⊑-down c τ_p⊑ (⊑⇒ τ_h⊑ ⊑□)) eq_₁ (wf-⊑ wf τ_h⊑) inner-cls

  -- aλ⇒: unannotated lambda. Like aλ: but no annotation precision needed.
  static-gradual-ana-cls Γ⊑ (⊑λu C'⊑) τ_p⊑ (aλ⇒ eq Cls')
    with ⊔-⇒-⊑ τ_p⊑ eq
  ... | τ_a₁ , τ_b₁ , eq_₁ , pa , pb
    with static-gradual-ana-cls (⊑∷ pa Γ⊑) C'⊑ pb Cls'
  ... | _ , _ , _ , Γ_f⊑ , m⊑ , inner-cls
      = _ , _ , _ , Γ_f⊑ , m⊑ , aλ⇒ eq_₁ inner-cls

  -- aι₁/aι₂/a&₁/a&₂: decompose τ_p_⊑ via outer match eq using ⊔-{+,×}-⊑
  -- to get component precisions. Recurse with appropriate component
  -- precision; lift sibling (for a&) via static-gradual-ana.
  static-gradual-ana-cls Γ⊑ (⊑ι₁ C'⊑) τ_p⊑ (aι₁ eq Cls')
    with ⊔-+-⊑ τ_p⊑ eq
  ... | τ_a₁ , τ_b₁ , eq_₁ , pa , pb
    with static-gradual-ana-cls Γ⊑ C'⊑ pa Cls'
  ... | _ , _ , _ , Γ_f⊑ , m⊑ , inner-cls
      = _ , _ , _ , Γ_f⊑ , m⊑ , aι₁ eq_₁ inner-cls

  static-gradual-ana-cls Γ⊑ (⊑ι₂ C'⊑) τ_p⊑ (aι₂ eq Cls')
    with ⊔-+-⊑ τ_p⊑ eq
  ... | τ_a₁ , τ_b₁ , eq_₁ , pa , pb
    with static-gradual-ana-cls Γ⊑ C'⊑ pb Cls'
  ... | _ , _ , _ , Γ_f⊑ , m⊑ , inner-cls
      = _ , _ , _ , Γ_f⊑ , m⊑ , aι₂ eq_₁ inner-cls

  static-gradual-ana-cls Γ⊑ (⊑&₁ C'⊑ e⊑) τ_p⊑ (a&₁ eq Cls' d₂)
    with ⊔-×-⊑ τ_p⊑ eq
  ... | τ_a₁ , τ_b₁ , eq_₁ , pa , pb
    with static-gradual-ana-cls Γ⊑ C'⊑ pa Cls'
  ... | _ , _ , _ , Γ_f⊑ , m⊑ , inner-cls
      = _ , _ , _ , Γ_f⊑ , m⊑
          , a&₁ eq_₁ inner-cls (static-gradual-ana Γ⊑ e⊑ pb d₂)

  static-gradual-ana-cls Γ⊑ (⊑&₂ e⊑ C'⊑) τ_p⊑ (a&₂ eq d₁ Cls')
    with ⊔-×-⊑ τ_p⊑ eq
  ... | τ_a₁ , τ_b₁ , eq_₁ , pa , pb
    with static-gradual-ana-cls Γ⊑ C'⊑ pb Cls'
  ... | _ , _ , _ , Γ_f⊑ , m⊑ , inner-cls
      = _ , _ , _ , Γ_f⊑ , m⊑
          , a&₂ eq_₁ (static-gradual-ana Γ⊑ e⊑ pa d₁) inner-cls

  static-gradual-ana-cls Γ⊑ (⊑case₀ C'⊑ e₁⊑ e₂⊑) τ_p⊑ (acase₀ Cls' eq d₁ d₂)
    with static-gradual-syn-cls Γ⊑ C'⊑ Cls'
  ... | τ₀_₁ , _ , _ , _ , τ₀⊑ , Γ_f⊑ , m⊑ , inner-cls
    with ⊔-+-⊑ τ₀⊑ eq
  ... | τ₁_₁ , τ₂_₁ , eq_₁ , p₁ , p₂
      = _ , _ , _ , Γ_f⊑ , m⊑
          , acase₀ inner-cls eq_₁
              (static-gradual-ana (⊑∷ p₁ Γ⊑) e₁⊑ τ_p⊑ d₁)
              (static-gradual-ana (⊑∷ p₂ Γ⊑) e₂⊑ τ_p⊑ d₂)

  static-gradual-ana-cls Γ⊑ (⊑case₁ e⊑ C'⊑ e'⊑) τ_p⊑ (acase₁ D eq Cls' d₂)
    with static-gradual-syn Γ⊑ e⊑ D
  ... | τ₀_₁ , D_₁ , τ₀⊑
    with ⊔-+-⊑ τ₀⊑ eq
  ... | τ₁_₁ , τ₂_₁ , eq_₁ , p₁ , p₂
    with static-gradual-ana-cls (⊑∷ p₁ Γ⊑) C'⊑ τ_p⊑ Cls'
  ... | _ , _ , _ , Γ_f⊑ , m⊑ , inner-cls
      = _ , _ , _ , Γ_f⊑ , m⊑
          , acase₁ D_₁ eq_₁ inner-cls (static-gradual-ana (⊑∷ p₂ Γ⊑) e'⊑ τ_p⊑ d₂)

  static-gradual-ana-cls Γ⊑ (⊑case₂ e⊑ e'⊑ C'⊑) τ_p⊑ (acase₂ D eq d₁ Cls')
    with static-gradual-syn Γ⊑ e⊑ D
  ... | τ₀_₁ , D_₁ , τ₀⊑
    with ⊔-+-⊑ τ₀⊑ eq
  ... | τ₁_₁ , τ₂_₁ , eq_₁ , p₁ , p₂
    with static-gradual-ana-cls (⊑∷ p₂ Γ⊑) C'⊑ τ_p⊑ Cls'
  ... | _ , _ , _ , Γ_f⊑ , m⊑ , inner-cls
      = _ , _ , _ , Γ_f⊑ , m⊑
          , acase₂ D_₁ eq_₁ (static-gradual-ana (⊑∷ p₁ Γ⊑) e'⊑ τ_p⊑ d₁) inner-cls

  static-gradual-ana-cls Γ⊑ (⊑def₁ C'⊑ e⊑) τ_p⊑ (adef₁ Cls'_syn d₂)
    with static-gradual-syn-cls Γ⊑ C'⊑ Cls'_syn
  ... | τ'_₁ , _ , _ , _ , τ'⊑ , Γ_f⊑ , m⊑ , inner-cls
      = _ , _ , _ , Γ_f⊑ , m⊑
          , adef₁ inner-cls (static-gradual-ana (⊑∷ τ'⊑ Γ⊑) e⊑ τ_p⊑ d₂)

  static-gradual-ana-cls Γ⊑ (⊑def₂ e⊑ C'⊑) τ_p⊑ (adef₂ D Cls')
    with static-gradual-syn Γ⊑ e⊑ D
  ... | τ'_₁ , D_₁ , τ'⊑
    with static-gradual-ana-cls (⊑∷ τ'⊑ Γ⊑) C'⊑ τ_p⊑ Cls'
  ... | _ , _ , _ , Γ_f⊑ , m⊑ , inner-cls
      = _ , _ , _ , Γ_f⊑ , m⊑ , adef₂ D_₁ inner-cls

-- Dissertation: Theorem 4.17 thm:unicity (Synthesis Unicity), §4.5.
-- Synthesis unicity: synthesis types are unique
syn-unicity : ∀ {n Γ e τ₁ τ₂} → n , Γ ⊢ e ⇑ τ₁ → n , Γ ⊢ e ⇑ τ₂ → τ₁ ≡ τ₂
syn-unicity ⇑* ⇑* = refl
syn-unicity ⇑□ ⇑□ = refl
syn-unicity (⇑Var p) (⇑Var q) with refl ← trans (sym p) q = refl
syn-unicity (⇑λ: _ D₁) (⇑λ: _ D₂) rewrite syn-unicity D₁ D₂ = refl
syn-unicity (⇑def D₁ D₂) (⇑def D₁' D₂') rewrite syn-unicity D₁ D₁' = syn-unicity D₂ D₂'
syn-unicity (⇑Λ D₁) (⇑Λ D₂) rewrite syn-unicity D₁ D₂ = refl
syn-unicity (⇑∘ D₁ m₁ _) (⇑∘ D₂ m₂ _)
  rewrite syn-unicity D₁ D₂ with refl ← trans (sym m₁) m₂ = refl
syn-unicity (⇑<> D₁ m₁ _) (⇑<> D₂ m₂ _)
  rewrite syn-unicity D₁ D₂ with refl ← trans (sym m₁) m₂ = refl
syn-unicity (⇑& D₁ D₂) (⇑& D₁' D₂') rewrite syn-unicity D₁ D₁' | syn-unicity D₂ D₂' = refl
syn-unicity (⇑π₁ D₁ m₁) (⇑π₁ D₂ m₂)
  rewrite syn-unicity D₁ D₂ with refl ← trans (sym m₁) m₂ = refl
syn-unicity (⇑π₂ D₁ m₁) (⇑π₂ D₂ m₂)
  rewrite syn-unicity D₁ D₂ with refl ← trans (sym m₁) m₂ = refl
syn-unicity (⇑case D₁ m₁ D₁a D₁b _) (⇑case D₂ m₂ D₂a D₂b _)
  rewrite syn-unicity D₁ D₂ with refl ← trans (sym m₁) m₂
  rewrite syn-unicity D₁a D₂a | syn-unicity D₁b D₂b = refl
syn-unicity (⇑ι₁ D₁) (⇑ι₁ D₂) rewrite syn-unicity D₁ D₂ = refl
syn-unicity (⇑ι₂ D₁) (⇑ι₂ D₂) rewrite syn-unicity D₁ D₂ = refl

-- Classification unicity: synthesis classification types are unique.
-- For a fixed (Γ, C, m), any two synPos derivations produce the same τ_p.
-- Mode is required to be the same because s○'s rule couples its type
-- output to its mode (`Γ ⊢ ○ at synPos τ [⇒mode τ]` — same τ in both),
-- so two s○ derivations at different modes produce different types.
syn-cls-unicity : ∀ {n Γ C τ_p₁ τ_p₂ n_f₁ n_f₂ Γ_f₁ Γ_f₂ m}
                → n , Γ ⊢ C at synPos τ_p₁ ▷ n_f₁ , Γ_f₁ [ m ]
                → n , Γ ⊢ C at synPos τ_p₂ ▷ n_f₂ , Γ_f₂ [ m ]
                → τ_p₁ ≡ τ_p₂
syn-cls-unicity s○ s○ = refl
syn-cls-unicity (sλ: _ cls₁) (sλ: _ cls₂)
  rewrite syn-cls-unicity cls₁ cls₂ = refl
syn-cls-unicity (s∘₁ cls₁ eq₁ _) (s∘₁ cls₂ eq₂ _)
  rewrite syn-cls-unicity cls₁ cls₂ with refl ← trans (sym eq₁) eq₂ = refl
syn-cls-unicity (s∘₂ D₁ eq₁ cls₁) (s∘₂ D₂ eq₂ cls₂)
  rewrite syn-unicity D₁ D₂ with refl ← trans (sym eq₁) eq₂ = refl
syn-cls-unicity (s<>₁ cls₁ eq₁ _) (s<>₁ cls₂ eq₂ _)
  rewrite syn-cls-unicity cls₁ cls₂ with refl ← trans (sym eq₁) eq₂ = refl
syn-cls-unicity (s&₁ cls₁ d₁) (s&₁ cls₂ d₂)
  rewrite syn-cls-unicity cls₁ cls₂ | syn-unicity d₁ d₂ = refl
syn-cls-unicity (s&₂ d₁ cls₁) (s&₂ d₂ cls₂)
  rewrite syn-unicity d₁ d₂ | syn-cls-unicity cls₁ cls₂ = refl
syn-cls-unicity (sι₁ cls₁) (sι₁ cls₂)
  rewrite syn-cls-unicity cls₁ cls₂ = refl
syn-cls-unicity (sι₂ cls₁) (sι₂ cls₂)
  rewrite syn-cls-unicity cls₁ cls₂ = refl
syn-cls-unicity (scase₀ cls₁ eq₁ d₁₁ d₂₁ _) (scase₀ cls₂ eq₂ d₁₂ d₂₂ _)
  with refl ← syn-cls-unicity cls₁ cls₂
  with refl ← trans (sym eq₁) eq₂
  rewrite syn-unicity d₁₁ d₁₂ | syn-unicity d₂₁ d₂₂ = refl
syn-cls-unicity (scase₁ D₁ eq₁ cls₁ d₂_₁ _) (scase₁ D₂ eq₂ cls₂ d₂_₂ _)
  rewrite syn-unicity D₁ D₂
  with refl ← trans (sym eq₁) eq₂
  with refl ← syn-cls-unicity cls₁ cls₂
  with refl ← syn-unicity d₂_₁ d₂_₂
  = refl
syn-cls-unicity (scase₂ D₁ eq₁ d₁_₁ cls₁ _) (scase₂ D₂ eq₂ d₁_₂ cls₂ _)
  rewrite syn-unicity D₁ D₂
  with refl ← trans (sym eq₁) eq₂
  with refl ← syn-unicity d₁_₁ d₁_₂
  with refl ← syn-cls-unicity cls₁ cls₂
  = refl
syn-cls-unicity (sπ₁ cls₁ eq₁) (sπ₁ cls₂ eq₂)
  rewrite syn-cls-unicity cls₁ cls₂ with refl ← trans (sym eq₁) eq₂ = refl
syn-cls-unicity (sπ₂ cls₁ eq₁) (sπ₂ cls₂ eq₂)
  rewrite syn-cls-unicity cls₁ cls₂ with refl ← trans (sym eq₁) eq₂ = refl
syn-cls-unicity (sΛ cls₁) (sΛ cls₂)
  rewrite syn-cls-unicity cls₁ cls₂ = refl
syn-cls-unicity (sdef₁ cls₁ d₁) (sdef₁ cls₂ d₂)
  rewrite syn-cls-unicity cls₁ cls₂ | syn-unicity d₁ d₂ = refl
syn-cls-unicity (sdef₂ d₁ cls₁) (sdef₂ d₂ cls₂)
  rewrite syn-unicity d₁ d₂ | syn-cls-unicity cls₁ cls₂ = refl

-- Dissertation: Corollary 4.18 cor:precision (Synthesis Precision), §4.5.
-- Hence, if less precise exp synthesises, its type is less precise
syn-precision : ∀ {n Γ₁ Γ₂ e₁ e₂ τ₁ τ₂}
                →  Γ₁ ⊑ Γ₂ → e₁ ⊑ e₂
                →  n , Γ₂ ⊢ e₂ ⇑ τ₂
                →  n , Γ₁ ⊢ e₁ ⇑ τ₁
                →  τ₁ ⊑ τ₂
syn-precision Γ⊑ e⊑ D₂ D₁
  with static-gradual-syn Γ⊑ e⊑ D₂
...  | τ₁' , D₁' , τ⊑ rewrite syn-unicity D₁ D₁' = τ⊑
