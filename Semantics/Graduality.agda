module Semantics.Graduality where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.List using ([]; _∷_)
open import Data.Product using (∃; Σ; _,_; Σ-syntax)
open import Data.Product using () renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂; trans; cong)
open import Core
open import Semantics.Statics.Typing



-- Static gradual guarantee
mutual
  static-gradual-syn : ∀ {n Γ₁ Γ₂ e₁ e₂ τ₂} →
    Γ₁ ⊑ Γ₂ → e₁ ⊑ e₂ →
    n ； Γ₂ ⊢ e₂ ↦ τ₂ →
    Σ[ τ₁ ∈ Typ ] n ； Γ₁ ⊢ e₁ ↦ τ₁ ∧ τ₁ ⊑ τ₂

  static-gradual-syn Γ⊑ ⊑□ _ = □ , ↦□ , ⊑□
  static-gradual-syn Γ⊑ ⊑* ↦* = * , ↦* , ⊑*
  static-gradual-syn Γ⊑ ⊑Var (↦Var p)
    with lookup-⊑ Γ⊑ p
  ...  | τ₁ , p₁ , τ⊑ = τ₁ , ↦Var p₁ , τ⊑
  static-gradual-syn Γ⊑ (⊑λ τ⊑ e⊑) (↦λ: wf₂ D₂)
    with static-gradual-syn (⊑∷ τ⊑ Γ⊑) e⊑ D₂
  ...  | τ₁b , D₁ , τb⊑ = _ ⇒ τ₁b , ↦λ: (wf-⊑ wf₂ τ⊑) D₁ , ⊑⇒ τ⊑ τb⊑
  static-gradual-syn Γ⊑ (⊑& p q) (↦& D₁ D₂)
    with static-gradual-syn Γ⊑ p D₁ | static-gradual-syn Γ⊑ q D₂
  ...  | τ₁ , D₁' , p₁ | τ₂ , D₂' , p₂ = (τ₁ × τ₂) , ↦& D₁' D₂' , ⊑× p₁ p₂
  static-gradual-syn Γ⊑ (⊑Λ e⊑) (↦Λ D₂)
    with static-gradual-syn (shiftΓ-⊑ Γ⊑) e⊑ D₂
  ...  | τ₁ , D₁ , τ⊑ = ∀· τ₁ , ↦Λ D₁ , ⊑∀ τ⊑
  static-gradual-syn Γ⊑ (⊑def p q) (↦def D₁ D₂)
    with static-gradual-syn Γ⊑ p D₁
  ...  | τ₁' , D₁'  , p₁ with static-gradual-syn (⊑∷ p₁ Γ⊑) q D₂
  ...                       | τ₁  , D₁'' , q₁ = τ₁ , ↦def D₁' D₁'' , q₁
  static-gradual-syn Γ⊑ (⊑∘ p q) (↦∘ D₂ m Da₂)
    with static-gradual-syn Γ⊑ p D₂
  ...  | τ₁ , D₁ , τ⊑ with ⊔-⇒-⊑ τ⊑ m
  ...                   | τ₁a , τ₁b , m₁ , pa , pb
                        with static-gradual-ana Γ⊑ q pa Da₂
  ...                      | Da₁ = τ₁b , ↦∘ D₁ m₁ Da₁ , pb
  static-gradual-syn Γ⊑ (⊑<> e⊑ σ⊑) (↦<> D₂ m wf₂)
    with static-gradual-syn Γ⊑ e⊑ D₂
  ...  | τ₁ , D₁ , τ⊑ with ⊔-∀-⊑ τ⊑ m
  ...                    | τ₁' , m₁ , p
                         = _ , ↦<> D₁ m₁ (wf-⊑ wf₂ σ⊑) , sub-⊑ zero σ⊑ p
  static-gradual-syn Γ⊑ (⊑π₁ e⊑) (↦π₁ D₂ m)
    with static-gradual-syn Γ⊑ e⊑ D₂
  ...  | τ₁ , D₁ , τ⊑ with ⊔-×-⊑ τ⊑ m
  ...                    | τ₁a , τ₁b , m₁ , pa , pb
                         = τ₁a , ↦π₁ D₁ m₁ , pa

  static-gradual-syn Γ⊑ (⊑π₂ e⊑) (↦π₂ D₂ m)
    with static-gradual-syn Γ⊑ e⊑ D₂
  ... | τ₁ , D₁ , τ⊑ with ⊔-×-⊑ τ⊑ m
  ...                   | τ₁a , τ₁b , m₁ , pa , pb
                        = τ₁b , ↦π₂ D₁ m₁ , pb

  static-gradual-syn Γ⊑ (⊑case e⊑ e₁⊑ e₂⊑) (↦case D₂ m D₂₁ D₂₂ c)
    with static-gradual-syn Γ⊑ e⊑ D₂
  ...  | τs , Ds , τs⊑
    with ⊔-+-⊑ τs⊑ m
  ...  | τa , τb , m₁ , pa , pb
    with static-gradual-syn (⊑∷ pa Γ⊑) e₁⊑ D₂₁ | static-gradual-syn (⊑∷ pb Γ⊑) e₂⊑ D₂₂
  ...  | τl , Dl , pl                          | τr , Dr , pr
       = τl ⊔ τr , ↦case Ds m₁ Dl Dr (~-⊑-down c pl pr) , ⊔-mono-⊑ c pl pr

  -- Analysis gradual guarantee
  static-gradual-ana : ∀ {n Γ₁ Γ₂ e₁ e₂ τ₁ τ₂} →
    Γ₁ ⊑ Γ₂ → e₁ ⊑ e₂ → τ₁ ⊑ τ₂ →
    n ； Γ₂ ⊢ e₂ ↤ τ₂ →
    n ； Γ₁ ⊢ e₁ ↤ τ₁

  static-gradual-ana Γ⊑ ⊑□ τ⊑ _ = ↤Sub ↦□ ~?₁
  -- Subsumption
  static-gradual-ana Γ⊑ e⊑ τ⊑ (↤Sub D₂ c)
    with static-gradual-syn Γ⊑ e⊑ D₂
  ...  | τ₁' , D₁ , τ'⊑ = ↤Sub D₁ (~-⊑-down c τ⊑ τ'⊑)
  static-gradual-ana Γ⊑ (⊑λu e⊑) τ⊑ (↤λ m Da₂)
    with ⊔-⇒-⊑ τ⊑ m
  ...  | τ₁a , τ₁b , m₁ , pa , pb
       = ↤λ m₁ (static-gradual-ana (⊑∷ pa Γ⊑) e⊑ pb Da₂)
  static-gradual-ana Γ⊑ (⊑λ τa⊑ e⊑) τ⊑ (↤λ: c₂ m₂ wf₂ Da₂)
    with ⊔-ann-⇒-⊑ τ⊑ τa⊑ m₂
  ...  | _ , _ , m₁ , pb
       = ↤λ: (~-⊑-down c₂ τ⊑ (⊑⇒ τa⊑ ⊑□)) m₁ (wf-⊑ wf₂ τa⊑)
                (static-gradual-ana (⊑∷ τa⊑ Γ⊑) e⊑ pb Da₂)
  static-gradual-ana Γ⊑ (⊑ι₁ e⊑) τ⊑ (↤ι₁ m Da₂)
    with ⊔-+-⊑ τ⊑ m
  ...  | τ₁a , τ₁b , m₁ , pa , pb
       = ↤ι₁ m₁ (static-gradual-ana Γ⊑ e⊑ pa Da₂)
  static-gradual-ana Γ⊑ (⊑ι₂ e⊑) τ⊑ (↤ι₂ m Da₂)
    with ⊔-+-⊑ τ⊑ m
  ...  | τ₁a , τ₁b , m₁ , pa , pb
       = ↤ι₂ m₁ (static-gradual-ana Γ⊑ e⊑ pb Da₂)
  static-gradual-ana Γ⊑ (⊑& e₁⊑ e₂⊑) τ⊑ (↤& m Da₁ Da₂)
    with ⊔-×-⊑ τ⊑ m
  ...  | τ₁a , τ₁b , m₁ , pa , pb
       = ↤& m₁ (static-gradual-ana Γ⊑ e₁⊑ pa Da₁)
               (static-gradual-ana Γ⊑ e₂⊑ pb Da₂)
  static-gradual-ana Γ⊑ (⊑case e⊑ e₁⊑ e₂⊑) τ⊑ (↤case Ds₂ m Da₁ Da₂)
    with static-gradual-syn Γ⊑ e⊑ Ds₂
  ...  | τs , Ds , τs⊑ with ⊔-+-⊑ τs⊑ m
  ...  | τa , τb , m₁ , pa , pb
       = ↤case Ds m₁ (static-gradual-ana (⊑∷ pa Γ⊑) e₁⊑ τ⊑ Da₁)
                     (static-gradual-ana (⊑∷ pb Γ⊑) e₂⊑ τ⊑ Da₂)
  static-gradual-ana Γ⊑ (⊑def e₁⊑ e₂⊑) τ⊑ (↤def Ds₂ Da₂)
    with static-gradual-syn Γ⊑ e₁⊑ Ds₂
  ...  | τ₁' , Ds₁ , p₁
       = ↤def Ds₁ (static-gradual-ana (⊑∷ p₁ Γ⊑) e₂⊑ τ⊑ Da₂)

-- Synthesis unicity: synthesis types are unique
syn-unicity : ∀ {n Γ e τ₁ τ₂} → n ； Γ ⊢ e ↦ τ₁ → n ； Γ ⊢ e ↦ τ₂ → τ₁ ≡ τ₂
syn-unicity ↦* ↦* = refl
syn-unicity ↦□ ↦□ = refl
syn-unicity (↦Var p) (↦Var q) with refl ← trans (sym p) q = refl
syn-unicity (↦λ: _ D₁) (↦λ: _ D₂) rewrite syn-unicity D₁ D₂ = refl
syn-unicity (↦def D₁ D₂) (↦def D₁' D₂') rewrite syn-unicity D₁ D₁' = syn-unicity D₂ D₂'
syn-unicity (↦Λ D₁) (↦Λ D₂) rewrite syn-unicity D₁ D₂ = refl
syn-unicity (↦∘ D₁ m₁ _) (↦∘ D₂ m₂ _)
  rewrite syn-unicity D₁ D₂ with refl ← trans (sym m₁) m₂ = refl
syn-unicity (↦<> D₁ m₁ _) (↦<> D₂ m₂ _)
  rewrite syn-unicity D₁ D₂ with refl ← trans (sym m₁) m₂ = refl
syn-unicity (↦& D₁ D₂) (↦& D₁' D₂') rewrite syn-unicity D₁ D₁' | syn-unicity D₂ D₂' = refl
syn-unicity (↦π₁ D₁ m₁) (↦π₁ D₂ m₂)
  rewrite syn-unicity D₁ D₂ with refl ← trans (sym m₁) m₂ = refl
syn-unicity (↦π₂ D₁ m₁) (↦π₂ D₂ m₂)
  rewrite syn-unicity D₁ D₂ with refl ← trans (sym m₁) m₂ = refl
syn-unicity (↦case D₁ m₁ D₁a D₁b _) (↦case D₂ m₂ D₂a D₂b _)
  rewrite syn-unicity D₁ D₂ with refl ← trans (sym m₁) m₂
  rewrite syn-unicity D₁a D₂a | syn-unicity D₁b D₂b = refl

-- Hence, if less precise exp synthesises, its type is less precise
syn-precision : ∀ {n Γ₁ Γ₂ e₁ e₂ τ₁ τ₂}
                →  Γ₁ ⊑ Γ₂ → e₁ ⊑ e₂
                →  n ； Γ₂ ⊢ e₂ ↦ τ₂
                →  n ； Γ₁ ⊢ e₁ ↦ τ₁
                →  τ₁ ⊑ τ₂
syn-precision Γ⊑ e⊑ D₂ D₁
  with static-gradual-syn Γ⊑ e⊑ D₂
...  | τ₁' , D₁' , τ⊑ rewrite syn-unicity D₁ D₁' = τ⊑
