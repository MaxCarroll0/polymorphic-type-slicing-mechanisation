open import Data.Nat hiding (_+_; _⊔_; _≟_)
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Data.Product using (_,_; ∃-syntax) renaming (_×_ to _∧_)
open import Core
open import Core.Assms.Lift using (hdₛ; tlₛ; cons-decompₛ)
open import Semantics.Statics
open import Semantics.Graduality using (static-gradual-ana-cls; static-gradual-syn-cls; ⇐mode-⊑; mode-⊑)
open import Slicing.Analysis.Analysis
open import Slicing.Analysis.AnaSliceCalc

-- Context-weakening lifts from static-gradual-{ana,syn}-cls (Dissertation §8.6).
module Slicing.Analysis.Alignment where

weaken-ana-cls : ∀ {n Γ₁ Γ₂ C n_f Γ_f τ_p τ_m}
    → Γ₁ ⊑ Γ₂
    → n , Γ₂ ⊢ C at anaPos τ_p ▷ n_f , Γ_f [ ⇐mode τ_m ]
    → ∃[ τ_m' ] (τ_m' ⊑t τ_m) ∧ ∃[ n_f' ] ∃[ Γ_f' ]
        (n , Γ₁ ⊢ C at anaPos τ_p ▷ n_f' , Γ_f' [ ⇐mode τ_m' ])
weaken-ana-cls Γ⊑ cls
  with static-gradual-ana-cls Γ⊑ (⊑.refl {A = Ctx}) (⊑.refl {A = Typ}) cls
... | _ , _ , .(⇐mode _) , _ , ⇐mode-⊑ τ_m'⊑ , derived =
      _ , τ_m'⊑ , _ , _ , derived

weaken-syn-cls : ∀ {n Γ₁ Γ₂ C n_f Γ_f τ_p τ_m}
    → Γ₁ ⊑ Γ₂
    → n , Γ₂ ⊢ C at synPos τ_p ▷ n_f , Γ_f [ ⇐mode τ_m ]
    → ∃[ τ_p' ] (τ_p' ⊑t τ_p) ∧ ∃[ τ_m' ] (τ_m' ⊑t τ_m) ∧ ∃[ n_f' ] ∃[ Γ_f' ]
        (n , Γ₁ ⊢ C at synPos τ_p' ▷ n_f' , Γ_f' [ ⇐mode τ_m' ])
weaken-syn-cls Γ⊑ cls
  with static-gradual-syn-cls Γ⊑ (⊑.refl {A = Ctx}) cls
... | _ , _ , _ , .(⇐mode _) , τ_p'⊑ , _ , ⇐mode-⊑ τ_m'⊑ , derived =
      _ , τ_p'⊑ , _ , τ_m'⊑ , _ , _ , derived

acase₁-Cls-lifted : ∀ {n n_f Γ Γ' C τ₁ τ τ'}
                      {Cls' : n , (τ₁ ∷ Γ) ⊢ C at anaPos τ ▷ n_f , Γ' [ ⇐mode τ' ]}
                      {υ : ⌊ τ' ⌋}
                    → (m : MinAnaPos Cls' υ)
                    → ∃[ τ_m' ] (τ_m' ⊑t (ana-focus (extract-pos m)).↓) ∧
                      ∃[ n-f' ] ∃[ Γ-f' ]
                        (n , (□ ∷ (tlₛ (ana-γ (extract-pos m))) .↓) ⊢ (ana-κ (extract-pos m)) .↓
                           at anaPos ((ana-υ_outer (extract-pos m)) .↓) ▷ n-f' , Γ-f'
                           [ ⇐mode τ_m' ])
acase₁-Cls-lifted {n = n} m =
  let inner = extract-pos m
      n_f , Γ_f , inner-cls = ana-valid inner
      inner-cls-decomp =
        subst (λ x → n , x ⊢ (ana-κ inner .↓) at anaPos (ana-υ_outer inner .↓)
                        ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ])
              (cons-decompₛ (ana-γ inner)) inner-cls
      Γ⊑ : (□ ∷ (tlₛ (ana-γ inner)) .↓) ⊑ (hdₛ (ana-γ inner) .↓ ∷ (tlₛ (ana-γ inner)) .↓)
      Γ⊑ = ⊑∷ ⊑□ (⊑.refl {Assms})
  in weaken-ana-cls Γ⊑ inner-cls-decomp

acase₂-Cls-lifted : ∀ {n n_f Γ Γ' C τ₂ τ τ'}
                      {Cls' : n , (τ₂ ∷ Γ) ⊢ C at anaPos τ ▷ n_f , Γ' [ ⇐mode τ' ]}
                      {υ : ⌊ τ' ⌋}
                    → (m : MinAnaPos Cls' υ)
                    → ∃[ τ_m' ] (τ_m' ⊑t (ana-focus (extract-pos m)).↓) ∧
                      ∃[ n-f' ] ∃[ Γ-f' ]
                        (n , (□ ∷ (tlₛ (ana-γ (extract-pos m))) .↓) ⊢ (ana-κ (extract-pos m)) .↓
                           at anaPos ((ana-υ_outer (extract-pos m)) .↓) ▷ n-f' , Γ-f'
                           [ ⇐mode τ_m' ])
acase₂-Cls-lifted {n = n} m =
  let inner = extract-pos m
      n_f , Γ_f , inner-cls = ana-valid inner
      inner-cls-decomp =
        subst (λ x → n , x ⊢ (ana-κ inner .↓) at anaPos (ana-υ_outer inner .↓)
                        ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ])
              (cons-decompₛ (ana-γ inner)) inner-cls
      Γ⊑ : (□ ∷ (tlₛ (ana-γ inner)) .↓) ⊑ (hdₛ (ana-γ inner) .↓ ∷ (tlₛ (ana-γ inner)) .↓)
      Γ⊑ = ⊑∷ ⊑□ (⊑.refl {Assms})
  in weaken-ana-cls Γ⊑ inner-cls-decomp

scase₁-Cls-lifted : ∀ {n n_f Γ Γ' C τ₁ τ₁' τ}
                      {Cls' : n , (τ₁ ∷ Γ) ⊢ C at synPos τ₁' ▷ n_f , Γ' [ ⇐mode τ ]}
                      {υ : ⌊ τ ⌋}
                    → (m : MinAna Cls' υ)
                    → ∃[ τ_p' ] (τ_p' ⊑t (extract m .type) .↓) ∧
                      ∃[ τ_m' ] (τ_m' ⊑t (extract m .focus) .↓) ∧
                      ∃[ n-f' ] ∃[ Γ-f' ]
                        (n , (□ ∷ (tlₛ (extract m .γ)) .↓) ⊢ (extract m .κ) .↓
                           at synPos τ_p' ▷ n-f' , Γ-f'
                           [ ⇐mode τ_m' ])
scase₁-Cls-lifted {n = n} m =
  let inner = extract m
      n_f , Γ_f , inner-cls = inner .valid
      inner-cls-decomp =
        subst (λ x → n , x ⊢ (inner .κ .↓) at synPos (inner .type .↓)
                        ▷ n_f , Γ_f [ ⇐mode (inner .focus .↓) ])
              (cons-decompₛ (inner .γ)) inner-cls
      Γ⊑ : (□ ∷ (tlₛ (inner .γ)) .↓) ⊑ (hdₛ (inner .γ) .↓ ∷ (tlₛ (inner .γ)) .↓)
      Γ⊑ = ⊑∷ ⊑□ (⊑.refl {Assms})
  in weaken-syn-cls Γ⊑ inner-cls-decomp

scase₂-Cls-lifted : ∀ {n n_f Γ Γ' C τ₂ τ₂' τ}
                      {Cls' : n , (τ₂ ∷ Γ) ⊢ C at synPos τ₂' ▷ n_f , Γ' [ ⇐mode τ ]}
                      {υ : ⌊ τ ⌋}
                    → (m : MinAna Cls' υ)
                    → ∃[ τ_p' ] (τ_p' ⊑t (extract m .type) .↓) ∧
                      ∃[ τ_m' ] (τ_m' ⊑t (extract m .focus) .↓) ∧
                      ∃[ n-f' ] ∃[ Γ-f' ]
                        (n , (□ ∷ (tlₛ (extract m .γ)) .↓) ⊢ (extract m .κ) .↓
                           at synPos τ_p' ▷ n-f' , Γ-f'
                           [ ⇐mode τ_m' ])
scase₂-Cls-lifted {n = n} m =
  let inner = extract m
      n_f , Γ_f , inner-cls = inner .valid
      inner-cls-decomp =
        subst (λ x → n , x ⊢ (inner .κ .↓) at synPos (inner .type .↓)
                        ▷ n_f , Γ_f [ ⇐mode (inner .focus .↓) ])
              (cons-decompₛ (inner .γ)) inner-cls
      Γ⊑ : (□ ∷ (tlₛ (inner .γ)) .↓) ⊑ (hdₛ (inner .γ) .↓ ∷ (tlₛ (inner .γ)) .↓)
      Γ⊑ = ⊑∷ ⊑□ (⊑.refl {Assms})
  in weaken-syn-cls Γ⊑ inner-cls-decomp

sdef₂-Cls-lifted : ∀ {n n_f Γ Γ' C τ' τ_body τ}
                     {Cls' : n , (τ' ∷ Γ) ⊢ C at synPos τ_body ▷ n_f , Γ' [ ⇐mode τ ]}
                     {υ : ⌊ τ ⌋}
                   → (m : MinAna Cls' υ)
                   → ∃[ τ_p' ] (τ_p' ⊑t (extract m .type) .↓) ∧
                     ∃[ τ_m' ] (τ_m' ⊑t (extract m .focus) .↓) ∧
                     ∃[ n-f' ] ∃[ Γ-f' ]
                       (n , (□ ∷ (tlₛ (extract m .γ)) .↓) ⊢ (extract m .κ) .↓
                          at synPos τ_p' ▷ n-f' , Γ-f'
                          [ ⇐mode τ_m' ])
sdef₂-Cls-lifted {n = n} m =
  let inner = extract m
      n_f , Γ_f , inner-cls = inner .valid
      inner-cls-decomp =
        subst (λ x → n , x ⊢ (inner .κ .↓) at synPos (inner .type .↓)
                        ▷ n_f , Γ_f [ ⇐mode (inner .focus .↓) ])
              (cons-decompₛ (inner .γ)) inner-cls
      Γ⊑ : (□ ∷ (tlₛ (inner .γ)) .↓) ⊑ (hdₛ (inner .γ) .↓ ∷ (tlₛ (inner .γ)) .↓)
      Γ⊑ = ⊑∷ ⊑□ (⊑.refl {Assms})
  in weaken-syn-cls Γ⊑ inner-cls-decomp

adef₂-Cls-lifted : ∀ {n n_f Γ Γ' C τ' τ_body τ}
                     {Cls' : n , (τ' ∷ Γ) ⊢ C at anaPos τ_body ▷ n_f , Γ' [ ⇐mode τ ]}
                     {υ : ⌊ τ ⌋}
                   → (m : MinAnaPos Cls' υ)
                   → ∃[ τ_m' ] (τ_m' ⊑t (ana-focus (extract-pos m)).↓) ∧
                     ∃[ n-f' ] ∃[ Γ-f' ]
                       (n , (□ ∷ (tlₛ (ana-γ (extract-pos m))) .↓) ⊢ (ana-κ (extract-pos m)) .↓
                          at anaPos ((ana-υ_outer (extract-pos m)) .↓) ▷ n-f' , Γ-f'
                          [ ⇐mode τ_m' ])
adef₂-Cls-lifted {n = n} m =
  let inner = extract-pos m
      n_f , Γ_f , inner-cls = ana-valid inner
      inner-cls-decomp =
        subst (λ x → n , x ⊢ (ana-κ inner .↓) at anaPos (ana-υ_outer inner .↓)
                        ▷ n_f , Γ_f [ ⇐mode (ana-focus inner .↓) ])
              (cons-decompₛ (ana-γ inner)) inner-cls
      Γ⊑ : (□ ∷ (tlₛ (ana-γ inner)) .↓) ⊑ (hdₛ (ana-γ inner) .↓ ∷ (tlₛ (ana-γ inner)) .↓)
      Γ⊑ = ⊑∷ ⊑□ (⊑.refl {Assms})
  in weaken-ana-cls Γ⊑ inner-cls-decomp
