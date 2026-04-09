module Core.Exp.Lattice where

open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary using (IsPartialOrder)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Antisymmetric; Maximum; Minimum)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Relation.Binary.Lattice.Structures using (IsMeetSemilattice; IsJoinSemilattice; IsLattice; IsBoundedLattice; IsDistributiveLattice)
open import Relation.Binary.Lattice.Definitions using (Infimum; Supremum)
open import Relation.Nullary using (yes; no)
open import Function using (_on_)

open import Core.Typ using (Typ)
  renaming (_⊑_ to _⊑t_; _⊓_ to _⊓t_; _⊔_ to _⊔t_;
            ⊑-consistent to ⊑t-consistent;
            module ~ to ~t; module ⊑ to ⊑t;
            module ⊑Lat to ⊑tLat; module ⊑ₛLat to ⊑tₛLat;
            ↑ to ↑t)
open import Core.Exp.Base
open import Core.Exp.Equality renaming (_≟_ to _≟e_)
open import Core.Exp.Precision renaming (⊤ₛ to ⊤ₛ')

_⊓_ : Exp → Exp → Exp
e ⊓ e' with diag e e'
...       | diff                                    = □
...       | kind□                                   = □
...       | kind*                                   = *
...       | kindλ  {τ} {τ'} {e₁} {e₁'}              = λ: (τ ⊓t τ') ⇒ (e₁ ⊓ e₁')
...       | kindλu {e₁} {e₁'}                       = λ⇒ (e₁ ⊓ e₁')
...       | kind∘  {e₁} {e₂} {e₁'} {e₂'}            = (e₁ ⊓ e₁') ∘ (e₂ ⊓ e₂')
...       | kind<> {e₁} {e₁'} {τ} {τ'}              = (e₁ ⊓ e₁') < (τ ⊓t τ') >
...       | kind&  {e₁} {e₂} {e₁'} {e₂'}            = (e₁ ⊓ e₁') & (e₂ ⊓ e₂')
...       | kindι₁ {e₁} {e₁'}                       = ι₁ (e₁ ⊓ e₁')
...       | kindι₂ {e₁} {e₁'}                       = ι₂ (e₁ ⊓ e₁')
...       | kindcase {e} {e'} {e₁} {e₂} {e₁'} {e₂'} = case (e ⊓ e') of (e₁ ⊓ e₁') · (e₂ ⊓ e₂')
...       | kindπ₁ {e₁} {e₁'}                       = π₁ (e₁ ⊓ e₁')
...       | kindπ₂ {e₁} {e₁'}                       = π₂ (e₁ ⊓ e₁')
...       | kindΛ  {e₁} {e₁'}                       = Λ (e₁ ⊓ e₁')
...       | kinddef {e₁} {e₂} {e₁'} {e₂'}           = def (e₁ ⊓ e₁') ⊢ (e₂ ⊓ e₂')
...       | kindVar {m} {n}            with m ≟ℕ n
...                                       | yes _   = ⟨ m ⟩
...                                       | no  _   = □

infixl 6 _⊓_

_⊔_ : Exp → Exp → Exp
e ⊔ e' with diag e e'
...       | kind□                                   = □
...       | kind*                                   = *
...       | kindVar {m}                             = ⟨ m ⟩
...       | kindλ  {τ} {τ'} {e₁} {e₁'}              = λ: (τ ⊔t τ') ⇒ (e₁ ⊔ e₁')
...       | kindλu {e₁} {e₁'}                       = λ⇒ (e₁ ⊔ e₁')
...       | kind∘  {e₁} {e₂} {e₁'} {e₂'}            = (e₁ ⊔ e₁') ∘ (e₂ ⊔ e₂')
...       | kind<> {e₁} {e₁'} {τ} {τ'}              = (e₁ ⊔ e₁') < (τ ⊔t τ') >
...       | kind&  {e₁} {e₂} {e₁'} {e₂'}            = (e₁ ⊔ e₁') & (e₂ ⊔ e₂')
...       | kindι₁ {e₁} {e₁'}                       = ι₁ (e₁ ⊔ e₁')
...       | kindι₂ {e₁} {e₁'}                       = ι₂ (e₁ ⊔ e₁')
...       | kindcase {e} {e'} {e₁} {e₂} {e₁'} {e₂'} = case (e ⊔ e') of (e₁ ⊔ e₁') · (e₂ ⊔ e₂')
...       | kindπ₁ {e₁} {e₁'}                       = π₁ (e₁ ⊔ e₁')
...       | kindπ₂ {e₁} {e₁'}                       = π₂ (e₁ ⊔ e₁')
...       | kindΛ  {e₁} {e₁'}                       = Λ (e₁ ⊔ e₁')
...       | kinddef {e₁} {e₂} {e₁'} {e₂'}           = def (e₁ ⊔ e₁') ⊢ (e₂ ⊔ e₂')
e ⊔ e'    | diff with e ≟e □
...                | yes _  = e'
...                | no  _  = e

infixl 6 _⊔_

private
  -- Meet lower bounds
  ⊓-lb₁ : ∀ e₁ e₂ → e₁ ⊓ e₂ ⊑ e₁
  ⊓-lb₁ e       e'                         with diag e e'
  ⊓-lb₁ (λ: τ ⇒ e₁)   (λ: τ' ⇒ e₁')            | kindλ    
                                                 = ⊑λ (⊑tLat.x⊓y⊑x τ τ') (⊓-lb₁ e₁ e₁')
  ⊓-lb₁ (λ⇒ e₁)       (λ⇒ e₁')                 | kindλu   = ⊑λu (⊓-lb₁ e₁ e₁')
  ⊓-lb₁ (e₁ ∘ e₂)     (e₁' ∘ e₂')              | kind∘    = ⊑∘ (⊓-lb₁ e₁ e₁') (⊓-lb₁ e₂ e₂')
  ⊓-lb₁ (e₁ < τ >)    (e₁' < τ' >)             | kind<>   
                                                 = ⊑<> (⊓-lb₁ e₁ e₁') (⊑tLat.x⊓y⊑x τ τ')
  ⊓-lb₁ (e₁ & e₂)     (e₁' & e₂')              | kind&    = ⊑& (⊓-lb₁ e₁ e₁') (⊓-lb₁ e₂ e₂')
  ⊓-lb₁ (ι₁ e₁)       (ι₁ e₁')                 | kindι₁   = ⊑ι₁ (⊓-lb₁ e₁ e₁')
  ⊓-lb₁ (ι₂ e₁)       (ι₂ e₁')                 | kindι₂   = ⊑ι₂ (⊓-lb₁ e₁ e₁')
  ⊓-lb₁ (case e of e₁ · e₂) (case e' of e₁' · e₂') | kindcase
                                                 = ⊑case (⊓-lb₁ e e') (⊓-lb₁ e₁ e₁') (⊓-lb₁ e₂ e₂')
  ⊓-lb₁ (π₁ e₁)       (π₁ e₁')                 | kindπ₁   = ⊑π₁ (⊓-lb₁ e₁ e₁')
  ⊓-lb₁ (π₂ e₁)       (π₂ e₁')                 | kindπ₂   = ⊑π₂ (⊓-lb₁ e₁ e₁')
  ⊓-lb₁ (Λ e₁)        (Λ e₁')                  | kindΛ    = ⊑Λ (⊓-lb₁ e₁ e₁')
  ⊓-lb₁ (def e₁ ⊢ e₂) (def e₁' ⊢ e₂')          | kinddef  = ⊑def (⊓-lb₁ e₁ e₁') (⊓-lb₁ e₂ e₂')
  ⊓-lb₁ *             *                        | kind*    = ⊑*
  ⊓-lb₁ □             □                        | kind□    = ⊑□
  ⊓-lb₁ ⟨ m ⟩         ⟨ n ⟩                    | kindVar  with m ≟ℕ n
  ...                                                        | yes _  = ⊑Var
  ...                                                        | no  _  = ⊑□
  ⊓-lb₁ _             _                        | diff     = ⊑□

  ⊓-lb₂ : ∀ e₁ e₂ → e₁ ⊓ e₂ ⊑ e₂
  ⊓-lb₂ e       e'                          with diag e e'
  ⊓-lb₂ (λ: τ ⇒ e₁)   (λ: τ' ⇒ e₁')            | kindλ
                                                 = ⊑λ (⊑tLat.x⊓y⊑y τ τ') (⊓-lb₂ e₁ e₁')
  ⊓-lb₂ (λ⇒ e₁)       (λ⇒ e₁')                 | kindλu   = ⊑λu (⊓-lb₂ e₁ e₁')
  ⊓-lb₂ (e₁ ∘ e₂)     (e₁' ∘ e₂')              | kind∘    = ⊑∘ (⊓-lb₂ e₁ e₁') (⊓-lb₂ e₂ e₂')
  ⊓-lb₂ (e₁ < τ >)    (e₁' < τ' >)             | kind<>   
                                                 = ⊑<> (⊓-lb₂ e₁ e₁') (⊑tLat.x⊓y⊑y τ τ')
  ⊓-lb₂ (e₁ & e₂)     (e₁' & e₂')              | kind&    = ⊑& (⊓-lb₂ e₁ e₁') (⊓-lb₂ e₂ e₂')
  ⊓-lb₂ (ι₁ e₁)       (ι₁ e₁')                 | kindι₁   = ⊑ι₁ (⊓-lb₂ e₁ e₁')
  ⊓-lb₂ (ι₂ e₁)       (ι₂ e₁')                 | kindι₂   = ⊑ι₂ (⊓-lb₂ e₁ e₁')
  ⊓-lb₂ (case e of e₁ · e₂) (case e' of e₁' · e₂') | kindcase 
                                                 = ⊑case (⊓-lb₂ e e') (⊓-lb₂ e₁ e₁') (⊓-lb₂ e₂ e₂')
  ⊓-lb₂ (π₁ e₁)       (π₁ e₁')                 | kindπ₁   = ⊑π₁ (⊓-lb₂ e₁ e₁')
  ⊓-lb₂ (π₂ e₁)       (π₂ e₁')                 | kindπ₂   = ⊑π₂ (⊓-lb₂ e₁ e₁')
  ⊓-lb₂ (Λ e₁)        (Λ e₁')                  | kindΛ    = ⊑Λ (⊓-lb₂ e₁ e₁')
  ⊓-lb₂ (def e₁ ⊢ e₂) (def e₁' ⊢ e₂')          | kinddef  = ⊑def (⊓-lb₂ e₁ e₁') (⊓-lb₂ e₂ e₂')
  ⊓-lb₂ *             *                        | kind*    = ⊑*
  ⊓-lb₂ □             □                        | kind□    = ⊑□
  ⊓-lb₂ ⟨ m ⟩         ⟨ n ⟩                    | kindVar  with m ≟ℕ n
  ...                                                        | yes refl = ⊑Var
  ...                                                        | no  _    = ⊑□
  ⊓-lb₂ _             _                        | diff     = ⊑□

  -- Meet is greatest lower bound
  ⊓-glb : ∀ {e e₁ e₂} → e ⊑ e₁ → e ⊑ e₂ → e ⊑ e₁ ⊓ e₂
  ⊓-glb ⊑□ _                             = ⊑□
  ⊓-glb ⊑* ⊑*                            = ⊑*
  ⊓-glb (⊑Var {n}) (⊑Var {n})            with n ≟ℕ n
  ...                                       | yes _     = ⊑Var
  ...                                       | no  contr = ⊥-elim (contr refl)
  ⊓-glb (⊑λ pt pe)   (⊑λ qt qe)          = ⊑λ (⊑tLat.⊓-greatest pt qt) (⊓-glb pe qe)
  ⊓-glb (⊑λu pe)     (⊑λu qe)            = ⊑λu (⊓-glb pe qe)
  ⊓-glb (⊑∘ pe₁ pe₂) (⊑∘ qe₁ qe₂)        = ⊑∘ (⊓-glb pe₁ qe₁) (⊓-glb pe₂ qe₂)
  ⊓-glb (⊑<> pe pt)  (⊑<> qe qt)         = ⊑<> (⊓-glb pe qe) (⊑tLat.⊓-greatest pt qt)
  ⊓-glb (⊑& pe₁ pe₂) (⊑& qe₁ qe₂)        = ⊑& (⊓-glb pe₁ qe₁) (⊓-glb pe₂ qe₂)
  ⊓-glb (⊑ι₁ pe)     (⊑ι₁ qe)            = ⊑ι₁ (⊓-glb pe qe)
  ⊓-glb (⊑ι₂ pe)     (⊑ι₂ qe)            = ⊑ι₂ (⊓-glb pe qe)
  ⊓-glb (⊑case pe pe₁ pe₂) (⊑case qe qe₁ qe₂)
                                  = ⊑case (⊓-glb pe qe) (⊓-glb pe₁ qe₁) (⊓-glb pe₂ qe₂)
  ⊓-glb (⊑π₁ pe)     (⊑π₁ qe)            = ⊑π₁ (⊓-glb pe qe)
  ⊓-glb (⊑π₂ pe)     (⊑π₂ qe)            = ⊑π₂ (⊓-glb pe qe)
  ⊓-glb (⊑Λ pe)      (⊑Λ qe)             = ⊑Λ (⊓-glb pe qe)
  ⊓-glb (⊑def pe₁ pe₂) (⊑def qe₁ qe₂)    = ⊑def (⊓-glb pe₁ qe₁) (⊓-glb pe₂ qe₂)

  ⊓-infimum : Infimum _⊑_ _⊓_
  ⊓-infimum e₁ e₂ = ⊓-lb₁ e₁ e₂ , ⊓-lb₂ e₁ e₂ , λ e → ⊓-glb {e} {e₁} {e₂}

  ⊑-isMeetSemilattice : IsMeetSemilattice _≡_ _⊑_ _⊓_
  ⊑-isMeetSemilattice = record
                        { isPartialOrder = ⊑.isPartialOrder
                        ; infimum        = ⊓-infimum
                        }

module ⊑Lat where
  open IsMeetSemilattice ⊑-isMeetSemilattice public
    using (infimum)
    renaming (∧-greatest to ⊓-greatest; x∧y≤x to x⊓y⊑x; x∧y≤y to x⊓y⊑y)

  isMeetSemilattice = ⊑-isMeetSemilattice

open LiftMeetSemilattice ⊑-isMeetSemilattice public

private
  ⊔-identityₗ : ∀ e → □ ⊔ e ≡ e
  ⊔-identityₗ e with diag □ e
  ⊔-identityₗ □ | kind□ = refl
  ⊔-identityₗ _ | diff  = refl

  ⊔-identityᵣ : ∀ e → e ⊔ □ ≡ e
  ⊔-identityᵣ e with diag e □
  ⊔-identityᵣ □    | kind□ = refl
  ⊔-identityᵣ e    | diff  with e ≟e □
  ...                         | yes refl = refl
  ...                         | no  _    = refl

  -- Join upper bounds (requires bounded hypotheses instead of consistency)
  ⊔-ub₁ : ∀ {e₁ e₂ e} → e₁ ⊑ e → e₂ ⊑ e → e₁ ⊑ e₁ ⊔ e₂
  ⊔-ub₁ ⊑□ _                           = ⊑□
  ⊔-ub₁ {e₁ = e₁} p ⊑□                 rewrite ⊔-identityᵣ e₁ = ⊑.refl
  ⊔-ub₁ ⊑*               ⊑*            = ⊑*
  ⊔-ub₁ ⊑Var             ⊑Var          = ⊑Var
  ⊔-ub₁ (⊑λ pt pe)       (⊑λ qt qe)    = ⊑λ (~t.⊔-ub₁ (⊑t-consistent pt qt)) (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑λu pe)         (⊑λu qe)      = ⊑λu (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑∘ pe₁ pe₂)    (⊑∘ qe₁ qe₂)   = ⊑∘ (⊔-ub₁ pe₁ qe₁) (⊔-ub₁ pe₂ qe₂)
  ⊔-ub₁ (⊑<> pe pt)      (⊑<> qe qt)   = ⊑<> (⊔-ub₁ pe qe) (~t.⊔-ub₁ (⊑t-consistent pt qt))
  ⊔-ub₁ (⊑& pe₁ pe₂)    (⊑& qe₁ qe₂)   = ⊑& (⊔-ub₁ pe₁ qe₁) (⊔-ub₁ pe₂ qe₂)
  ⊔-ub₁ (⊑ι₁ pe)         (⊑ι₁ qe)      = ⊑ι₁ (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑ι₂ pe)         (⊑ι₂ qe)      = ⊑ι₂ (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑case pe pe₁ pe₂) (⊑case qe qe₁ qe₂)
    = ⊑case (⊔-ub₁ pe qe) (⊔-ub₁ pe₁ qe₁) (⊔-ub₁ pe₂ qe₂)
  ⊔-ub₁ (⊑π₁ pe)         (⊑π₁ qe)      = ⊑π₁ (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑π₂ pe)         (⊑π₂ qe)      = ⊑π₂ (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑Λ pe)          (⊑Λ qe)       = ⊑Λ (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑def pe₁ pe₂)  (⊑def qe₁ qe₂) = ⊑def (⊔-ub₁ pe₁ qe₁) (⊔-ub₁ pe₂ qe₂)

  ⊔-ub₂ : ∀ {e₁ e₂ e} → e₁ ⊑ e → e₂ ⊑ e → e₂ ⊑ e₁ ⊔ e₂
  ⊔-ub₂ {e₂ = e₂} ⊑□ q                 rewrite ⊔-identityₗ e₂ = ⊑.refl
  ⊔-ub₂ _ ⊑□                           = ⊑□
  ⊔-ub₂ ⊑*               ⊑*            = ⊑*
  ⊔-ub₂ ⊑Var             ⊑Var          = ⊑Var
  ⊔-ub₂ (⊑λ pt pe)       (⊑λ qt qe)    = ⊑λ (~t.⊔-ub₂ (⊑t-consistent pt qt)) (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑λu pe)         (⊑λu qe)      = ⊑λu (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑∘ pe₁ pe₂)    (⊑∘ qe₁ qe₂)   = ⊑∘ (⊔-ub₂ pe₁ qe₁) (⊔-ub₂ pe₂ qe₂)
  ⊔-ub₂ (⊑<> pe pt)      (⊑<> qe qt)   = ⊑<> (⊔-ub₂ pe qe) (~t.⊔-ub₂ (⊑t-consistent pt qt))
  ⊔-ub₂ (⊑& pe₁ pe₂)    (⊑& qe₁ qe₂)   = ⊑& (⊔-ub₂ pe₁ qe₁) (⊔-ub₂ pe₂ qe₂)
  ⊔-ub₂ (⊑ι₁ pe)         (⊑ι₁ qe)      = ⊑ι₁ (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑ι₂ pe)         (⊑ι₂ qe)      = ⊑ι₂ (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑case pe pe₁ pe₂) (⊑case qe qe₁ qe₂)
    = ⊑case (⊔-ub₂ pe qe) (⊔-ub₂ pe₁ qe₁) (⊔-ub₂ pe₂ qe₂)
  ⊔-ub₂ (⊑π₁ pe)         (⊑π₁ qe)      = ⊑π₁ (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑π₂ pe)         (⊑π₂ qe)      = ⊑π₂ (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑Λ pe)          (⊑Λ qe)       = ⊑Λ (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑def pe₁ pe₂)  (⊑def qe₁ qe₂) = ⊑def (⊔-ub₂ pe₁ qe₁) (⊔-ub₂ pe₂ qe₂)

  ⊔-lub : ∀ {e₁ e₂ e} → e₁ ⊑ e → e₂ ⊑ e → e₁ ⊔ e₂ ⊑ e
  ⊔-lub {e₂ = e₂} ⊑□ q                 rewrite ⊔-identityₗ e₂ = q
  ⊔-lub {e₁ = e₁} p  ⊑□                rewrite ⊔-identityᵣ e₁ = p
  ⊔-lub ⊑*               ⊑*            = ⊑*
  ⊔-lub ⊑Var             ⊑Var          = ⊑Var
  ⊔-lub (⊑λ pt pe)       (⊑λ qt qe)    =
    ⊑λ (~t.⊔-lub (⊑t-consistent pt qt) pt qt) (⊔-lub pe qe)
  ⊔-lub (⊑λu pe)         (⊑λu qe)      = ⊑λu (⊔-lub pe qe)
  ⊔-lub (⊑∘ pe₁ pe₂)    (⊑∘ qe₁ qe₂)   = ⊑∘ (⊔-lub pe₁ qe₁) (⊔-lub pe₂ qe₂)
  ⊔-lub (⊑<> pe pt)      (⊑<> qe qt)   =
    ⊑<> (⊔-lub pe qe) (~t.⊔-lub (⊑t-consistent pt qt) pt qt)
  ⊔-lub (⊑& pe₁ pe₂)    (⊑& qe₁ qe₂)   = ⊑& (⊔-lub pe₁ qe₁) (⊔-lub pe₂ qe₂)
  ⊔-lub (⊑ι₁ pe)         (⊑ι₁ qe)      = ⊑ι₁ (⊔-lub pe qe)
  ⊔-lub (⊑ι₂ pe)         (⊑ι₂ qe)      = ⊑ι₂ (⊔-lub pe qe)
  ⊔-lub (⊑case pe pe₁ pe₂) (⊑case qe qe₁ qe₂) =
    ⊑case (⊔-lub pe qe) (⊔-lub pe₁ qe₁) (⊔-lub pe₂ qe₂)
  ⊔-lub (⊑π₁ pe)         (⊑π₁ qe)      = ⊑π₁ (⊔-lub pe qe)
  ⊔-lub (⊑π₂ pe)         (⊑π₂ qe)      = ⊑π₂ (⊔-lub pe qe)
  ⊔-lub (⊑Λ pe)          (⊑Λ qe)       = ⊑Λ (⊔-lub pe qe)
  ⊔-lub (⊑def pe₁ pe₂)  (⊑def qe₁ qe₂) = ⊑def (⊔-lub pe₁ qe₁) (⊔-lub pe₂ qe₂)

  ⊥ₛ' : ∀ {e} → ⌊ e ⌋
  ⊥ₛ' {e} = □ isSlice ⊑□

  ⊥ₛ-min : ∀ {e} → Minimum (_⊑ₛ_ {e}) ⊥ₛ'
  ⊥ₛ-min υ = ⊑□

  ⊔-preserves-⊑ : ∀ {e₁ e₂ e} → e₁ ⊑ e → e₂ ⊑ e → e₁ ⊔ e₂ ⊑ e
  ⊔-preserves-⊑ p q = ⊔-lub p q

-- Lift joins
_⊔ₛ_ : ∀ {e} → ⌊ e ⌋ → ⌊ e ⌋ → ⌊ e ⌋
υ ⊔ₛ υ' = υ .↓ ⊔ υ' .↓ isSlice ⊔-preserves-⊑ (υ .proof) (υ' .proof)

infixl 7 _⊔ₛ_

private
  ⊔ₛ-ub₁ : ∀ {e} (υ₁ υ₂ : ⌊ e ⌋) → υ₁ ⊑ₛ υ₁ ⊔ₛ υ₂
  ⊔ₛ-ub₁ υ₁ υ₂ = ⊔-ub₁ (υ₁ .proof) (υ₂ .proof)

  ⊔ₛ-ub₂ : ∀ {e} (υ₁ υ₂ : ⌊ e ⌋) → υ₂ ⊑ₛ υ₁ ⊔ₛ υ₂
  ⊔ₛ-ub₂ υ₁ υ₂ = ⊔-ub₂ (υ₁ .proof) (υ₂ .proof)

  ⊔ₛ-lub : ∀ {e} {υ υ₁ υ₂ : ⌊ e ⌋} → υ₁ ⊑ₛ υ → υ₂ ⊑ₛ υ → υ₁ ⊔ₛ υ₂ ⊑ₛ υ
  ⊔ₛ-lub {_} {υ} {υ₁} {υ₂} p q = ⊔-preserves-⊑ p q

  ⊔ₛ-supremum : ∀ {e} → Supremum (_⊑ₛ_ {e}) _⊔ₛ_
  ⊔ₛ-supremum υ₁ υ₂ = ⊔ₛ-ub₁ υ₁ υ₂ , ⊔ₛ-ub₂ υ₁ υ₂ , λ υ → ⊔ₛ-lub {υ = υ} {υ₁} {υ₂}

  ⊑ₛ-isJoinSemilattice : ∀ {e} → IsJoinSemilattice (_≡_ on ↓) (_⊑ₛ_ {e}) _⊔ₛ_
  ⊑ₛ-isJoinSemilattice = record
                         { isPartialOrder = ⊑ₛ.isPartialOrder
                         ; supremum       = ⊔ₛ-supremum
                         }

  ⊑ₛ-isLattice : ∀ {e} → IsLattice (_≡_ on ↓) (_⊑ₛ_ {e}) _⊔ₛ_ _⊓ₛ_
  ⊑ₛ-isLattice = record
                 { isPartialOrder = ⊑ₛ.isPartialOrder
                 ; supremum       = ⊔ₛ-supremum
                 ; infimum        = ⊓ₛ.infimum
                 }

  ⊑ₛ-isBoundedLattice : ∀ {e} → IsBoundedLattice (_≡_ on ↓) (_⊑ₛ_ {e}) _⊔ₛ_ _⊓ₛ_ ⊤ₛ' ⊥ₛ'
  ⊑ₛ-isBoundedLattice = record
                        { isLattice = ⊑ₛ-isLattice
                        ; maximum   = ⊤ₛ-max
                        ; minimum   = ⊥ₛ-min
                        }

  □⊓-absorb : ∀ e → □ ⊓ e ≡ □
  □⊓-absorb e with diag □ e
  ... | kind□ = refl
  ... | diff  = refl

  ⊓□-absorb : ∀ e → e ⊓ □ ≡ □
  ⊓□-absorb e with diag e □
  ... | kind□ = refl
  ... | diff  = refl

  □⊔□ : □ ⊔ □ ≡ □
  □⊔□ = refl

  dist : ∀ {e e₁ e₂ e₃} → e₁ ⊑ e → e₂ ⊑ e → e₃ ⊑ e
       → e₁ ⊓ (e₂ ⊔ e₃) ≡ (e₁ ⊓ e₂) ⊔ (e₁ ⊓ e₃)
  dist {e₂ = e₂} {e₃ = e₃} ⊑□ _ _ =
    begin
    □ ⊓ (e₂ ⊔ e₃)        ≡⟨ □⊓-absorb (e₂ ⊔ e₃) ⟩
    □                    ≡⟨⟩
    □ ⊔ □                ≡˘⟨ cong₂ _⊔_ (□⊓-absorb e₂) (□⊓-absorb e₃) ⟩
    (□ ⊓ e₂) ⊔ (□ ⊓ e₃)  ∎
  dist {e₁ = e₁} {e₃ = e₃} _ ⊑□ _ =
    begin
    e₁ ⊓ (□ ⊔ e₃)         ≡⟨ cong (e₁ ⊓_) (⊔-identityₗ e₃) ⟩
    e₁ ⊓ e₃               ≡˘⟨ ⊔-identityₗ (e₁ ⊓ e₃) ⟩
    □ ⊔ (e₁ ⊓ e₃)         ≡˘⟨ cong (_⊔ (e₁ ⊓ e₃)) (⊓□-absorb e₁) ⟩
    (e₁ ⊓ □) ⊔ (e₁ ⊓ e₃)  ∎
  dist {e₁ = e₁} {e₂ = e₂} _ _ ⊑□ =
    begin
    e₁ ⊓ (e₂ ⊔ □)         ≡⟨ cong (e₁ ⊓_) (⊔-identityᵣ e₂) ⟩
    e₁ ⊓ e₂               ≡˘⟨ ⊔-identityᵣ (e₁ ⊓ e₂) ⟩
    (e₁ ⊓ e₂) ⊔ □         ≡˘⟨ cong ((e₁ ⊓ e₂) ⊔_) (⊓□-absorb e₁) ⟩
    (e₁ ⊓ e₂) ⊔ (e₁ ⊓ □)  ∎
  dist ⊑*               ⊑*   ⊑*   = refl
  dist (⊑Var {n})       ⊑Var ⊑Var with n ≟ℕ n
  ...                                 | yes _ = refl
  ...                                 | no n≢n = ⊥-elim (n≢n refl)
  dist (⊑λ pt pe)       (⊑λ qt qe)      (⊑λ rt re)
    = cong₂ λ:_⇒_ (⊑tₛLat.⊓ₛ-distribˡ-⊔ₛ (↑t pt) (↑t qt) (↑t rt)) (dist pe qe re)
  dist (⊑λu pe)         (⊑λu qe)        (⊑λu re)
    = cong λ⇒_ (dist pe qe re)
  dist (⊑∘ pe₁ pe₂)     (⊑∘ qe₁ qe₂)    (⊑∘ re₁ re₂)
    = cong₂ _∘_ (dist pe₁ qe₁ re₁) (dist pe₂ qe₂ re₂)
  dist (⊑<> pe pt)      (⊑<> qe qt)     (⊑<> re rt)     
    = cong₂ _<_> (dist pe qe re) (⊑tₛLat.⊓ₛ-distribˡ-⊔ₛ (↑t pt) (↑t qt) (↑t rt))
  dist (⊑& pe₁ pe₂)     (⊑& qe₁ qe₂)    (⊑& re₁ re₂)    
    = cong₂ _&_ (dist pe₁ qe₁ re₁) (dist pe₂ qe₂ re₂)
  dist (⊑ι₁ pe)         (⊑ι₁ qe)        (⊑ι₁ re) = cong ι₁ (dist pe qe re)
  dist (⊑ι₂ pe)         (⊑ι₂ qe)        (⊑ι₂ re) = cong ι₂ (dist pe qe re)
  dist (⊑case pe pe₁ pe₂) (⊑case qe qe₁ qe₂) (⊑case re re₁ re₂)
    = case-cong (dist pe qe re) (dist pe₁ qe₁ re₁) (dist pe₂ qe₂ re₂)
      where
      case-cong : ∀ {a a' b b' c c' : Exp}
                → a ≡ a' → b ≡ b' → c ≡ c'
                → case a of b · c ≡ case a' of b' · c'
      case-cong refl refl refl = refl
  dist (⊑π₁ pe)         (⊑π₁ qe)        (⊑π₁ re)        = cong π₁ (dist pe qe re)
  dist (⊑π₂ pe)         (⊑π₂ qe)        (⊑π₂ re)        = cong π₂ (dist pe qe re)
  dist (⊑Λ pe)          (⊑Λ qe)         (⊑Λ re)         = cong Λ (dist pe qe re)
  dist (⊑def pe₁ pe₂)   (⊑def qe₁ qe₂)  (⊑def re₁ re₂)  =
    cong₂ def_⊢_ (dist pe₁ qe₁ re₁) (dist pe₂ qe₂ re₂)

  ⊓ₛ-distribˡ-⊔ₛ : ∀ {e} (υ₁ υ₂ υ₃ : ⌊ e ⌋) → (υ₁ ⊓ₛ (υ₂ ⊔ₛ υ₃)) ≈ₛ ((υ₁ ⊓ₛ υ₂) ⊔ₛ (υ₁ ⊓ₛ υ₃))
  ⊓ₛ-distribˡ-⊔ₛ υ₁ υ₂ υ₃ = dist (υ₁ .proof) (υ₂ .proof) (υ₃ .proof)

  ⊑ₛ-isDistributiveLattice : ∀ {e} → IsDistributiveLattice (_≡_ on ↓) (_⊑ₛ_ {e}) _⊔ₛ_ _⊓ₛ_
  ⊑ₛ-isDistributiveLattice = record
                             { isLattice    = ⊑ₛ-isLattice
                             ; ∧-distribˡ-∨ = ⊓ₛ-distribˡ-⊔ₛ
                             }

module ⊑ₛLat {e} where
  open IsBoundedLattice (⊑ₛ-isBoundedLattice {e}) public
    using (infimum; supremum;
           isBoundedJoinSemilattice; isBoundedMeetSemilattice; isJoinSemilattice; isMeetSemilattice; isLattice)
    renaming (x∧y≤x to x⊓ₛy⊑ₛx; x∧y≤y to x⊓ₛy⊑ₛy; x≤x∨y to x⊑ₛx⊔ₛy; y≤x∨y to y⊑ₛx⊔ₛy;
              ∧-greatest to ⊓ₛ-greatest; ∨-least to ⊔ₛ-least;
              maximum to ⊤ₛ-max; minimum to ⊥ₛ-min)
  ⊤ₛ : ⌊ e ⌋
  ⊤ₛ = ⊤ₛ'

  ⊥ₛ : ⌊ e ⌋
  ⊥ₛ = ⊥ₛ'

  isBoundedLattice = ⊑ₛ-isBoundedLattice

  open IsDistributiveLattice (⊑ₛ-isDistributiveLattice {e}) public
    using () renaming (∧-distribˡ-∨ to ⊓ₛ-distribˡ-⊔ₛ)

  isDistributiveLattice = ⊑ₛ-isDistributiveLattice
