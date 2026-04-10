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

open import Core.Instances
open import Core.Typ
open import Core.Exp.Base
open import Core.Exp.Equality
open import Core.Exp.Precision

private
  _⊓e_ : Exp → Exp → Exp
  e ⊓e e' with diag e e'
  ...       | diff                                    = □
  ...       | kind□                                   = □
  ...       | kind*                                   = *
  ...       | kindλ  {τ} {τ'} {e₁} {e₁'}              = λ: (τ ⊓ τ') ⇒ (e₁ ⊓e e₁')
  ...       | kindλu {e₁} {e₁'}                       = λ⇒ (e₁ ⊓e e₁')
  ...       | kind∘  {e₁} {e₂} {e₁'} {e₂'}            = (e₁ ⊓e e₁') ∘ (e₂ ⊓e e₂')
  ...       | kind<> {e₁} {e₁'} {τ} {τ'}              = (e₁ ⊓e e₁') < (τ ⊓ τ') >
  ...       | kind&  {e₁} {e₂} {e₁'} {e₂'}            = (e₁ ⊓e e₁') & (e₂ ⊓e e₂')
  ...       | kindι₁ {e₁} {e₁'}                       = ι₁ (e₁ ⊓e e₁')
  ...       | kindι₂ {e₁} {e₁'}                       = ι₂ (e₁ ⊓e e₁')
  ...       | kindcase {e} {e'} {e₁} {e₂} {e₁'} {e₂'} = case (e ⊓e e') of (e₁ ⊓e e₁') · (e₂ ⊓e e₂')
  ...       | kindπ₁ {e₁} {e₁'}                       = π₁ (e₁ ⊓e e₁')
  ...       | kindπ₂ {e₁} {e₁'}                       = π₂ (e₁ ⊓e e₁')
  ...       | kindΛ  {e₁} {e₁'}                       = Λ (e₁ ⊓e e₁')
  ...       | kinddef {e₁} {e₂} {e₁'} {e₂'}           = def (e₁ ⊓e e₁') ⊢ (e₂ ⊓e e₂')
  ...       | kindVar {m} {n}            with m ≟ℕ n
  ...                                       | yes _   = ⟨ m ⟩
  ...                                       | no  _   = □

  infixl 6 _⊓e_

  _⊔e_ : Exp → Exp → Exp
  e ⊔e e' with diag e e'
  ...       | kind□                                   = □
  ...       | kind*                                   = *
  ...       | kindVar {m}                             = ⟨ m ⟩
  ...       | kindλ  {τ} {τ'} {e₁} {e₁'}              = λ: (τ ⊔ τ') ⇒ (e₁ ⊔e e₁')
  ...       | kindλu {e₁} {e₁'}                       = λ⇒ (e₁ ⊔e e₁')
  ...       | kind∘  {e₁} {e₂} {e₁'} {e₂'}            = (e₁ ⊔e e₁') ∘ (e₂ ⊔e e₂')
  ...       | kind<> {e₁} {e₁'} {τ} {τ'}              = (e₁ ⊔e e₁') < (τ ⊔ τ') >
  ...       | kind&  {e₁} {e₂} {e₁'} {e₂'}            = (e₁ ⊔e e₁') & (e₂ ⊔e e₂')
  ...       | kindι₁ {e₁} {e₁'}                       = ι₁ (e₁ ⊔e e₁')
  ...       | kindι₂ {e₁} {e₁'}                       = ι₂ (e₁ ⊔e e₁')
  ...       | kindcase {e} {e'} {e₁} {e₂} {e₁'} {e₂'} = case (e ⊔e e') of (e₁ ⊔e e₁') · (e₂ ⊔e e₂')
  ...       | kindπ₁ {e₁} {e₁'}                       = π₁ (e₁ ⊔e e₁')
  ...       | kindπ₂ {e₁} {e₁'}                       = π₂ (e₁ ⊔e e₁')
  ...       | kindΛ  {e₁} {e₁'}                       = Λ (e₁ ⊔e e₁')
  ...       | kinddef {e₁} {e₂} {e₁'} {e₂'}           = def (e₁ ⊔e e₁') ⊢ (e₂ ⊔e e₂')
  e ⊔e e'    | diff with e ≟ □
  ...                | yes _  = e'
  ...                | no  _  = e

  infixl 6 _⊔e_

  -- Meet lower bounds
  ⊓-lb₁ : ∀ e₁ e₂ → e₁ ⊓e e₂ ⊑ e₁
  ⊓-lb₁ e       e'                         with diag e e'
  ⊓-lb₁ (λ: τ ⇒ e₁)   (λ: τ' ⇒ e₁')            | kindλ
                                                 = ⊑λ (⊑Lat.x⊓y⊑x τ τ') (⊓-lb₁ e₁ e₁')
  ⊓-lb₁ (λ⇒ e₁)       (λ⇒ e₁')                 | kindλu   = ⊑λu (⊓-lb₁ e₁ e₁')
  ⊓-lb₁ (e₁ ∘ e₂)     (e₁' ∘ e₂')              | kind∘    = ⊑∘ (⊓-lb₁ e₁ e₁') (⊓-lb₁ e₂ e₂')
  ⊓-lb₁ (e₁ < τ >)    (e₁' < τ' >)             | kind<>
                                                 = ⊑<> (⊓-lb₁ e₁ e₁') (⊑Lat.x⊓y⊑x τ τ')
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

  ⊓-lb₂ : ∀ e₁ e₂ → e₁ ⊓e e₂ ⊑ e₂
  ⊓-lb₂ e       e'                          with diag e e'
  ⊓-lb₂ (λ: τ ⇒ e₁)   (λ: τ' ⇒ e₁')            | kindλ
                                                 = ⊑λ (⊑Lat.x⊓y⊑y τ τ') (⊓-lb₂ e₁ e₁')
  ⊓-lb₂ (λ⇒ e₁)       (λ⇒ e₁')                 | kindλu   = ⊑λu (⊓-lb₂ e₁ e₁')
  ⊓-lb₂ (e₁ ∘ e₂)     (e₁' ∘ e₂')              | kind∘    = ⊑∘ (⊓-lb₂ e₁ e₁') (⊓-lb₂ e₂ e₂')
  ⊓-lb₂ (e₁ < τ >)    (e₁' < τ' >)             | kind<>
                                                 = ⊑<> (⊓-lb₂ e₁ e₁') (⊑Lat.x⊓y⊑y τ τ')
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
  ⊓-glb : ∀ {e e₁ e₂} → e ⊑ e₁ → e ⊑ e₂ → e ⊑ e₁ ⊓e e₂
  ⊓-glb ⊑□ _                             = ⊑□
  ⊓-glb ⊑* ⊑*                            = ⊑*
  ⊓-glb (⊑Var {n}) (⊑Var {n})            with n ≟ℕ n
  ...                                       | yes _     = ⊑Var
  ...                                       | no  contr = ⊥-elim (contr refl)
  ⊓-glb (⊑λ pt pe)   (⊑λ qt qe)          = ⊑λ (⊑Lat.⊓-greatest pt qt) (⊓-glb pe qe)
  ⊓-glb (⊑λu pe)     (⊑λu qe)            = ⊑λu (⊓-glb pe qe)
  ⊓-glb (⊑∘ pe₁ pe₂) (⊑∘ qe₁ qe₂)        = ⊑∘ (⊓-glb pe₁ qe₁) (⊓-glb pe₂ qe₂)
  ⊓-glb (⊑<> pe pt)  (⊑<> qe qt)         = ⊑<> (⊓-glb pe qe) (⊑Lat.⊓-greatest pt qt)
  ⊓-glb (⊑& pe₁ pe₂) (⊑& qe₁ qe₂)        = ⊑& (⊓-glb pe₁ qe₁) (⊓-glb pe₂ qe₂)
  ⊓-glb (⊑ι₁ pe)     (⊑ι₁ qe)            = ⊑ι₁ (⊓-glb pe qe)
  ⊓-glb (⊑ι₂ pe)     (⊑ι₂ qe)            = ⊑ι₂ (⊓-glb pe qe)
  ⊓-glb (⊑case pe pe₁ pe₂) (⊑case qe qe₁ qe₂)
                                  = ⊑case (⊓-glb pe qe) (⊓-glb pe₁ qe₁) (⊓-glb pe₂ qe₂)
  ⊓-glb (⊑π₁ pe)     (⊑π₁ qe)            = ⊑π₁ (⊓-glb pe qe)
  ⊓-glb (⊑π₂ pe)     (⊑π₂ qe)            = ⊑π₂ (⊓-glb pe qe)
  ⊓-glb (⊑Λ pe)      (⊑Λ qe)             = ⊑Λ (⊓-glb pe qe)
  ⊓-glb (⊑def pe₁ pe₂) (⊑def qe₁ qe₂)    = ⊑def (⊓-glb pe₁ qe₁) (⊓-glb pe₂ qe₂)

  ⊓-infimum : Infimum _⊑e_ _⊓e_
  ⊓-infimum e₁ e₂ = ⊓-lb₁ e₁ e₂ , ⊓-lb₂ e₁ e₂ , λ e → ⊓-glb {e} {e₁} {e₂}

  ⊑-isMeetSemilattice : IsMeetSemilattice _≡_ _⊑e_ _⊓e_
  ⊑-isMeetSemilattice = record
                        { isPartialOrder = ⊑.isPartialOrder
                        ; infimum        = ⊓-infimum
                        }

  ⊔-identityₗ : ∀ e → □ ⊔e e ≡ e
  ⊔-identityₗ e with diag □ e
  ⊔-identityₗ □ | kind□ = refl
  ⊔-identityₗ _ | diff  = refl

  ⊔-identityᵣ : ∀ e → e ⊔e □ ≡ e
  ⊔-identityᵣ e with diag e □
  ⊔-identityᵣ □    | kind□ = refl
  ⊔-identityᵣ e    | diff  with e ≟ □
  ...                         | yes refl = refl
  ...                         | no  _    = refl

  -- Join upper bounds (requires bounded hypotheses instead of consistency)
  ⊔-ub₁ : ∀ {e₁ e₂ e} → e₁ ⊑ e → e₂ ⊑ e → e₁ ⊑ e₁ ⊔e e₂
  ⊔-ub₁ ⊑□ _                           = ⊑□
  ⊔-ub₁ {e₁ = e₁} p ⊑□                 rewrite ⊔-identityᵣ e₁ = ⊑.refl {A = Exp}
  ⊔-ub₁ ⊑*               ⊑*            = ⊑*
  ⊔-ub₁ ⊑Var             ⊑Var          = ⊑Var
  ⊔-ub₁ (⊑λ pt pe)       (⊑λ qt qe)    = ⊑λ (~.⊔-ub₁ (⊑-consistent pt qt)) (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑λu pe)         (⊑λu qe)      = ⊑λu (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑∘ pe₁ pe₂)    (⊑∘ qe₁ qe₂)   = ⊑∘ (⊔-ub₁ pe₁ qe₁) (⊔-ub₁ pe₂ qe₂)
  ⊔-ub₁ (⊑<> pe pt)      (⊑<> qe qt)   = ⊑<> (⊔-ub₁ pe qe) (~.⊔-ub₁ (⊑-consistent pt qt))
  ⊔-ub₁ (⊑& pe₁ pe₂)    (⊑& qe₁ qe₂)   = ⊑& (⊔-ub₁ pe₁ qe₁) (⊔-ub₁ pe₂ qe₂)
  ⊔-ub₁ (⊑ι₁ pe)         (⊑ι₁ qe)      = ⊑ι₁ (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑ι₂ pe)         (⊑ι₂ qe)      = ⊑ι₂ (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑case pe pe₁ pe₂) (⊑case qe qe₁ qe₂)
    = ⊑case (⊔-ub₁ pe qe) (⊔-ub₁ pe₁ qe₁) (⊔-ub₁ pe₂ qe₂)
  ⊔-ub₁ (⊑π₁ pe)         (⊑π₁ qe)      = ⊑π₁ (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑π₂ pe)         (⊑π₂ qe)      = ⊑π₂ (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑Λ pe)          (⊑Λ qe)       = ⊑Λ (⊔-ub₁ pe qe)
  ⊔-ub₁ (⊑def pe₁ pe₂)  (⊑def qe₁ qe₂) = ⊑def (⊔-ub₁ pe₁ qe₁) (⊔-ub₁ pe₂ qe₂)

  ⊔-ub₂ : ∀ {e₁ e₂ e} → e₁ ⊑ e → e₂ ⊑ e → e₂ ⊑ e₁ ⊔e e₂
  ⊔-ub₂ {e₂ = e₂} ⊑□ q                 rewrite ⊔-identityₗ e₂ = ⊑.refl {A = Exp}
  ⊔-ub₂ _ ⊑□                           = ⊑□
  ⊔-ub₂ ⊑*               ⊑*            = ⊑*
  ⊔-ub₂ ⊑Var             ⊑Var          = ⊑Var
  ⊔-ub₂ (⊑λ pt pe)       (⊑λ qt qe)    = ⊑λ (~.⊔-ub₂ (⊑-consistent pt qt)) (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑λu pe)         (⊑λu qe)      = ⊑λu (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑∘ pe₁ pe₂)    (⊑∘ qe₁ qe₂)   = ⊑∘ (⊔-ub₂ pe₁ qe₁) (⊔-ub₂ pe₂ qe₂)
  ⊔-ub₂ (⊑<> pe pt)      (⊑<> qe qt)   = ⊑<> (⊔-ub₂ pe qe) (~.⊔-ub₂ (⊑-consistent pt qt))
  ⊔-ub₂ (⊑& pe₁ pe₂)    (⊑& qe₁ qe₂)   = ⊑& (⊔-ub₂ pe₁ qe₁) (⊔-ub₂ pe₂ qe₂)
  ⊔-ub₂ (⊑ι₁ pe)         (⊑ι₁ qe)      = ⊑ι₁ (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑ι₂ pe)         (⊑ι₂ qe)      = ⊑ι₂ (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑case pe pe₁ pe₂) (⊑case qe qe₁ qe₂)
    = ⊑case (⊔-ub₂ pe qe) (⊔-ub₂ pe₁ qe₁) (⊔-ub₂ pe₂ qe₂)
  ⊔-ub₂ (⊑π₁ pe)         (⊑π₁ qe)      = ⊑π₁ (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑π₂ pe)         (⊑π₂ qe)      = ⊑π₂ (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑Λ pe)          (⊑Λ qe)       = ⊑Λ (⊔-ub₂ pe qe)
  ⊔-ub₂ (⊑def pe₁ pe₂)  (⊑def qe₁ qe₂) = ⊑def (⊔-ub₂ pe₁ qe₁) (⊔-ub₂ pe₂ qe₂)

  ⊔-lub : ∀ {e₁ e₂ e} → e₁ ⊑ e → e₂ ⊑ e → e₁ ⊔e e₂ ⊑ e
  ⊔-lub {e₂ = e₂} ⊑□ q                 rewrite ⊔-identityₗ e₂ = q
  ⊔-lub {e₁ = e₁} p  ⊑□                rewrite ⊔-identityᵣ e₁ = p
  ⊔-lub ⊑*               ⊑*            = ⊑*
  ⊔-lub ⊑Var             ⊑Var          = ⊑Var
  ⊔-lub (⊑λ pt pe)       (⊑λ qt qe)    =
    ⊑λ (~.⊔-lub (⊑-consistent pt qt) pt qt) (⊔-lub pe qe)
  ⊔-lub (⊑λu pe)         (⊑λu qe)      = ⊑λu (⊔-lub pe qe)
  ⊔-lub (⊑∘ pe₁ pe₂)    (⊑∘ qe₁ qe₂)   = ⊑∘ (⊔-lub pe₁ qe₁) (⊔-lub pe₂ qe₂)
  ⊔-lub (⊑<> pe pt)      (⊑<> qe qt)   =
    ⊑<> (⊔-lub pe qe) (~.⊔-lub (⊑-consistent pt qt) pt qt)
  ⊔-lub (⊑& pe₁ pe₂)    (⊑& qe₁ qe₂)   = ⊑& (⊔-lub pe₁ qe₁) (⊔-lub pe₂ qe₂)
  ⊔-lub (⊑ι₁ pe)         (⊑ι₁ qe)      = ⊑ι₁ (⊔-lub pe qe)
  ⊔-lub (⊑ι₂ pe)         (⊑ι₂ qe)      = ⊑ι₂ (⊔-lub pe qe)
  ⊔-lub (⊑case pe pe₁ pe₂) (⊑case qe qe₁ qe₂) =
    ⊑case (⊔-lub pe qe) (⊔-lub pe₁ qe₁) (⊔-lub pe₂ qe₂)
  ⊔-lub (⊑π₁ pe)         (⊑π₁ qe)      = ⊑π₁ (⊔-lub pe qe)
  ⊔-lub (⊑π₂ pe)         (⊑π₂ qe)      = ⊑π₂ (⊔-lub pe qe)
  ⊔-lub (⊑Λ pe)          (⊑Λ qe)       = ⊑Λ (⊔-lub pe qe)
  ⊔-lub (⊑def pe₁ pe₂)  (⊑def qe₁ qe₂) = ⊑def (⊔-lub pe₁ qe₁) (⊔-lub pe₂ qe₂)

instance
  exp-meet : HasMeet Exp
  exp-meet = record { _⊓_ = _⊓e_ ; closure = λ p q → ⊑.trans {A = Exp} (⊓-lb₁ _ _) p }
  exp-join : HasJoin Exp
  exp-join = record { _⊔_ = _⊔e_ ; closure = ⊔-lub }
  exp-meetSemilattice : HasMeetSemilattice Exp
  exp-meetSemilattice = record { isMeetSemilattice = ⊑-isMeetSemilattice }

private
  ⊥ₛ' : ∀ {e : Exp} → ⌊ e ⌋
  ⊥ₛ' = □ isSlice ⊑□

  ⊥ₛ-min : ∀ {e : Exp} → Minimum (_⊑ₛ_ {A = Exp} {a = e}) ⊥ₛ'
  ⊥ₛ-min υ = ⊑□

  ⊔ₛ-ub₁ : ∀ {e : Exp} (υ₁ υ₂ : ⌊ e ⌋) → υ₁ ⊑ₛ (υ₁ ⊔ₛ υ₂)
  ⊔ₛ-ub₁ υ₁ υ₂ = ⊔-ub₁ (υ₁ .proof) (υ₂ .proof)

  ⊔ₛ-ub₂ : ∀ {e : Exp} (υ₁ υ₂ : ⌊ e ⌋) → υ₂ ⊑ₛ (υ₁ ⊔ₛ υ₂)
  ⊔ₛ-ub₂ υ₁ υ₂ = ⊔-ub₂ (υ₁ .proof) (υ₂ .proof)

  □⊓-absorb : ∀ e → □ ⊓e e ≡ □
  □⊓-absorb e with diag □ e
  ... | kind□ = refl
  ... | diff  = refl

  ⊓□-absorb : ∀ e → e ⊓e □ ≡ □
  ⊓□-absorb e with diag e □
  ... | kind□ = refl
  ... | diff  = refl

  dist : ∀ {e e₁ e₂ e₃} → e₁ ⊑ e → e₂ ⊑ e → e₃ ⊑ e
       → e₁ ⊓e (e₂ ⊔e e₃) ≡ (e₁ ⊓e e₂) ⊔e (e₁ ⊓e e₃)
  dist {e₂ = e₂} {e₃ = e₃} ⊑□ _ _ =
    begin
    □ ⊓e (e₂ ⊔e e₃)        ≡⟨ □⊓-absorb (e₂ ⊔e e₃) ⟩
    □                    ≡⟨⟩
    □ ⊔e □                ≡˘⟨ cong₂ _⊔e_ (□⊓-absorb e₂) (□⊓-absorb e₃) ⟩
    (□ ⊓e e₂) ⊔e (□ ⊓e e₃)  ∎
  dist {e₁ = e₁} {e₃ = e₃} _ ⊑□ _ =
    begin
    e₁ ⊓e (□ ⊔e e₃)         ≡⟨ cong (e₁ ⊓e_) (⊔-identityₗ e₃) ⟩
    e₁ ⊓e e₃               ≡˘⟨ ⊔-identityₗ (e₁ ⊓e e₃) ⟩
    □ ⊔e (e₁ ⊓e e₃)         ≡˘⟨ cong (_⊔e (e₁ ⊓e e₃)) (⊓□-absorb e₁) ⟩
    (e₁ ⊓e □) ⊔e (e₁ ⊓e e₃)  ∎
  dist {e₁ = e₁} {e₂ = e₂} _ _ ⊑□ =
    begin
    e₁ ⊓e (e₂ ⊔e □)         ≡⟨ cong (e₁ ⊓e_) (⊔-identityᵣ e₂) ⟩
    e₁ ⊓e e₂               ≡˘⟨ ⊔-identityᵣ (e₁ ⊓e e₂) ⟩
    (e₁ ⊓e e₂) ⊔e □         ≡˘⟨ cong ((e₁ ⊓e e₂) ⊔e_) (⊓□-absorb e₁) ⟩
    (e₁ ⊓e e₂) ⊔e (e₁ ⊓e □)  ∎
  dist ⊑*               ⊑*   ⊑*   = refl
  dist (⊑Var {n})       ⊑Var ⊑Var with n ≟ℕ n
  ...                                 | yes _ = refl
  ...                                 | no n≢n = ⊥-elim (n≢n refl)
  dist (⊑λ pt pe)       (⊑λ qt qe)      (⊑λ rt re)
    = cong₂ λ:_⇒_ (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ pt) (↑ qt) (↑ rt)) (dist pe qe re)
  dist (⊑λu pe)         (⊑λu qe)        (⊑λu re)
    = cong λ⇒_ (dist pe qe re)
  dist (⊑∘ pe₁ pe₂)    (⊑∘ qe₁ qe₂)    (⊑∘ re₁ re₂)
    = cong₂ _∘_ (dist pe₁ qe₁ re₁) (dist pe₂ qe₂ re₂)
  dist (⊑<> pe pt)      (⊑<> qe qt)     (⊑<> re rt)
    = cong₂ _<_> (dist pe qe re) (⊑ₛLat.⊓ₛ-distribˡ-⊔ₛ (↑ pt) (↑ qt) (↑ rt))
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

  ⊓ₛ-distribˡ-⊔ₛ' : ∀ {e : Exp} (υ₁ υ₂ υ₃ : ⌊ e ⌋) → (υ₁ ⊓ₛ (υ₂ ⊔ₛ υ₃)) ≈ₛ ((υ₁ ⊓ₛ υ₂) ⊔ₛ (υ₁ ⊓ₛ υ₃))
  ⊓ₛ-distribˡ-⊔ₛ' υ₁ υ₂ υ₃ = dist (υ₁ .proof) (υ₂ .proof) (υ₃ .proof)

instance
  exp-sliceLattice : SliceLattice Exp
  exp-sliceLattice = record
    { ⊥ₛ = ⊥ₛ'
    ; ⊥ₛ-min = ⊥ₛ-min
    ; x⊓ₛy⊑ₛx = λ s₁ s₂ → ⊓-lb₁ (s₁ .↓) (s₂ .↓)
    ; x⊓ₛy⊑ₛy = λ s₁ s₂ → ⊓-lb₂ (s₁ .↓) (s₂ .↓)
    ; ⊓ₛ-greatest = λ p q → ⊓-glb p q
    ; x⊑ₛx⊔ₛy = ⊔ₛ-ub₁
    ; y⊑ₛx⊔ₛy = ⊔ₛ-ub₂
    ; ⊓ₛ-distribˡ-⊔ₛ = ⊓ₛ-distribˡ-⊔ₛ'
    }
