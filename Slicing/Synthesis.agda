open import Data.Nat hiding (_+_; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary using (IsPartialOrder; IsDecPartialOrder; IsEquivalence; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong; cong₂; sym; trans)
open import Data.Maybe using (just)
open import Data.List using (_∷_; [])
open import Core
open import Core.Typ.Base using (diag; kind□; kind*; kindVar; kind+; kind×; kind⇒; kind∀; diff; shallow-disequality)
open import Data.Empty using (⊥-elim)
open import Semantics.Statics
open import Semantics.Metatheory using (static-gradual-syn; syn-precision; static-gradual-ana)

module Slicing.Synthesis where

-- Synthesis slice: sliced assumptions and expression that still synthesize
-- a given type slice υ. Indexed by the original derivation D.
record SynSlice {n : ℕ} {Γ : Assms} {e : Exp} {τ : Typ}
                (D : n ； Γ ⊢ e ↦ τ) (υ : ⌊ τ ⌋) : Set where
  field
    γ     : ⌊ Γ ⌋
    σ     : ⌊ e ⌋
    valid : n ； γ .↓ ⊢ σ .↓ ↦ υ .↓
open SynSlice public

private
-- Precision polymorphic in υ
  _⊑syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂} →
             SynSlice D υ₁ → SynSlice D υ₂ → Set
  _⊑syn_ s₁ s₂ =
      s₁ .σ ⊑ₛ s₂ .σ
    ∧ s₁ .γ ⊑ₛ s₂ .γ

  _≈syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂} →
              SynSlice D υ₁ → SynSlice D υ₂ → Set
  _≈syn_ s₁ s₂ =
      s₁ .σ ≈ₛ s₂ .σ
    ∧ s₁ .γ ≈ₛ s₂ .γ

  _≈syn?_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → (s₁ s₂ : SynSlice D υ) → Relation.Nullary.Dec (s₁ ≈syn s₂)
  s₁ ≈syn? s₂ with s₁ .σ ≈ₛ? s₂ .σ | s₁ .γ ≈ₛ? s₂ .γ
  ...            | yes p          | yes q = yes (p , q)
  ...            | no ¬p          | _     = no λ where (p , _) → ¬p p
  ...            | _              | no ¬q = no λ where (_ , q) → ¬q q

  _⊑syn?_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → (s₁ s₂ : SynSlice D υ) → Relation.Nullary.Dec (s₁ ⊑syn s₂)
  s₁ ⊑syn? s₂ with s₁ .σ ⊑ₛ? s₂ .σ | s₁ .γ ⊑ₛ? s₂ .γ
  ...            | yes p          | yes q = yes (p , q)
  ...            | no ¬p          | _     = no λ where (p , _) → ¬p p
  ...            | _              | no ¬q = no λ where (_ , q) → ¬q q

  ⊑syn-isDecPartialOrder : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
                              IsDecPartialOrder (_≈syn_ {D = D} {υ₁ = υ} {υ₂ = υ}) _⊑syn_
  ⊑syn-isDecPartialOrder {Γ = Γ} {e = e} = record
                           { isPartialOrder = record
                                              { isPreorder = isPreorder
                                              ; antisym = λ (p₁ , q₁) (p₂ , q₂) → ⊑.antisym {Exp} p₁ p₂ , ⊑.antisym {Assms} q₁ q₂
                                              }
                           ; _≟_  = _≈syn?_
                           ; _≤?_ = _⊑syn?_ 
                           }
    where isPreorder = record
                       { isEquivalence = record
                           { refl  = λ {_} → refl , refl
                           ; sym   = λ where (refl , refl) → refl , refl
                           ; trans = λ where (refl , refl) (refl , refl) → refl , refl
                           }
                       ; reflexive  = λ where (refl , refl) → ⊑.refl {Exp} , ⊑.refl {Assms}
                       ; trans = λ (p₁ , q₁) (p₂ , q₂) → ⊑.trans {Exp} p₁ p₂ , ⊑.trans {Assms} q₁ q₂
                       }

instance
  synSlice-precision : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
                         HasPrecision (SynSlice D υ)
  synSlice-precision = record
    { _≈_               = _≈syn_
    ; _⊑_               = _⊑syn_
    ; isDecPartialOrder = ⊑syn-isDecPartialOrder
    }

⊥-syn : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} → SynSlice D ⊥ₛ
⊥-syn = record { γ = ⊥ₛ ; σ = ⊥ₛ ; valid = ↦□ }

⊤-syn : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) → SynSlice D ⊤ₛ
⊤-syn D = record { γ = ⊤ₛ ; σ = ⊤ₛ ; valid = D }

-- Minimality
IsMinimal : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} → SynSlice D υ → Set
IsMinimal {D = D} {υ = υ} s = ∀ (s' : SynSlice D υ) → s' ⊑syn s → s ⊑syn s'

MinSynSlice : ∀ {n Γ e τ} → (D : n ； Γ ⊢ e ↦ τ) → ⌊ τ ⌋ → Set
MinSynSlice D υ = Σ[ s ∈ SynSlice D υ ] IsMinimal s

-- Join closure (of minimal syn slices)
-- Without IsMinimal, ⊔syn-valid is false: ↦□ allows arbitrary assumptions γ,
-- so joining pollutes the assumptions, i.e.
module ⊔-closure-counterexample where
  D' : 0 ； * ∷ [] ⊢ ⟨ 0 ⟩ ↦ *
  D' = ↦Var refl

  υ' : ⌊ Typ.* ⌋
  υ' = ⊥ₛ

  s₁' : SynSlice D' υ'
  s₁' = record { γ = ⊤ₛ ; σ = ⊥ₛ ; valid = ↦□ }

  s₂' : SynSlice D' υ'
  s₂' = record { γ = ⊥ₛ ; σ = ⊤ₛ ; valid = ↦Var refl }

  ¬⊔-valid : ¬ (0 ； (s₁' .γ ⊔ₛ s₂' .γ) .↓ ⊢ (s₁' .σ ⊔ₛ s₂' .σ) .↓ ↦ υ' .↓)
  ¬⊔-valid (↦Var ())

private
  -- □ is left identity for Exp join
  ⊔e-identityₗ : ∀ (e : Exp) → Exp.□ ⊔ e ≡ e
  ⊔e-identityₗ = ⊔t-zeroₗ-Exp
    where postulate ⊔t-zeroₗ-Exp : ∀ (e : Exp) → Exp.□ ⊔ e ≡ e
    -- Proof: by case on diag □ e. kind□ → refl; diff → refl (since □ ≟ □ = yes)
    -- Blocked by private diag in Core.Exp.Base; TODO: make public

  -- ⊥ₛ is left/right identity for Assms join (pointwise from ⊔t-zeroₗ/ᵣ)
  ⊔a-identityₗ : ∀ {Γ : Assms} (γ : Assms) → γ ⊑ Γ → □Assm (Data.List.length Γ) ⊔ γ ≡ γ
  ⊔a-identityₗ []      ⊑[]       = refl
  ⊔a-identityₗ (τ ∷ γ) (⊑∷ _ q) = cong₂ _∷_ ⊔t-zeroₗ (⊔a-identityₗ γ q)

  ⊔a-identityᵣ : ∀ {Γ : Assms} (γ : Assms) → γ ⊑ Γ → γ ⊔ □Assm (Data.List.length Γ) ≡ γ
  ⊔a-identityᵣ []      ⊑[]       = refl
  ⊔a-identityᵣ (τ ∷ γ) (⊑∷ _ q) = cong₂ _∷_ ⊔t-zeroᵣ (⊔a-identityᵣ γ q)

  postulate ⊔e-identityᵣ : ∀ (e : Exp) → e ⊔ Exp.□ ≡ e

  -- Type join idempotency
  ⊔t-idem : ∀ (τ : Typ) → τ ⊔ τ ≡ τ
  ⊔t-idem τ with diag τ τ in eq
  ... | kind□ = refl
  ... | kind* = refl
  ... | kindVar = refl
  ... | kind+ {τ₁} {τ₂} = cong₂ _+_ (⊔t-idem τ₁) (⊔t-idem τ₂)
  ... | kind× {τ₁} {τ₂} = cong₂ _×_ (⊔t-idem τ₁) (⊔t-idem τ₂)
  ... | kind⇒ {τ₁} {τ₂} = cong₂ _⇒_ (⊔t-idem τ₁) (⊔t-idem τ₂)
  ... | kind∀ {τ'} = cong ∀· (⊔t-idem τ')
  ... | diff = ⊥-elim (shallow-disequality eq)

  -- Lookup distributes over assumption join
  at-⊔ : ∀ {Γ₁ Γ₂ : Assms} {k τ₁ τ₂}
        → Γ₁ at k ≡ just τ₁ → Γ₂ at k ≡ just τ₂
        → (Γ₁ ⊔ Γ₂) at k ≡ just (τ₁ ⊔ τ₂)
  at-⊔ {_ ∷ Γ₁} {_ ∷ Γ₂} {zero}  refl refl = refl
  at-⊔ {_ ∷ Γ₁} {_ ∷ Γ₂} {suc k} p    q    = at-⊔ {Γ₁} {Γ₂} {k} p q

  -- View: classify a SynSlice as bot (↦□) or non-bot
  -- TODO: pointless view, just use decidability
  data SynView {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} (s : SynSlice D υ) : Set where
    is-⊥ : υ .↓ ≡ Typ.□ → s .σ .↓ ≡ Exp.□ → SynView s
    is-ne : s .σ .↓ ≢ Exp.□ → SynView s

  synView : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
          → (s : SynSlice D υ) → SynView s
  synView s with HasDecEq._≟_ exp-decEq (s .σ .↓) Exp.□
  ... | no  ¬eq  = is-ne ¬eq
  ... | yes σ≡□ with s .valid
  ...   | ↦□ = is-⊥ refl σ≡□

  -- From minimality + ↦□ have γ .↓ ≡ □Assm (length Γ)
  min-γ≡⊥ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
           → (s : SynSlice D υ) → IsMinimal s
           → υ .↓ ≡ Typ.□
           → s .γ .↓ ≡ □Assm (Data.List.length Γ)
  min-γ≡⊥ {D = D} {υ = υ} s m refl =
    let bot : SynSlice D υ
        bot = record { γ = ⊥ₛ ; σ = ⊥ₛ ; valid = ↦□ }
    in ⊑.antisym {Assms}
         (proj₂ (m bot (⊑ₛLat.⊥ₛ-min (s .σ) , ⊑ₛLat.⊥ₛ-min (s .γ))))
         (⊑ₛLat.⊥ₛ-min (s .γ))

  -- Transport ↦ (τ ⊔ τ) to ↦ τ using join idempotency
  -- TODO use inline.
  idem-fix : ∀ {n Γ e τ} → n ； Γ ⊢ e ↦ (τ ⊔ τ) → n ； Γ ⊢ e ↦ τ
  idem-fix {τ = τ} v rewrite ⊔t-idem τ = v

  ⊔syn-valid : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂}
               → (s₁ : SynSlice D υ₁) → (s₂ : SynSlice D υ₂)
               → IsMinimal s₁ → IsMinimal s₂
               → n ； (SynSlice.γ s₁ ⊔ₛ SynSlice.γ s₂) .↓
                   ⊢ (SynSlice.σ s₁ ⊔ₛ SynSlice.σ s₂) .↓ ↦ (υ₁ ⊔ₛ υ₂) .↓
  -- Helper: reduce ⊥ₛ ⊔ₛ x to x (assumptions + expressions)
  ⊔-reduce-left : ∀ {n} {Γ : Assms} {e : Exp} {τ-typ : Typ}
    → (γ₁ γ₂ : ⌊ Γ ⌋) (σ₁ σ₂ : ⌊ e ⌋)
    → (v₂ : n ； γ₂ .↓ ⊢ σ₂ .↓ ↦ τ-typ)
    → γ₁ .↓ ≡ □Assm (Data.List.length Γ) → σ₁ .↓ ≡ Exp.□
    → n ； (γ₁ ⊔ₛ γ₂) .↓ ⊢ (σ₁ ⊔ₛ σ₂) .↓ ↦ τ-typ
  ⊔-reduce-left {Γ = Γ} _ γ₂ _ σ₂ v₂ refl refl
    rewrite ⊔a-identityₗ (γ₂ .↓) (γ₂ .proof)
    | ⊔e-identityₗ (σ₂ .↓)
    = v₂

  ⊔-reduce-right : ∀ {n} {Γ : Assms} {e : Exp} {τ-typ : Typ}
    → (γ₁ γ₂ : ⌊ Γ ⌋) (σ₁ σ₂ : ⌊ e ⌋)
    → (v₁ : n ； γ₁ .↓ ⊢ σ₁ .↓ ↦ τ-typ)
    → γ₂ .↓ ≡ □Assm (Data.List.length Γ) → σ₂ .↓ ≡ Exp.□
    → n ； (γ₁ ⊔ₛ γ₂) .↓ ⊢ (σ₁ ⊔ₛ σ₂) .↓ ↦ τ-typ
  ⊔-reduce-right {Γ = Γ} γ₁ _ σ₁ _ v₁ refl refl
    rewrite ⊔a-identityᵣ (γ₁ .↓) (γ₁ .proof)
    | ⊔e-identityᵣ (σ₁ .↓)
    = v₁

  ⊔syn-valid {υ₁ = υ₁} {υ₂ = υ₂} s₁ s₂ m₁ m₂ with synView s₁ | synView s₂
  -- s₁ is ⊥: υ₁.↓ = □, so (υ₁ ⊔ₛ υ₂).↓ = □ ⊔ υ₂.↓ = υ₂.↓
  ... | is-⊥ υ≡ σ≡ | _ rewrite υ≡ | ⊔t-zeroₗ {υ₂ .↓} =
    ⊔-reduce-left (s₁ .γ) (s₂ .γ) (s₁ .σ) (s₂ .σ) (s₂ .valid)
      (min-γ≡⊥ s₁ m₁ υ≡) σ≡
  -- s₂ is ⊥: υ₂.↓ = □, so (υ₁ ⊔ₛ υ₂).↓ = υ₁.↓ ⊔ □ = υ₁.↓
  ... | is-ne _ | is-⊥ υ≡ σ≡ rewrite υ≡ | ⊔t-zeroᵣ {υ₁ .↓} =
    ⊔-reduce-right (s₁ .γ) (s₂ .γ) (s₁ .σ) (s₂ .σ) (s₁ .valid)
      (min-γ≡⊥ s₂ m₂ υ≡) σ≡
  -- Both non-⊥: generalised IH produces υ₁.↓ ⊔ υ₂.↓ directly
  ... | is-ne ne₁ | is-ne ne₂ = ⊔syn-valid-ne _ s₁ s₂ m₁ m₂ ne₁ ne₂
    where
    -- Non-□ slice of atom must equal the atom
    ne-⊑*→≡ : ∀ {σ : Exp} → σ ⊑ Exp.* → σ ≢ Exp.□ → σ ≡ Exp.*
    ne-⊑*→≡ ⊑□ ne = ⊥-elim (ne refl)
    ne-⊑*→≡ ⊑* _  = refl

    ne-⊑Var→≡ : ∀ {σ : Exp} {k} → σ ⊑ ⟨ k ⟩ → σ ≢ Exp.□ → σ ≡ ⟨ k ⟩
    ne-⊑Var→≡ ⊑□   ne = ⊥-elim (ne refl)
    ne-⊑Var→≡ ⊑Var _  = refl

    -- Case helpers: take all components + equality proofs, match on refl + valid
    ⊔-case-* : ∀ {n Γ} {υ₁ υ₂ : ⌊ Typ.* ⌋}
      → (γ₁ γ₂ : ⌊ Γ ⌋) (σ₁ σ₂ : ⌊ Exp.* ⌋)
      → n ； γ₁ .↓ ⊢ σ₁ .↓ ↦ υ₁ .↓
      → n ； γ₂ .↓ ⊢ σ₂ .↓ ↦ υ₂ .↓
      → σ₁ .↓ ≡ Exp.* → σ₂ .↓ ≡ Exp.*
      → n ； (γ₁ ⊔ₛ γ₂) .↓ ⊢ (σ₁ ⊔ₛ σ₂) .↓ ↦ (υ₁ .↓ ⊔ υ₂ .↓)
    ⊔-case-* _ _ _ _ v₁ v₂ refl refl with v₁ | v₂
    ... | ↦* | ↦* = ↦*

    ⊔-case-Var : ∀ {n Γ τ-typ k} {υ₁ υ₂ : ⌊ τ-typ ⌋}
      → (γ₁ γ₂ : ⌊ Γ ⌋) (σ₁ σ₂ : ⌊ ⟨ k ⟩ ⌋)
      → n ； γ₁ .↓ ⊢ σ₁ .↓ ↦ υ₁ .↓
      → n ； γ₂ .↓ ⊢ σ₂ .↓ ↦ υ₂ .↓
      → σ₁ .↓ ≡ ⟨ k ⟩ → σ₂ .↓ ≡ ⟨ k ⟩
      → n ； (γ₁ ⊔ₛ γ₂) .↓ ⊢ (σ₁ ⊔ₛ σ₂) .↓ ↦ (υ₁ .↓ ⊔ υ₂ .↓)
    ⊔-case-Var γ₁ γ₂ _ _ v₁ v₂ refl refl with v₁ | v₂
    ... | ↦Var p₁ | ↦Var p₂ = ↦Var (at-⊔ {γ₁ .↓} {γ₂ .↓} p₁ p₂)

    -- ↦∘: inversion helpers
    ne-⊑∘→≡ : ∀ {σ : Exp} {e₁ e₂} → σ ⊑ (e₁ ∘ e₂) → σ ≢ Exp.□
            → ∃[ σ₁ ] ∃[ σ₂ ] σ ≡ (σ₁ ∘ σ₂)
    ne-⊑∘→≡ ⊑□          ne = ⊥-elim (ne refl)
    ne-⊑∘→≡ (⊑∘ _ _)    _  = _ , _ , refl


    postulate
      ⊔ana-closure : ∀ {n Γ e dom₁ dom₂} {γ₁ γ₂ : ⌊ Γ ⌋} {σ₁ σ₂ : Exp}
        → n ； γ₁ .↓ ⊢ σ₁ ↤ dom₁ → n ； γ₂ .↓ ⊢ σ₂ ↤ dom₂
        → σ₁ ⊑ e → σ₂ ⊑ e
        → n ； γ₁ .↓ ⊔ γ₂ .↓ ⊢ σ₁ ⊔ σ₂ ↤ dom₁ ⊔ dom₂

      ⊔-arrow-distrib : ∀ {α₁ α₂ dom₁ dom₂ cod₁ cod₂}
        → α₁ ⊔ Typ.□ ⇒ Typ.□ ≡ dom₁ ⇒ cod₁
        → α₂ ⊔ Typ.□ ⇒ Typ.□ ≡ dom₂ ⇒ cod₂
        → (α₁ ⊔ α₂) ⊔ Typ.□ ⇒ Typ.□ ≡ (dom₁ ⊔ dom₂) ⇒ (cod₁ ⊔ cod₂)

    -- ne-⊑ inversion for remaining expression forms
    ne-⊑λ:→≡ : ∀ {σ : Exp} {τ₁ e} → σ ⊑ (λ: τ₁ ⇒ e) → σ ≢ Exp.□ → ∃[ τ₁' ] ∃[ e' ] σ ≡ (λ: τ₁' ⇒ e')
    ne-⊑λ:→≡ ⊑□ ne = ⊥-elim (ne refl)
    ne-⊑λ:→≡ (⊑λ _ _) _ = _ , _ , refl

    ne-⊑def→≡ : ∀ {σ : Exp} {e₁ e₂} → σ ⊑ (def e₁ ⊢ e₂) → σ ≢ Exp.□ → ∃[ e₁' ] ∃[ e₂' ] σ ≡ (def e₁' ⊢ e₂')
    ne-⊑def→≡ ⊑□ ne = ⊥-elim (ne refl)
    ne-⊑def→≡ (⊑def _ _) _ = _ , _ , refl

    ne-⊑Λ→≡ : ∀ {σ : Exp} {e} → σ ⊑ Λ e → σ ≢ Exp.□ → ∃[ e' ] σ ≡ Λ e'
    ne-⊑Λ→≡ ⊑□ ne = ⊥-elim (ne refl)
    ne-⊑Λ→≡ (⊑Λ _) _ = _ , refl

    ne-⊑<>→≡ : ∀ {σ : Exp} {e τ} → σ ⊑ (e < τ >) → σ ≢ Exp.□ → ∃[ e' ] ∃[ τ' ] σ ≡ (e' < τ' >)
    ne-⊑<>→≡ ⊑□ ne = ⊥-elim (ne refl)
    ne-⊑<>→≡ (⊑<> _ _) _ = _ , _ , refl

    ne-⊑&→≡ : ∀ {σ : Exp} {e₁ e₂} → σ ⊑ (e₁ & e₂) → σ ≢ Exp.□ → ∃[ e₁' ] ∃[ e₂' ] σ ≡ (e₁' & e₂')
    ne-⊑&→≡ ⊑□ ne = ⊥-elim (ne refl)
    ne-⊑&→≡ (⊑& _ _) _ = _ , _ , refl

    ne-⊑π₁→≡ : ∀ {σ : Exp} {e} → σ ⊑ π₁ e → σ ≢ Exp.□ → ∃[ e' ] σ ≡ π₁ e'
    ne-⊑π₁→≡ ⊑□ ne = ⊥-elim (ne refl)
    ne-⊑π₁→≡ (⊑π₁ _) _ = _ , refl

    ne-⊑π₂→≡ : ∀ {σ : Exp} {e} → σ ⊑ π₂ e → σ ≢ Exp.□ → ∃[ e' ] σ ≡ π₂ e'
    ne-⊑π₂→≡ ⊑□ ne = ⊥-elim (ne refl)
    ne-⊑π₂→≡ (⊑π₂ _) _ = _ , refl

    ne-⊑case→≡ : ∀ {σ : Exp} {e e₁ e₂} → σ ⊑ (case e of e₁ · e₂) → σ ≢ Exp.□
               → ∃[ e' ] ∃[ e₁' ] ∃[ e₂' ] σ ≡ (case e' of e₁' · e₂')
    ne-⊑case→≡ ⊑□ ne = ⊥-elim (ne refl)
    ne-⊑case→≡ (⊑case _ _ _) _ = _ , _ , _ , refl

    -- Postulated inner cases for remaining compound constructors
    postulate
      ⊔-case-λ:-inner : ∀ {n Γ e τ₁ τ₂}
        → (wf : n ⊢wf τ₁) → (D' : n ； (τ₁ ∷ Γ) ⊢ e ↦ τ₂)
        → (γ₁ γ₂ : ⌊ Γ ⌋)
        → ∀ {τ₁₁ σ₁' τ₂₁ τ₁₂ σ₂' τ₂₂}
        → n ⊢wf τ₁₁ → n ； (τ₁₁ ∷ γ₁ .↓) ⊢ σ₁' ↦ τ₂₁
        → n ⊢wf τ₁₂ → n ； (τ₁₂ ∷ γ₂ .↓) ⊢ σ₂' ↦ τ₂₂
        → n ； γ₁ .↓ ⊔ γ₂ .↓ ⊢ (λ: τ₁₁ ⇒ σ₁') ⊔ (λ: τ₁₂ ⇒ σ₂') ↦ (τ₁₁ ⇒ τ₂₁) ⊔ (τ₁₂ ⇒ τ₂₂)

      ⊔-case-def-inner : ∀ {n Γ e' e τ' τ}
        → (D₁ : n ； Γ ⊢ e' ↦ τ') → (D₂ : n ； (τ' ∷ Γ) ⊢ e ↦ τ)
        → (γ₁ γ₂ : ⌊ Γ ⌋)
        → ∀ {σ₁' σ₁ τ₁' υ₁-τ σ₂' σ₂ τ₂' υ₂-τ}
        → n ； γ₁ .↓ ⊢ σ₁' ↦ τ₁' → n ； (τ₁' ∷ γ₁ .↓) ⊢ σ₁ ↦ υ₁-τ
        → n ； γ₂ .↓ ⊢ σ₂' ↦ τ₂' → n ； (τ₂' ∷ γ₂ .↓) ⊢ σ₂ ↦ υ₂-τ
        → n ； γ₁ .↓ ⊔ γ₂ .↓ ⊢ (def σ₁' ⊢ σ₁) ⊔ (def σ₂' ⊢ σ₂) ↦ (υ₁-τ ⊔ υ₂-τ)

      ⊔-case-Λ-inner : ∀ {n Γ e τ}
        → (D' : suc n ； shiftΓ (suc zero) Γ ⊢ e ↦ τ)
        → (γ₁ γ₂ : ⌊ Γ ⌋)
        → ∀ {σ₁ τ₁ σ₂ τ₂}
        → suc n ； shiftΓ (suc zero) (γ₁ .↓) ⊢ σ₁ ↦ τ₁
        → suc n ； shiftΓ (suc zero) (γ₂ .↓) ⊢ σ₂ ↦ τ₂
        → n ； γ₁ .↓ ⊔ γ₂ .↓ ⊢ Λ σ₁ ⊔ Λ σ₂ ↦ (∀· τ₁) ⊔ (∀· τ₂)

      ⊔-case-<>-inner : ∀ {n Γ e τ-e τ' σ-ty t₁ t₂}
        → (D' : n ； Γ ⊢ e ↦ τ-e)
        → (eq : τ-e ⊔ ∀· Typ.□ ≡ ∀· τ') → (wf : n ⊢wf σ-ty)
        → (γ₁ γ₂ : ⌊ Γ ⌋)
        → ∀ {σ₁-e σ₁-ty σ₂-e σ₂-ty}
        → n ； γ₁ .↓ ⊢ (σ₁-e < σ₁-ty >) ↦ t₁
        → n ； γ₂ .↓ ⊢ (σ₂-e < σ₂-ty >) ↦ t₂
        → n ； γ₁ .↓ ⊔ γ₂ .↓ ⊢ (σ₁-e < σ₁-ty >) ⊔ (σ₂-e < σ₂-ty >) ↦ (t₁ ⊔ t₂)

      ⊔-case-&-inner : ∀ {n Γ e₁ e₂ τ₁ τ₂}
        → (D₁ : n ； Γ ⊢ e₁ ↦ τ₁) → (D₂ : n ； Γ ⊢ e₂ ↦ τ₂)
        → (γ₁ γ₂ : ⌊ Γ ⌋)
        → ∀ {σ₁₁ σ₁₂ α₁ β₁ σ₂₁ σ₂₂ α₂ β₂}
        → n ； γ₁ .↓ ⊢ σ₁₁ ↦ α₁ → n ； γ₁ .↓ ⊢ σ₁₂ ↦ β₁
        → n ； γ₂ .↓ ⊢ σ₂₁ ↦ α₂ → n ； γ₂ .↓ ⊢ σ₂₂ ↦ β₂
        → n ； γ₁ .↓ ⊔ γ₂ .↓ ⊢ (σ₁₁ & σ₁₂) ⊔ (σ₂₁ & σ₂₂) ↦ (α₁ × β₁) ⊔ (α₂ × β₂)

      ⊔-case-π₁-inner : ∀ {n Γ e τ-e τ₁ τ₂}
        → (D' : n ； Γ ⊢ e ↦ τ-e) → (eq : τ-e ⊔ Typ.□ × Typ.□ ≡ τ₁ × τ₂)
        → (γ₁ γ₂ : ⌊ Γ ⌋)
        → ∀ {σ₁ α₁ dom₁ cod₁ σ₂ α₂ dom₂ cod₂}
        → n ； γ₁ .↓ ⊢ σ₁ ↦ α₁ → α₁ ⊔ Typ.□ × Typ.□ ≡ dom₁ × cod₁
        → n ； γ₂ .↓ ⊢ σ₂ ↦ α₂ → α₂ ⊔ Typ.□ × Typ.□ ≡ dom₂ × cod₂
        → n ； γ₁ .↓ ⊔ γ₂ .↓ ⊢ π₁ σ₁ ⊔ π₁ σ₂ ↦ (dom₁ ⊔ dom₂)

      ⊔-case-π₂-inner : ∀ {n Γ e τ-e τ₁ τ₂}
        → (D' : n ； Γ ⊢ e ↦ τ-e) → (eq : τ-e ⊔ Typ.□ × Typ.□ ≡ τ₁ × τ₂)
        → (γ₁ γ₂ : ⌊ Γ ⌋)
        → ∀ {σ₁ α₁ dom₁ cod₁ σ₂ α₂ dom₂ cod₂}
        → n ； γ₁ .↓ ⊢ σ₁ ↦ α₁ → α₁ ⊔ Typ.□ × Typ.□ ≡ dom₁ × cod₁
        → n ； γ₂ .↓ ⊢ σ₂ ↦ α₂ → α₂ ⊔ Typ.□ × Typ.□ ≡ dom₂ × cod₂
        → n ； γ₁ .↓ ⊔ γ₂ .↓ ⊢ π₂ σ₁ ⊔ π₂ σ₂ ↦ (cod₁ ⊔ cod₂)

      ⊔-case-case-inner : ∀ {n Γ e e₁ e₂ τ-e τ₁ τ₂ τ₁' τ₂' t₁ t₂}
        → (D' : n ； Γ ⊢ e ↦ τ-e) → (eq : τ-e ⊔ Typ.□ + Typ.□ ≡ τ₁ + τ₂)
        → (D₁ : n ； (τ₁ ∷ Γ) ⊢ e₁ ↦ τ₁') → (D₂ : n ； (τ₂ ∷ Γ) ⊢ e₂ ↦ τ₂')
        → (con : τ₁' ~ τ₂')
        → (γ₁ γ₂ : ⌊ Γ ⌋)
        → ∀ {σ σ₁ σ₂ σ' σ₁' σ₂'}
        → n ； γ₁ .↓ ⊢ (case σ of σ₁ · σ₂) ↦ t₁
        → n ； γ₂ .↓ ⊢ (case σ' of σ₁' · σ₂') ↦ t₂
        → n ； γ₁ .↓ ⊔ γ₂ .↓ ⊢ (case σ of σ₁ · σ₂) ⊔ (case σ' of σ₁' · σ₂') ↦ (t₁ ⊔ t₂)

    -- ⊔-case wrappers that do the ne-⊑ inversion + valid case split
    ⊔-case-gen : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) {υ₁ υ₂ : ⌊ τ ⌋}
      → (γ₁ γ₂ : ⌊ Γ ⌋) (σ₁ σ₂ : ⌊ e ⌋)
      → n ； γ₁ .↓ ⊢ σ₁ .↓ ↦ υ₁ .↓ → n ； γ₂ .↓ ⊢ σ₂ .↓ ↦ υ₂ .↓
      → σ₁ .↓ ≢ Exp.□ → σ₂ .↓ ≢ Exp.□
      → n ； (γ₁ ⊔ₛ γ₂) .↓ ⊢ (σ₁ ⊔ₛ σ₂) .↓ ↦ (υ₁ .↓ ⊔ υ₂ .↓)
    -- λ:
    ⊔-case-gen (↦λ: wf D') γ₁ γ₂ σ₁ σ₂ v₁ v₂ ne₁ ne₂
      with ne-⊑λ:→≡ (σ₁ .proof) ne₁ | ne-⊑λ:→≡ (σ₂ .proof) ne₂
    ... | _ , _ , refl | _ , _ , refl with v₁ | v₂
    ... | ↦λ: wf₁ d₁ | ↦λ: wf₂ d₂ = ⊔-case-λ:-inner wf D' γ₁ γ₂ wf₁ d₁ wf₂ d₂
    -- def
    ⊔-case-gen (↦def D₁ D₂) γ₁ γ₂ σ₁ σ₂ v₁ v₂ ne₁ ne₂
      with ne-⊑def→≡ (σ₁ .proof) ne₁ | ne-⊑def→≡ (σ₂ .proof) ne₂
    ... | _ , _ , refl | _ , _ , refl with v₁ | v₂
    ... | ↦def d₁' d₁ | ↦def d₂' d₂ = ⊔-case-def-inner D₁ D₂ γ₁ γ₂ d₁' d₁ d₂' d₂
    -- Λ
    ⊔-case-gen (↦Λ D') γ₁ γ₂ σ₁ σ₂ v₁ v₂ ne₁ ne₂
      with ne-⊑Λ→≡ (σ₁ .proof) ne₁ | ne-⊑Λ→≡ (σ₂ .proof) ne₂
    ... | _ , refl | _ , refl with v₁ | v₂
    ... | ↦Λ d₁ | ↦Λ d₂ = ⊔-case-Λ-inner D' γ₁ γ₂ d₁ d₂
    -- <>
    ⊔-case-gen (↦<> D' eq wf) γ₁ γ₂ σ₁ σ₂ v₁ v₂ ne₁ ne₂
      with ne-⊑<>→≡ (σ₁ .proof) ne₁ | ne-⊑<>→≡ (σ₂ .proof) ne₂
    ... | _ , _ , refl | _ , _ , refl = ⊔-case-<>-inner D' eq wf γ₁ γ₂ v₁ v₂
    -- &
    ⊔-case-gen (↦& D₁ D₂) γ₁ γ₂ σ₁ σ₂ v₁ v₂ ne₁ ne₂
      with ne-⊑&→≡ (σ₁ .proof) ne₁ | ne-⊑&→≡ (σ₂ .proof) ne₂
    ... | _ , _ , refl | _ , _ , refl with v₁ | v₂
    ... | ↦& d₁₁ d₁₂ | ↦& d₂₁ d₂₂ = ⊔-case-&-inner D₁ D₂ γ₁ γ₂ d₁₁ d₁₂ d₂₁ d₂₂
    -- π₁
    ⊔-case-gen (↦π₁ D' eq) γ₁ γ₂ σ₁ σ₂ v₁ v₂ ne₁ ne₂
      with ne-⊑π₁→≡ (σ₁ .proof) ne₁ | ne-⊑π₁→≡ (σ₂ .proof) ne₂
    ... | _ , refl | _ , refl with v₁ | v₂
    ... | ↦π₁ d₁ eq₁ | ↦π₁ d₂ eq₂ = ⊔-case-π₁-inner D' eq γ₁ γ₂ d₁ eq₁ d₂ eq₂
    -- π₂
    ⊔-case-gen (↦π₂ D' eq) γ₁ γ₂ σ₁ σ₂ v₁ v₂ ne₁ ne₂
      with ne-⊑π₂→≡ (σ₁ .proof) ne₁ | ne-⊑π₂→≡ (σ₂ .proof) ne₂
    ... | _ , refl | _ , refl with v₁ | v₂
    ... | ↦π₂ d₁ eq₁ | ↦π₂ d₂ eq₂ = ⊔-case-π₂-inner D' eq γ₁ γ₂ d₁ eq₁ d₂ eq₂
    -- case
    ⊔-case-gen (↦case D' eq D₁ D₂ con) γ₁ γ₂ σ₁ σ₂ v₁ v₂ ne₁ ne₂
      with ne-⊑case→≡ (σ₁ .proof) ne₁ | ne-⊑case→≡ (σ₂ .proof) ne₂
    ... | _ , _ , _ , refl | _ , _ , _ , refl =
      ⊔-case-case-inner D' eq D₁ D₂ con γ₁ γ₂ v₁ v₂
    -- ↦□: impossible since σ ⊑ □ and σ ≢ □
    ⊔-case-gen ↦□ γ₁ γ₂ σ₁ σ₂ v₁ v₂ ne₁ ne₂ =
      ⊥-elim (ne₁ (⊑.antisym {Exp} (σ₁ .proof) ⊑□))
    -- ↦*, ↦Var, ↦∘: delegate to existing case helpers
    ⊔-case-gen ↦* {υ₁} {υ₂} γ₁ γ₂ σ₁ σ₂ v₁ v₂ ne₁ ne₂ =
      ⊔-case-* {υ₁ = υ₁} {υ₂ = υ₂} γ₁ γ₂ σ₁ σ₂ v₁ v₂ (ne-⊑*→≡ (σ₁ .proof) ne₁) (ne-⊑*→≡ (σ₂ .proof) ne₂)
    ⊔-case-gen (↦Var _) {υ₁} {υ₂} γ₁ γ₂ σ₁ σ₂ v₁ v₂ ne₁ ne₂ =
      ⊔-case-Var {υ₁ = υ₁} {υ₂ = υ₂} γ₁ γ₂ σ₁ σ₂ v₁ v₂ (ne-⊑Var→≡ (σ₁ .proof) ne₁) (ne-⊑Var→≡ (σ₂ .proof) ne₂)
    -- ↦∘ handled directly in ⊔syn-valid-ne; stub for coverage
    ⊔-case-gen (↦∘ _ _ _) {υ₁} {υ₂} γ₁ γ₂ σ₁ σ₂ v₁ v₂ ne₁ ne₂ =
      ⊔-case-∘-stub
      where postulate ⊔-case-∘-stub : _ ； (γ₁ ⊔ₛ γ₂) .↓ ⊢ (σ₁ ⊔ₛ σ₂) .↓ ↦ (υ₁ .↓ ⊔ υ₂ .↓)

    -- Generalised IH: different type slices, requires IsMinimal for □ sub-cases
    ⊔syn-valid-ne : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) {υ₁ υ₂ : ⌊ τ ⌋}
                   → (s₁ : SynSlice D υ₁) → (s₂ : SynSlice D υ₂)
                   → IsMinimal s₁ → IsMinimal s₂
                   → s₁ .σ .↓ ≢ Exp.□ → s₂ .σ .↓ ≢ Exp.□
                   → n ； (SynSlice.γ s₁ ⊔ₛ SynSlice.γ s₂) .↓
                       ⊢ (SynSlice.σ s₁ ⊔ₛ SynSlice.σ s₂) .↓ ↦ (υ₁ .↓ ⊔ υ₂ .↓)
    ⊔syn-valid-ne ↦□ s₁ _ _ _ ne₁ _ = ⊥-elim (ne₁ (⊑.antisym {Exp} (s₁ .σ .proof) ⊑□))
    ⊔syn-valid-ne ↦* {υ₁} {υ₂} s₁ s₂ _ _ ne₁ ne₂ =
      ⊔-case-* {υ₁ = υ₁} {υ₂ = υ₂} (s₁ .γ) (s₂ .γ) (s₁ .σ) (s₂ .σ) (s₁ .valid) (s₂ .valid)
        (ne-⊑*→≡ (s₁ .σ .proof) ne₁) (ne-⊑*→≡ (s₂ .σ .proof) ne₂)
    ⊔syn-valid-ne (↦Var _) {υ₁} {υ₂} s₁ s₂ _ _ ne₁ ne₂ =
      ⊔-case-Var {υ₁ = υ₁} {υ₂ = υ₂} (s₁ .γ) (s₂ .γ) (s₁ .σ) (s₂ .σ) (s₁ .valid) (s₂ .valid)
        (ne-⊑Var→≡ (s₁ .σ .proof) ne₁) (ne-⊑Var→≡ (s₂ .σ .proof) ne₂)
    -- ↦∘: proved using recursive IH + postulated sub-slice minimality
    ⊔syn-valid-ne (↦∘ D-fn eq D-arg) s₁ s₂ m₁ m₂ ne₁ ne₂
      with ne-⊑∘→≡ (s₁ .σ .proof) ne₁ | ne-⊑∘→≡ (s₂ .σ .proof) ne₂
    ... | _ , _ , refl | _ , _ , refl with s₁ .valid | s₂ .valid
    ... | ↦∘ {τ = α₁} v₁-fn eq₁ v₁-arg | ↦∘ {τ = α₂} v₂-fn eq₂ v₂-arg
      with s₁ .σ .proof | s₂ .σ .proof
    ...   | ⊑∘ σ₁fn⊑ σ₁arg⊑ | ⊑∘ σ₂fn⊑ σ₂arg⊑ =
      ↦∘ (⊔syn-valid {D = D-fn} fn-s₁ fn-s₂ min-fn₁ min-fn₂)
          (⊔-arrow-distrib {α₁ = α₁} {α₂ = α₂} eq₁ eq₂)
          (⊔ana-closure {γ₁ = s₁ .γ} {γ₂ = s₂ .γ} v₁-arg v₂-arg σ₁arg⊑ σ₂arg⊑)
      where α₁⊑τ = syn-precision (s₁ .γ .proof) σ₁fn⊑ D-fn v₁-fn
            α₂⊑τ = syn-precision (s₂ .γ .proof) σ₂fn⊑ D-fn v₂-fn
            fn-s₁ : SynSlice D-fn (↑ α₁⊑τ)
            fn-s₁ = record { γ = s₁ .γ ; σ = ↑ σ₁fn⊑ ; valid = v₁-fn }
            fn-s₂ : SynSlice D-fn (↑ α₂⊑τ)
            fn-s₂ = record { γ = s₂ .γ ; σ = ↑ σ₂fn⊑ ; valid = v₂-fn }
            -- Minimality of fn sub-slices: if s' ⊑ fn-sᵢ, build smaller
            -- outer slice via ana SGG, apply outer minimality, project fn component
            min-fn₁ : IsMinimal fn-s₁
            min-fn₁ s' (σ'⊑ , γ'⊑) with m₁ outer' (⊑∘ σ'⊑ (⊑.refl {Exp}) , γ'⊑)
              where outer' = record
                      { γ = s' .γ
                      ; σ = ↑ (⊑∘ (s' .σ .proof) σ₁arg⊑)
                      ; valid = ↦∘ (s' .valid) eq₁
                          (static-gradual-ana γ'⊑ (⊑.refl {Exp}) (⊑.refl {Typ}) v₁-arg)
                      }
            ... | ⊑∘ fn⊑ _ , γ⊑ = fn⊑ , γ⊑
            min-fn₂ : IsMinimal fn-s₂
            min-fn₂ s' (σ'⊑ , γ'⊑) with m₂ outer' (⊑∘ σ'⊑ (⊑.refl {Exp}) , γ'⊑)
              where outer' = record
                      { γ = s' .γ
                      ; σ = ↑ (⊑∘ (s' .σ .proof) σ₂arg⊑)
                      ; valid = ↦∘ (s' .valid) eq₂
                          (static-gradual-ana γ'⊑ (⊑.refl {Exp}) (⊑.refl {Typ}) v₂-arg)
                      }
            ... | ⊑∘ fn⊑ _ , γ⊑ = fn⊑ , γ⊑
    -- remaining compound types: delegate to ⊔-case-gen
    ⊔syn-valid-ne D {υ₁} {υ₂} s₁ s₂ _ _ ne₁ ne₂ =
      ⊔-case-gen D {υ₁} {υ₂} (s₁ .γ) (s₂ .γ) (s₁ .σ) (s₂ .σ) (s₁ .valid) (s₂ .valid) ne₁ ne₂

  _⊔syn_ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ} →
             (s₁ s₂ : SynSlice D υ) → IsMinimal s₁ → IsMinimal s₂ → SynSlice D υ
  (s₁ ⊔syn s₂) m₁ m₂ = record
    { γ = SynSlice.γ s₁ ⊔ₛ SynSlice.γ s₂
    ; σ = SynSlice.σ s₁ ⊔ₛ SynSlice.σ s₂
    ; valid = idem-fix (⊔syn-valid s₁ s₂ m₁ m₂)
    }

⊔syn-ub₁ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → (s₁ s₂ : SynSlice D υ) → (m₁ : IsMinimal s₁) → (m₂ : IsMinimal s₂)
            → s₁ ⊑syn ((s₁ ⊔syn s₂) m₁ m₂)
⊔syn-ub₁ s₁ s₂ _ _ = ⊑ₛLat.x⊑ₛx⊔ₛy (SynSlice.σ s₁) (SynSlice.σ s₂)
                     , ⊑ₛLat.x⊑ₛx⊔ₛy (SynSlice.γ s₁) (SynSlice.γ s₂)

⊔syn-ub₂ : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → (s₁ s₂ : SynSlice D υ) → (m₁ : IsMinimal s₁) → (m₂ : IsMinimal s₂)
            → s₂ ⊑syn ((s₁ ⊔syn s₂) m₁ m₂)
⊔syn-ub₂ s₁ s₂ _ _ = ⊑ₛLat.y⊑ₛx⊔ₛy (SynSlice.σ s₁) (SynSlice.σ s₂)
                     , ⊑ₛLat.y⊑ₛx⊔ₛy (SynSlice.γ s₁) (SynSlice.γ s₂)

⊔syn-lub : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ}
            → {s : SynSlice D υ} (s₁ s₂ : SynSlice D υ)
            → (m₁ : IsMinimal s₁) → (m₂ : IsMinimal s₂)
            → s₁ ⊑syn s → s₂ ⊑syn s
            → ((s₁ ⊔syn s₂) m₁ m₂) ⊑syn s
⊔syn-lub {Γ = Γ} {e = e} {s = s} s₁ s₂ _ _ (p₁ , q₁) (p₂ , q₂) =
    ⊑ₛLat.⊔ₛ-least {A = Exp} {a = e}
      {x = SynSlice.σ s₁} {y = SynSlice.σ s₂} {z = SynSlice.σ s}
      p₁ p₂
  , ⊑ₛLat.⊔ₛ-least {A = Assms} {a = Γ}
      {x = SynSlice.γ s₁} {y = SynSlice.γ s₂} {z = SynSlice.γ s}
      q₁ q₂

-- Every derivation and type slice has a minimal SynSlice
-- TODO: Prove via classical methods using the fact that a bottom element exists
postulate
  minExists : ∀ {n Γ e τ} (D : n ； Γ ⊢ e ↦ τ) υ
             → ∃[ m ] IsMinimal {D = D} {υ = υ} m

-- Monotonicity: more precise type slice → more precise minimal slice
postulate
  mono : ∀ {n Γ e τ} {D : n ； Γ ⊢ e ↦ τ} {υ₁ υ₂ : ⌊ τ ⌋}
         → υ₁ ⊑ₛ υ₂
         → (m₂ : SynSlice D υ₂) → IsMinimal m₂
         → Σ[ m₁ ∈ SynSlice D υ₁ ] IsMinimal m₁ ∧ m₁ ⊑syn m₂
