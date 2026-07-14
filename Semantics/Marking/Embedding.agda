-- Canonical, mark-free embeddings of well-typed terms and classified
-- contexts into the marking calculus.  These lemmas are the reuse boundary
-- for marked slicing: every unmarked slice proof can be decorated without
-- repeating its static or minimality argument.
module Semantics.Marking.Embedding where

open import Data.Nat hiding (_+_; _⊔_)
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Core
import Core.MExp as M
import Core.MCtx as K
open import Semantics.Statics
open import Semantics.Marking.Judgment
open import Semantics.Marking.CtxMarking
open import Semantics.Marking.Erasure

embed : Exp → M.MExp
embed □ = M.□
embed * = M.*
embed ⟨ k ⟩ = M.⟨ k ⟩
embed (λ: τ ⇒ e) = M.λ: τ ⇒ embed e
embed (λ⇒ e) = M.λ⇒ embed e
embed (e₁ ∘ e₂) = embed e₁ M.∘ embed e₂
embed (e < τ >) = embed e M.< τ >
embed (e₁ & e₂) = embed e₁ M.& embed e₂
embed (ι₁ e) = M.ι₁ (embed e)
embed (ι₂ e) = M.ι₂ (embed e)
embed (case e₀ of e₁ · e₂) = M.case embed e₀ of embed e₁ · embed e₂
embed (π₁ e) = M.π₁ (embed e)
embed (π₂ e) = M.π₂ (embed e)
embed (Λ e) = M.Λ (embed e)
embed (def e₁ ⊢ e₂) = M.def embed e₁ ⊢ embed e₂

erase-embed : ∀ e → erase (embed e) ≡ e
erase-embed □ = refl
erase-embed * = refl
erase-embed ⟨ k ⟩ = refl
erase-embed (λ: τ ⇒ e) = cong (λ: τ ⇒_) (erase-embed e)
erase-embed (λ⇒ e) = cong λ⇒_ (erase-embed e)
erase-embed (e₁ ∘ e₂) = cong₂ _∘_ (erase-embed e₁) (erase-embed e₂)
erase-embed (e < τ >) = cong (_< τ >) (erase-embed e)
erase-embed (e₁ & e₂) = cong₂ _&_ (erase-embed e₁) (erase-embed e₂)
erase-embed (ι₁ e) = cong ι₁ (erase-embed e)
erase-embed (ι₂ e) = cong ι₂ (erase-embed e)
erase-embed (case e₀ of e₁ · e₂)
  rewrite erase-embed e₀ | erase-embed e₁ | erase-embed e₂ = refl
erase-embed (π₁ e) = cong π₁ (erase-embed e)
erase-embed (π₂ e) = cong π₂ (erase-embed e)
erase-embed (Λ e) = cong Λ (erase-embed e)
erase-embed (def e₁ ⊢ e₂) = cong₂ (def_⊢_) (erase-embed e₁) (erase-embed e₂)

embedCtx : Ctx → K.MCtx
embedCtx ○ = K.○
embedCtx (λ: τ ⇒ C) = K.λ: τ ⇒ embedCtx C
embedCtx (λ⇒ C) = K.λ⇒ embedCtx C
embedCtx (C ∘₁ e) = embedCtx C K.∘₁ embed e
embedCtx (e ∘₂ C) = embed e K.∘₂ embedCtx C
embedCtx (C < τ >₁) = embedCtx C K.< τ >₁
embedCtx (C &₁ e) = embedCtx C K.&₁ embed e
embedCtx (e &₂ C) = embed e K.&₂ embedCtx C
embedCtx (ι₁ C) = K.ι₁ (embedCtx C)
embedCtx (ι₂ C) = K.ι₂ (embedCtx C)
embedCtx (case₀ C of e₁ · e₂) = K.case₀ embedCtx C of embed e₁ · embed e₂
embedCtx (case e₀ of C ·₁ e₂) = K.case embed e₀ of embedCtx C ·₁ embed e₂
embedCtx (case e₀ of₂ e₁ · C) = K.case embed e₀ of₂ embed e₁ · embedCtx C
embedCtx (π₁ C) = K.π₁ (embedCtx C)
embedCtx (π₂ C) = K.π₂ (embedCtx C)
embedCtx (Λ C) = K.Λ (embedCtx C)
embedCtx (def C ⊢₁ e) = K.def embedCtx C ⊢₁ embed e
embedCtx (def e ⊢₂ C) = K.def embed e ⊢₂ embedCtx C

erase-embedCtx : ∀ C → eraseCtx (embedCtx C) ≡ C
erase-embedCtx ○ = refl
erase-embedCtx (λ: τ ⇒ C) rewrite erase-embedCtx C = refl
erase-embedCtx (λ⇒ C) rewrite erase-embedCtx C = refl
erase-embedCtx (C ∘₁ e) rewrite erase-embedCtx C | erase-embed e = refl
erase-embedCtx (e ∘₂ C) rewrite erase-embed e | erase-embedCtx C = refl
erase-embedCtx (C < τ >₁) rewrite erase-embedCtx C = refl
erase-embedCtx (C &₁ e) rewrite erase-embedCtx C | erase-embed e = refl
erase-embedCtx (e &₂ C) rewrite erase-embed e | erase-embedCtx C = refl
erase-embedCtx (ι₁ C) rewrite erase-embedCtx C = refl
erase-embedCtx (ι₂ C) rewrite erase-embedCtx C = refl
erase-embedCtx (case₀ C of e₁ · e₂)
  rewrite erase-embedCtx C | erase-embed e₁ | erase-embed e₂ = refl
erase-embedCtx (case e₀ of C ·₁ e₂)
  rewrite erase-embed e₀ | erase-embedCtx C | erase-embed e₂ = refl
erase-embedCtx (case e₀ of₂ e₁ · C)
  rewrite erase-embed e₀ | erase-embed e₁ | erase-embedCtx C = refl
erase-embedCtx (π₁ C) rewrite erase-embedCtx C = refl
erase-embedCtx (π₂ C) rewrite erase-embedCtx C = refl
erase-embedCtx (Λ C) rewrite erase-embedCtx C = refl
erase-embedCtx (def C ⊢₁ e) rewrite erase-embedCtx C | erase-embed e = refl
erase-embedCtx (def e ⊢₂ C) rewrite erase-embed e | erase-embedCtx C = refl

-- Every ordinary typing derivation is a successful marking derivation of the
-- canonical embedding, at exactly the same type.
mutual
  mark-typing-syn : ∀ {n Γ e τ} → n , Γ ⊢ e ⇑ τ → n , Γ ⊢ e ↬ embed e ⇑ τ
  mark-typing-syn ⇑* = mark⇑*
  mark-typing-syn ⇑□ = mark⇑□
  mark-typing-syn (⇑Var p) = mark⇑Var p
  mark-typing-syn (⇑λ: wf d) = mark⇑λ: wf (mark-typing-syn d)
  mark-typing-syn (⇑Λ d) = mark⇑Λ (mark-typing-syn d)
  mark-typing-syn (⇑∘ d₁ eq d₂) = mark⇑∘ (mark-typing-syn d₁) eq (mark-typing-ana d₂)
  mark-typing-syn (⇑<> d eq wf) = mark⇑<> (mark-typing-syn d) eq wf
  mark-typing-syn (⇑& d₁ d₂) = mark⇑& (mark-typing-syn d₁) (mark-typing-syn d₂)
  mark-typing-syn (⇑π₁ d eq) = mark⇑π₁ (mark-typing-syn d) eq
  mark-typing-syn (⇑π₂ d eq) = mark⇑π₂ (mark-typing-syn d) eq
  mark-typing-syn (⇑case d₀ eq d₁ d₂ con) =
    mark⇑case (mark-typing-syn d₀) eq (mark-typing-syn d₁) (mark-typing-syn d₂) con
  mark-typing-syn (⇑def d₁ d₂) = mark⇑def (mark-typing-syn d₁) (mark-typing-syn d₂)
  mark-typing-syn (⇑ι₁ d) = mark⇑ι₁ (mark-typing-syn d)
  mark-typing-syn (⇑ι₂ d) = mark⇑ι₂ (mark-typing-syn d)

  mark-typing-ana : ∀ {n Γ e τ} → n , Γ ⊢ e ⇓ τ → n , Γ ⊢ e ↬ embed e ⇓ τ
  mark-typing-ana (⇓Sub d con) = mark⇓sub (mark-typing-syn d) con
  mark-typing-ana (⇓λ eq d) = mark⇓λ eq (mark-typing-ana d)
  mark-typing-ana (⇓λ: con eq wf d) = mark⇓λ: con eq wf (mark-typing-ana d)
  mark-typing-ana (⇓ι₁ eq d) = mark⇓ι₁ eq (mark-typing-ana d)
  mark-typing-ana (⇓ι₂ eq d) = mark⇓ι₂ eq (mark-typing-ana d)
  mark-typing-ana (⇓& eq d₁ d₂) = mark⇓& eq (mark-typing-ana d₁) (mark-typing-ana d₂)
  mark-typing-ana (⇓case d₀ eq d₁ d₂) =
    mark⇓case (mark-typing-syn d₀) eq (mark-typing-ana d₁) (mark-typing-ana d₂)
  mark-typing-ana (⇓def d₁ d₂) = mark⇓def (mark-typing-syn d₁) (mark-typing-ana d₂)

-- Classification proofs lift in the same way; the marked context has the
-- identical syntactic decomposition and all fixed siblings are embedded.
mutual
  mark-syn-cls : ∀ {n Γ C τₚ n' Γ' m}
    → n , Γ ⊢ C at synPos τₚ ▷ n' , Γ' [ m ]
    → n , Γ ⊢ C ↬ embedCtx C at synPos τₚ ▷ n' , Γ' [ m ]
  mark-syn-cls s○ = ms○
  mark-syn-cls (sλ: wf cls) = msλ: wf (mark-syn-cls cls)
  mark-syn-cls (s∘₁ cls eq d) = ms∘₁ (mark-syn-cls cls) eq (mark-typing-ana d)
  mark-syn-cls (s∘₂ d eq cls) = ms∘₂ (mark-typing-syn d) eq (mark-ana-cls cls)
  mark-syn-cls (s<>₁ cls eq wf) = ms<>₁ (mark-syn-cls cls) eq wf
  mark-syn-cls (s&₁ cls d) = ms&₁ (mark-syn-cls cls) (mark-typing-syn d)
  mark-syn-cls (s&₂ d cls) = ms&₂ (mark-typing-syn d) (mark-syn-cls cls)
  mark-syn-cls (sι₁ cls) = msι₁ (mark-syn-cls cls)
  mark-syn-cls (sι₂ cls) = msι₂ (mark-syn-cls cls)
  mark-syn-cls (scase₀ cls eq d₁ d₂ con) =
    mscase₀ (mark-syn-cls cls) eq (mark-typing-syn d₁) (mark-typing-syn d₂) con
  mark-syn-cls (scase₁ d₀ eq cls d₂ con) =
    mscase₁ (mark-typing-syn d₀) eq (mark-syn-cls cls) (mark-typing-syn d₂) con
  mark-syn-cls (scase₂ d₀ eq d₁ cls con) =
    mscase₂ (mark-typing-syn d₀) eq (mark-typing-syn d₁) (mark-syn-cls cls) con
  mark-syn-cls (sπ₁ cls eq) = msπ₁ (mark-syn-cls cls) eq
  mark-syn-cls (sπ₂ cls eq) = msπ₂ (mark-syn-cls cls) eq
  mark-syn-cls (sΛ cls) = msΛ (mark-syn-cls cls)
  mark-syn-cls (sdef₁ cls d) = msdef₁ (mark-syn-cls cls) (mark-typing-syn d)
  mark-syn-cls (sdef₂ d cls) = msdef₂ (mark-typing-syn d) (mark-syn-cls cls)

  mark-ana-cls : ∀ {n Γ C τₚ n' Γ' m}
    → n , Γ ⊢ C at anaPos τₚ ▷ n' , Γ' [ m ]
    → n , Γ ⊢ C ↬ embedCtx C at anaPos τₚ ▷ n' , Γ' [ m ]
  mark-ana-cls a○ = ma○
  mark-ana-cls (aSub cls con) = maSub (mark-syn-cls cls) con
  mark-ana-cls (aλ: con eq wf cls) = maλ: con eq wf (mark-ana-cls cls)
  mark-ana-cls (aλ⇒ eq cls) = maλ⇒ eq (mark-ana-cls cls)
  mark-ana-cls (a&₁ eq cls d) = ma&₁ eq (mark-ana-cls cls) (mark-typing-ana d)
  mark-ana-cls (a&₂ eq d cls) = ma&₂ eq (mark-typing-ana d) (mark-ana-cls cls)
  mark-ana-cls (aι₁ eq cls) = maι₁ eq (mark-ana-cls cls)
  mark-ana-cls (aι₂ eq cls) = maι₂ eq (mark-ana-cls cls)
  mark-ana-cls (acase₀ cls eq d₁ d₂) =
    macase₀ (mark-syn-cls cls) eq (mark-typing-ana d₁) (mark-typing-ana d₂)
  mark-ana-cls (acase₁ d₀ eq cls d₂) =
    macase₁ (mark-typing-syn d₀) eq (mark-ana-cls cls) (mark-typing-ana d₂)
  mark-ana-cls (acase₂ d₀ eq d₁ cls) =
    macase₂ (mark-typing-syn d₀) eq (mark-typing-ana d₁) (mark-ana-cls cls)
  mark-ana-cls (adef₁ cls d) = madef₁ (mark-syn-cls cls) (mark-typing-ana d)
  mark-ana-cls (adef₂ d cls) = madef₂ (mark-typing-syn d) (mark-ana-cls cls)
