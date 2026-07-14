-- Mark-erasure operation: drops marks from a marked expression to recover the original Exp.
-- Dissertation: §7.1 Error Marking (supporting `erase` for Theorem 7.2 thm:mark-erase).
module Semantics.Marking.Erasure where

open import Data.Nat using (ℕ)
open import Core.Typ using (Typ)
open import Core.Exp.Base
open import Core.MExp
import Core.Ctx.Base as C
import Core.MCtx as K

erase : MExp → Exp
erase □                   = □
erase *                   = *
erase ⟨ n ⟩               = ⟨ n ⟩
erase (λ: τ ⇒ ě)          = λ: τ ⇒ erase ě
erase (λ⇒ ě)              = λ⇒ erase ě
erase (ě₁ ∘ ě₂)           = erase ě₁ ∘ erase ě₂
erase (ě < τ >)           = erase ě < τ >
erase (ě₁ & ě₂)           = erase ě₁ & erase ě₂
erase (ι₁ ě)              = ι₁ (erase ě)
erase (ι₂ ě)              = ι₂ (erase ě)
erase (case ě of ě₁ · ě₂) = case erase ě of erase ě₁ · erase ě₂
erase (π₁ ě)              = π₁ (erase ě)
erase (π₂ ě)              = π₂ (erase ě)
erase (Λ ě)               = Λ (erase ě)
erase (def ě₁ ⊢ ě₂)       = def erase ě₁ ⊢ erase ě₂
erase (⟨ n ⟩⇑)            = ⟨ n ⟩
erase (ě ⦅≁ _ ⦆)           = erase ě
erase (ě ⦅▸⇒⦆)             = erase ě
erase (ě ⦅▸+⦆)             = erase ě
erase (ě ⦅▸×⦆)             = erase ě
erase (ě ⦅▸∀⦆)             = erase ě
erase (ě ⦅~⇒⦆)             = erase ě
erase (ě ⦅~+⦆)             = erase ě
erase (ě ⦅~×⦆)             = erase ě

-- Mark erasure extends pointwise to one-hole contexts.  Wrappers disappear,
-- while the unique hole and the underlying syntactic decomposition are
-- preserved.
eraseCtx : K.MCtx → C.Ctx
eraseCtx K.○ = C.○
eraseCtx (K.λ: τ ⇒ Č) = C.λ: τ ⇒ eraseCtx Č
eraseCtx (K.λ⇒ Č) = C.λ⇒ eraseCtx Č
eraseCtx (Č K.∘₁ ě) = eraseCtx Č C.∘₁ erase ě
eraseCtx (ě K.∘₂ Č) = erase ě C.∘₂ eraseCtx Č
eraseCtx (Č K.< τ >₁) = eraseCtx Č C.< τ >₁
eraseCtx (Č K.&₁ ě) = eraseCtx Č C.&₁ erase ě
eraseCtx (ě K.&₂ Č) = erase ě C.&₂ eraseCtx Č
eraseCtx (K.ι₁ Č) = C.ι₁ (eraseCtx Č)
eraseCtx (K.ι₂ Č) = C.ι₂ (eraseCtx Č)
eraseCtx (K.case₀ Č of ě₁ · ě₂) = C.case₀ eraseCtx Č of erase ě₁ · erase ě₂
eraseCtx (K.case ě₀ of Č ·₁ ě₂) = C.case erase ě₀ of eraseCtx Č ·₁ erase ě₂
eraseCtx (K.case ě₀ of₂ ě₁ · Č) = C.case erase ě₀ of₂ erase ě₁ · eraseCtx Č
eraseCtx (K.π₁ Č) = C.π₁ (eraseCtx Č)
eraseCtx (K.π₂ Č) = C.π₂ (eraseCtx Č)
eraseCtx (K.Λ Č) = C.Λ (eraseCtx Č)
eraseCtx (K.def Č ⊢₁ ě) = C.def eraseCtx Č ⊢₁ erase ě
eraseCtx (K.def ě ⊢₂ Č) = C.def erase ě ⊢₂ eraseCtx Č
eraseCtx (Č K.⦅≁ τ ⦆) = eraseCtx Č
eraseCtx (Č K.⦅▸⇒⦆) = eraseCtx Č
eraseCtx (Č K.⦅▸+⦆) = eraseCtx Č
eraseCtx (Č K.⦅▸×⦆) = eraseCtx Č
eraseCtx (Č K.⦅▸∀⦆) = eraseCtx Č
eraseCtx (Č K.⦅~⇒⦆) = eraseCtx Č
eraseCtx (Č K.⦅~+⦆) = eraseCtx Č
