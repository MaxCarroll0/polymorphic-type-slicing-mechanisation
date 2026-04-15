module Semantics.Marking.Erasure where

open import Data.Nat using (ℕ)
open import Core.Typ using (Typ)
open import Core.Exp.Base
open import Core.MExp

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
